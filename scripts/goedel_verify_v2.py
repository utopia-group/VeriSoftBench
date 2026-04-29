#!/usr/bin/env python3
"""Verify Goedel inference results using the real BenchmarkEvaluator pipeline.

Uses the same verify_proof path as evaluate.py — proven to work on all 500
ground truth proofs with Docker.
"""

import argparse
import json
import os
import re
import sys
import time
from pathlib import Path
from typing import Dict, Any, List

sys.path.insert(0, str(Path(__file__).parent.parent))

import utils.utils as utils
from core.evaluator import BenchmarkEvaluator, _clean_thm_stmt
from config.paths import PROJECT_ROOT, EVAL_INPUT_DIR, PROMPTS_DIR, RESULTS_DATA_DIR


def main():
    parser = argparse.ArgumentParser(description="Verify Goedel inference results")
    parser.add_argument("--input", required=True, help="Inference JSONL")
    parser.add_argument("--output", required=True, help="Verified JSONL")
    parser.add_argument("--lean-backend", default="docker", choices=["local", "docker"])
    parser.add_argument("--docker-container", default="verisoftbench-test")
    parser.add_argument("--lean-src-dir", default=None)
    parser.add_argument("--save-every", type=int, default=5)
    args = parser.parse_args()

    lean_src = args.lean_src_dir or os.environ.get("VERISOFTBENCH_LEAN_SRC") or str(PROJECT_ROOT / "data" / "lean_repos")

    # Create a minimal evaluator just for verification (no LLM calls)
    model_config = {
        "model_name": "openai",
        "model_id": "dummy",
        "base_url": "http://localhost:1/v1",  # won't be called
        "prompt_mode": "goedel",
        "mode": "filtered_context",
    }
    evaluator = BenchmarkEvaluator(
        locator_data_dir=EVAL_INPUT_DIR,
        context_data_dir=EVAL_INPUT_DIR,
        lean_src_dir=Path(lean_src),
        prompts_dir=PROMPTS_DIR,
        output_dir=RESULTS_DATA_DIR,
        model_config=model_config,
        fix_enabled=False,
        docker_container=args.docker_container if args.lean_backend == "docker" else None,
    )

    # Load data
    inference = [json.loads(l) for l in open(args.input) if l.strip()]
    entries = {}
    with open(EVAL_INPUT_DIR / "verisoftbench.jsonl") as f:
        for line in f:
            e = json.loads(line)
            entries[e["id"]] = e
    print(f"Loaded {len(inference)} inference results")

    # Resume
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    done_ids = set()
    if output_path.exists():
        for l in open(output_path):
            if l.strip():
                done_ids.add(json.loads(l)["id"])
        print(f"Resuming: {len(done_ids)} done")

    todo = [r for r in inference if r["id"] not in done_ids]
    total = len(todo)
    proved = 0
    start = time.time()

    print(f"Verifying {total} theorems (backend: {args.lean_backend})")
    print("=" * 60)

    with open(output_path, "a") as f:
        for i, result in enumerate(todo):
            entry = entries.get(result["id"])
            if not entry:
                print(f"  WARNING: no entry for id={result['id']}")
                continue

            thm_name = result["thm_name"]
            elapsed = time.time() - start
            rate = (i + 1) / elapsed if elapsed > 0 else 0
            eta = (total - i - 1) / rate / 60 if rate > 0 else 0
            print(f"[{i+1}/{total}] {thm_name[:50]} (ETA: {eta:.1f}m)")

            # Clean thm_stmt the same way evaluate.py does
            thm_stmt = _clean_thm_stmt(
                entry["thm_stmt"], gt_proof=entry.get("ground_truth_proof", ""))
            entry_copy = dict(entry)
            entry_copy["thm_stmt"] = thm_stmt

            lean_root = entry["lean_root"]
            rel_path = entry["rel_path"]
            imports = entry["imports"]
            local_ctx = entry.get("local_ctxs") or entry.get("local_ctx", "")
            suffix = entry.get("suffix", "")

            # Build verif context the same way evaluator does
            verif_ctx = evaluator._build_verif_context(
                lean_root, rel_path, imports, local_ctx, thm_stmt, thm_name)

            verified_samples = []
            any_success = False

            for si, sample in enumerate(result.get("samples", [])):
                raw = sample.get("model_response", "") or ""
                if not raw:
                    verified_samples.append({
                        "sample_idx": si, "compilation_success": False,
                        "compilation_error": "No model output"})
                    continue

                lemmas = utils.get_goedel_lemmas_from_output(raw, thm_name)
                proof = utils.get_goedel_proof_from_output(raw, thm_name)

                if not proof:
                    verified_samples.append({
                        "sample_idx": si, "compilation_success": False,
                        "compilation_error": "Failed to parse proof"})
                    continue

                if "verina" in lean_root and lemmas.strip():
                    lemmas = re.sub(r'lemma\b', 'theorem', lemmas)

                name_mapping = utils.find_conflicting_names_from_local_context(verif_ctx, lemmas)
                if name_mapping:
                    lemmas, proof = utils.apply_name_replacements(lemmas, proof, name_mapping)
                while "axiom " in lemmas:
                    lemmas = lemmas.replace("axiom ", "theorem ")
                proof, lemmas = utils.clean_leaked_identifiers(entry_copy, proof, lemmas)

                try:
                    success, error_msg = evaluator.lean_repl.verify_proof(
                        thm_name=thm_name,
                        repo_name=lean_root,
                        rel_path=rel_path,
                        local_context=verif_ctx,
                        theorem_stmt=thm_stmt,
                        theorem_proof=proof,
                        proof_id=f"goedel_{si}",
                        aux_lemmas=lemmas,
                        suffix=suffix,
                    )
                except Exception as e:
                    success = False
                    error_msg = f"Exception: {e}"

                if success:
                    any_success = True
                    verified_samples.append({
                        "sample_idx": si, "compilation_success": True,
                        "extracted_proof": proof, "extracted_lemmas": lemmas})
                    # Early exit for pass@k
                    for skip in range(si + 1, len(result.get("samples", []))):
                        verified_samples.append({
                            "sample_idx": skip, "compilation_success": False,
                            "compilation_error": "Skipped (earlier proved)"})
                    break
                else:
                    verified_samples.append({
                        "sample_idx": si, "compilation_success": False,
                        "compilation_error": (error_msg or "")[:1000],
                        "extracted_proof": proof, "extracted_lemmas": lemmas})

            if any_success:
                proved += 1
                print(f"  PROVED!")

            record = {
                "id": result["id"], "thm_name": thm_name, "lean_root": lean_root,
                "rel_path": rel_path, "category": result.get("category", ""),
                "success": any_success, "samples": verified_samples,
            }
            f.write(json.dumps(record) + "\n")

            if (i + 1) % args.save_every == 0:
                f.flush()
                os.fsync(f.fileno())
                pct = proved / (i + 1) * 100
                print(f"  [{i+1}/{total}] {proved} proved ({pct:.1f}%)")

    pct = proved / total * 100 if total else 0
    print(f"\nDone: {proved}/{total} proved ({pct:.1f}%)")


if __name__ == "__main__":
    main()
