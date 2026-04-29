#!/usr/bin/env python3
"""Verify Goedel inference results using Lean compilation.

Reads the JSONL output from goedel_inference.py, parses the Goedel-format
model outputs (```lean code blocks), and verifies each proof via Lean
compilation using VeriSoftBench's pipeline.

Usage:
    python scripts/goedel_verify.py \
        --input results/goedel_8b_inference.jsonl \
        --output results/goedel_8b_verified.jsonl \
        --lean-src-dir data/lean_repos \
        [--lean-backend docker --docker-container verisoftbench-lean]
"""

import argparse
import json
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Any, List, Tuple

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

import utils.utils as utils
from core.lean_interface import LeanREPL
from config.paths import PROJECT_ROOT, EVAL_INPUT_DIR


def _clean_thm_stmt(thm_stmt: str, gt_proof: str = "") -> str:
    """Strip proof body from thm_stmt and append correct separator.

    Inlined from core.evaluator to avoid importing ProverInterface deps.
    """
    sep_idx, sep_pat = utils.find_decl_body_separator(thm_stmt)
    _body_pats = {':=\\s+by\\b', ':=\\s+match\\b', ':=\\s+calc\\b',
                  ':=\\s+fun\\b', ':=\\s+λ\\b', ':=\\s+begin\\b',
                  '\\bwhere\\b', '(?<!<)\\|\\s+(?!<)\\S'}
    if sep_idx > 0 and sep_pat in _body_pats:
        thm_stmt = thm_stmt[:sep_idx].rstrip()
    elif sep_idx > 0 and thm_stmt[sep_idx:sep_idx+2] == ':=':
        thm_stmt = thm_stmt[:sep_idx].rstrip()

    gt_stripped = gt_proof.strip()
    uses_where = gt_stripped.startswith('where')
    uses_pipe = gt_stripped.startswith('|')

    stripped = thm_stmt.rstrip()
    if stripped.endswith(':='):
        stripped = stripped[:-2].rstrip()
    elif stripped.endswith('where'):
        stripped = stripped[:-5].rstrip()

    if uses_where or uses_pipe:
        thm_stmt = stripped
    else:
        thm_stmt = stripped + ' :='

    return thm_stmt


def load_inference_results(path: Path) -> List[Dict]:
    """Load inference JSONL."""
    results = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                results.append(json.loads(line))
    print(f"Loaded {len(results)} inference results from {path}")
    return results


def load_benchmark_entries(data_dir: Path) -> Dict[int, Dict]:
    """Load benchmark entries keyed by ID."""
    path = data_dir / "verisoftbench.jsonl"
    entries = {}
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                e = json.loads(line)
                entries[e["id"]] = e
    return entries


SAMPLE_TIMEOUT = 120  # seconds per sample


def verify_single_result(
    result: Dict,
    entry: Dict,
    lean_repl: LeanREPL,
    lean_src_dir: Path,
) -> Dict:
    """Verify all samples for one theorem sequentially."""
    thm_name = result["thm_name"]
    lean_root = result["lean_root"]
    rel_path = result["rel_path"]

    # Clean theorem statement
    thm_stmt = _clean_thm_stmt(
        entry["thm_stmt"],
        gt_proof=entry.get("ground_truth_proof", ""),
    )

    imports = entry["imports"]
    local_ctx = entry.get("local_ctxs") or entry.get("local_ctx", "")
    suffix = entry.get("suffix", "")

    # Build verification context from source file
    verif_ctx = _build_verif_context_standalone(
        lean_repl, lean_src_dir, lean_root, rel_path, imports, local_ctx, thm_stmt, thm_name
    )

    verified_samples = []
    any_success = False

    for sample_idx, sample in enumerate(result.get("samples", [])):
        raw_output = sample.get("model_response", "")
        finish_reason = sample.get("finish_reason", "")

        if not raw_output:
            verified_samples.append({
                "sample_idx": sample_idx,
                "finish_reason": finish_reason or "error",
                "compilation_success": False,
                "compilation_error": "No model output",
                "extracted_proof": "",
                "extracted_lemmas": "",
            })
            continue

        # Skip degenerate outputs: model stuck in repetition loops
        # (e.g. "field.field.field." x20, "True → True → True →" x20)
        if re.search(r'(.{10,50})\1{14,}', raw_output):
            verified_samples.append({
                "sample_idx": sample_idx,
                "finish_reason": finish_reason,
                "compilation_success": False,
                "compilation_error": "Degenerate output: repetitive pattern detected",
                "extracted_proof": "",
                "extracted_lemmas": "",
                "model_response": raw_output,
            })
            continue

        # Parse Goedel output
        lemmas = utils.get_goedel_lemmas_from_output(raw_output, thm_name)
        proof = utils.get_goedel_proof_from_output(raw_output, thm_name)

        if not proof:
            verified_samples.append({
                "sample_idx": sample_idx,
                "finish_reason": finish_reason,
                "compilation_success": False,
                "compilation_error": "Failed to parse proof from model output",
                "extracted_proof": "",
                "extracted_lemmas": lemmas,
                "model_response": raw_output,
            })
            continue

        # Handle verina repos
        if "verina" in str(lean_root) and lemmas.strip():
            lemmas = re.sub(r'lemma\b', 'theorem', lemmas)

        # Resolve name conflicts
        name_mapping = utils.find_conflicting_names_from_local_context(verif_ctx, lemmas)
        if name_mapping:
            lemmas, proof = utils.apply_name_replacements(lemmas, proof, name_mapping)

        # Remove axioms
        while "axiom " in lemmas:
            lemmas = lemmas.replace("axiom ", "theorem ")

        # Clean leaked identifiers
        proof, lemmas = utils.clean_leaked_identifiers(entry, proof, lemmas)

        # Verify directly — no multiprocessing
        success = False
        error_msg = ""
        try:
            s, e = lean_repl.verify_proof(
                thm_name=thm_name, repo_name=lean_root, rel_path=rel_path,
                local_context=verif_ctx, theorem_stmt=thm_stmt,
                theorem_proof=proof, proof_id=f"goedel_{sample_idx}",
                aux_lemmas=lemmas, suffix=suffix,
            )
            success = s
            error_msg = e if not s else ""
        except subprocess.TimeoutExpired:
            error_msg = f"Timeout ({SAMPLE_TIMEOUT}s) during Lean compilation"
        except Exception as ex:
            error_msg = str(ex)

        if success:
            any_success = True
            verified_samples.append({
                "sample_idx": sample_idx,
                "finish_reason": finish_reason,
                "compilation_success": True,
                "compilation_error": None,
                "extracted_proof": proof,
                "extracted_lemmas": lemmas,
                "model_response": raw_output,
            })
            # Early exit: for pass@k, one success is enough
            for skip_idx in range(sample_idx + 1, len(result.get("samples", []))):
                verified_samples.append({
                    "sample_idx": skip_idx,
                    "finish_reason": "skipped",
                    "compilation_success": False,
                    "compilation_error": "Skipped (earlier sample proved)",
                    "extracted_proof": "",
                    "extracted_lemmas": "",
                })
            break

        verified_samples.append({
            "sample_idx": sample_idx,
            "finish_reason": finish_reason,
            "compilation_success": False,
            "compilation_error": error_msg,
            "extracted_proof": proof,
            "extracted_lemmas": lemmas,
            "model_response": raw_output,
        })

    return {
        "id": result["id"],
        "thm_name": thm_name,
        "lean_root": lean_root,
        "rel_path": rel_path,
        "category": result.get("category", ""),
        "success": any_success,
        "samples": verified_samples,
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }


def _build_verif_context_standalone(
    lean_repl, lean_src_dir, lean_root, rel_path, imports, local_ctx, thm_stmt, thm_name
) -> str:
    """Build verification context from source file.

    Tries: local filesystem first, then Docker container, then fallback.
    """
    if lean_root == "iris-lean":
        imports = [imp.replace("import src.", "import ") for imp in imports]

    fallback_ctx = "\n".join(imports) + "\n" + local_ctx
    full_content = None

    # Try local filesystem
    try:
        full_file_path = lean_src_dir / lean_root / rel_path
        if full_file_path.exists():
            full_content = full_file_path.read_text(encoding="utf-8")
    except Exception:
        pass

    # Skip Docker reads for context — they cause deadlocks when interleaved
    # with verify_proof's Docker exec calls. The fallback context from JSONL
    # (imports + local_ctx) is sufficient for most theorems.

    if full_content is None:
        return fallback_ctx

    verif_ctx = utils.get_content_before_theorem(full_content, thm_stmt, thm_name=thm_name)
    if verif_ctx is None:
        return fallback_ctx

    # Strip noncomputable from lemma/theorem
    verif_ctx = re.sub(
        r'^noncomputable\s+(theorem|lemma)\b', r'\1',
        verif_ctx, flags=re.MULTILINE
    )

    return verif_ctx


def main():
    parser = argparse.ArgumentParser(description="Verify Goedel inference results with Lean")
    parser.add_argument("--input", type=str, required=True, help="Inference JSONL file")
    parser.add_argument("--output", type=str, required=True, help="Verified results JSONL")
    parser.add_argument("--data-dir", type=str, default=str(PROJECT_ROOT / "data"))
    parser.add_argument("--lean-src-dir", type=str, default=None)
    parser.add_argument("--lean-backend", type=str, default="local", choices=["local", "docker"])
    parser.add_argument("--docker-container", type=str, default="verisoftbench-lean")
    parser.add_argument("--max-workers", type=int, default=4)
    parser.add_argument("--save-every", type=int, default=10)
    args = parser.parse_args()

    import os
    lean_src = args.lean_src_dir or os.environ.get("VERISOFTBENCH_LEAN_SRC") or str(PROJECT_ROOT / "data" / "lean_repos")
    lean_src_dir = Path(lean_src)

    docker_container = args.docker_container if args.lean_backend == "docker" else None
    lean_repl = LeanREPL(lean_src_dir, docker_container=docker_container)

    # Load data
    inference_results = load_inference_results(Path(args.input))
    benchmark_entries = load_benchmark_entries(Path(args.data_dir))

    # Resume support
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    completed_ids = set()
    if output_path.exists():
        with open(output_path, "r") as f:
            for line in f:
                if line.strip():
                    r = json.loads(line)
                    completed_ids.add(r["id"])
        print(f"Resuming: {len(completed_ids)} already verified")

    to_verify = [r for r in inference_results if r["id"] not in completed_ids]
    total = len(to_verify)
    successes = 0
    parse_failures = 0
    start_time = time.time()

    print(f"\nVerifying {total} theorems (backend: {args.lean_backend})")
    print("=" * 60)

    with open(output_path, "a", encoding="utf-8") as f:
        for i, result in enumerate(to_verify):
            entry = benchmark_entries.get(result["id"])
            if not entry:
                print(f"  WARNING: No benchmark entry for ID {result['id']}, skipping")
                continue

            thm_name = result["thm_name"]
            elapsed = time.time() - start_time
            rate = (i + 1) / elapsed if elapsed > 0 else 0
            eta = (total - i - 1) / rate if rate > 0 else 0

            print(f"[{i+1}/{total}] {thm_name} (ETA: {eta/60:.1f}m)")

            verified = verify_single_result(result, entry, lean_repl, lean_src_dir)

            if verified["success"]:
                successes += 1
                print(f"  PROVED!")

            # Check parse failures
            for s in verified["samples"]:
                if not s.get("extracted_proof") and s.get("compilation_error", "").startswith("Failed to parse"):
                    parse_failures += 1

            f.write(json.dumps(verified, ensure_ascii=False) + "\n")

            if (i + 1) % args.save_every == 0:
                f.flush()
                os.fsync(f.fileno())
                pct = successes / (i + 1) * 100
                print(f"  [CHECKPOINT] {i+1}/{total} | {successes} proved ({pct:.1f}%) | {parse_failures} parse failures")

    elapsed = time.time() - start_time
    total_verified = total
    pct = successes / total_verified * 100 if total_verified > 0 else 0

    print(f"\n{'='*60}")
    print(f"Verification complete: {total_verified} theorems in {elapsed/60:.1f} minutes")
    print(f"  Proved: {successes}/{total_verified} ({pct:.1f}%)")
    print(f"  Parse failures: {parse_failures}")
    print(f"  Output: {output_path}")


if __name__ == "__main__":
    main()
