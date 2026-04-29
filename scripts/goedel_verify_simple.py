#!/usr/bin/env python3
"""Minimal Goedel verification — calls Docker directly without importing core/.

Avoids the ProverInterface import chain and Docker stdin pipe hangs by using
docker cp for writes and subprocess with explicit timeouts for compilation.
"""

import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Dict, Any, List, Optional, Tuple

sys.path.insert(0, str(Path(__file__).parent.parent))
import utils.utils as utils


DOCKER_LEAN_REPOS = "/workspace/lean_repos"


def docker_read_file(container: str, path: str, timeout: int = 30) -> Optional[str]:
    r = subprocess.run(
        ["docker", "exec", container, "cat", path],
        capture_output=True, text=True, timeout=timeout,
    )
    return r.stdout if r.returncode == 0 else None


def docker_write_file(container: str, container_path: str, content: str, timeout: int = 30):
    """Write file via docker cp (not docker exec tee — that hangs on large files)."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False, encoding='utf-8') as f:
        f.write(content)
        tmp = f.name
    try:
        subprocess.run(
            ["docker", "cp", tmp, f"{container}:{container_path}"],
            capture_output=True, text=True, timeout=timeout,
        )
    finally:
        os.unlink(tmp)


def docker_rm_file(container: str, path: str):
    subprocess.run(["docker", "exec", container, "rm", "-f", path],
                   capture_output=True, timeout=10)


def docker_compile(container: str, lean_file: str, repo_dir: str, timeout: int = 300) -> Tuple[bool, str]:
    """Compile a Lean file inside Docker. Returns (success, error_msg)."""
    try:
        r = subprocess.run(
            ["docker", "exec", "-w", repo_dir, container,
             "lake", "env", "lean", lean_file],
            capture_output=True, text=True, timeout=timeout,
        )
        if r.returncode == 0 and "error" not in r.stderr.lower():
            return True, ""
        return False, r.stderr[:2000]
    except subprocess.TimeoutExpired:
        return False, f"Compilation timed out ({timeout}s)"


def build_verif_context(container: str, entry: Dict) -> str:
    """Build verification context by reading source from Docker."""
    lean_root = entry["lean_root"]
    rel_path = entry["rel_path"]
    imports = entry["imports"]
    local_ctx = entry.get("local_ctx", "")
    thm_stmt = entry.get("thm_stmt", "")
    thm_name = entry["thm_name"]

    if lean_root == "iris-lean":
        imports = [imp.replace("import src.", "import ") for imp in imports]

    fallback = "\n".join(imports) + "\n" + local_ctx

    try:
        content = docker_read_file(container, f"{DOCKER_LEAN_REPOS}/{lean_root}/{rel_path}")
        if not content:
            return fallback
        ctx = utils.get_content_before_theorem(content, thm_stmt, thm_name=thm_name)
        if ctx is None:
            return fallback
        ctx = re.sub(r'^noncomputable\s+(theorem|lemma)\b', r'\1', ctx, flags=re.MULTILINE)
        return ctx
    except Exception:
        return fallback


def clean_thm_stmt(thm_stmt: str, gt_proof: str = "") -> str:
    """Inline version of evaluator's _clean_thm_stmt."""
    sep_idx, sep_pat = utils.find_decl_body_separator(thm_stmt)
    body_pats = {':=\\s+by\\b', ':=\\s+match\\b', ':=\\s+calc\\b',
                 ':=\\s+fun\\b', ':=\\s+λ\\b', ':=\\s+begin\\b',
                 '\\bwhere\\b', '(?<!<)\\|\\s+(?!<)\\S'}
    if sep_idx > 0 and sep_pat in body_pats:
        thm_stmt = thm_stmt[:sep_idx].rstrip()
    elif sep_idx > 0 and thm_stmt[sep_idx:sep_idx + 2] == ':=':
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
        return stripped
    return stripped + ' :='


def verify_single(
    result: Dict, entry: Dict, container: str, compile_timeout: int = 300
) -> Dict:
    """Verify all samples for one theorem."""
    thm_name = result["thm_name"]
    lean_root = result["lean_root"]
    rel_path = result["rel_path"]

    thm_stmt = clean_thm_stmt(entry["thm_stmt"], entry.get("ground_truth_proof", ""))
    suffix = entry.get("suffix", "")
    verif_ctx = build_verif_context(container, entry)

    verified = []
    any_success = False

    for si, sample in enumerate(result.get("samples", [])):
        raw = sample.get("model_response", "") or ""
        if not raw:
            verified.append({"sample_idx": si, "compilation_success": False,
                             "compilation_error": "No model output"})
            continue

        lemmas = utils.get_goedel_lemmas_from_output(raw, thm_name)
        proof = utils.get_goedel_proof_from_output(raw, thm_name)

        if not proof:
            verified.append({"sample_idx": si, "compilation_success": False,
                             "compilation_error": "Failed to parse proof",
                             "model_response": raw[:500]})
            continue

        # Handle verina
        if "verina" in lean_root and lemmas.strip():
            lemmas = re.sub(r'lemma\b', 'theorem', lemmas)

        # Clean
        name_mapping = utils.find_conflicting_names_from_local_context(verif_ctx, lemmas)
        if name_mapping:
            lemmas, proof = utils.apply_name_replacements(lemmas, proof, name_mapping)
        while "axiom " in lemmas:
            lemmas = lemmas.replace("axiom ", "theorem ")
        proof, lemmas = utils.clean_leaked_identifiers(entry, proof, lemmas)

        # Check for sorry/admit
        sorry_errors = utils.check_generated_content_for_incomplete_proofs(thm_name, proof, lemmas)

        # Build Lean file
        file_content = utils.format_generated_lean(verif_ctx, thm_stmt, proof, lemmas, suffix)

        # Write, compile, cleanup
        safe_name = thm_name.replace("/", "_").replace("\\", "_").replace(".", "_")
        container_file = f"{DOCKER_LEAN_REPOS}/{lean_root}/{Path(rel_path).parent}/{safe_name}_goedel_{si}.lean"
        repo_dir = f"{DOCKER_LEAN_REPOS}/{lean_root}"

        try:
            docker_write_file(container, container_file, file_content)
            success, error_msg = docker_compile(container, container_file, repo_dir, timeout=compile_timeout)
            docker_rm_file(container, container_file)
        except Exception as e:
            success = False
            error_msg = f"Exception: {e}"

        if sorry_errors:
            all_errors = sorry_errors + ([error_msg] if error_msg else [])
            success = False
            error_msg = "\n".join(all_errors)

        if success:
            any_success = True
            verified.append({"sample_idx": si, "compilation_success": True,
                             "extracted_proof": proof, "extracted_lemmas": lemmas})
            # Early exit for pass@k
            for skip in range(si + 1, len(result.get("samples", []))):
                verified.append({"sample_idx": skip, "compilation_success": False,
                                 "compilation_error": "Skipped (earlier proved)"})
            break
        else:
            verified.append({"sample_idx": si, "compilation_success": False,
                             "compilation_error": error_msg[:1000],
                             "extracted_proof": proof, "extracted_lemmas": lemmas})

    return {
        "id": result["id"], "thm_name": thm_name, "lean_root": lean_root,
        "rel_path": rel_path, "category": result.get("category", ""),
        "success": any_success, "samples": verified,
    }


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--docker-container", default="verisoftbench-test")
    parser.add_argument("--compile-timeout", type=int, default=300)
    parser.add_argument("--save-every", type=int, default=5)
    args = parser.parse_args()

    # Load data
    inference = [json.loads(l) for l in open(args.input) if l.strip()]
    entries = {e["id"]: e for l in open("data/verisoftbench.jsonl") for e in [json.loads(l)]}
    print(f"Loaded {len(inference)} theorems")

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

    print(f"Verifying {total} theorems (container: {args.docker_container})")

    with open(output_path, "a") as f:
        for i, result in enumerate(todo):
            entry = entries.get(result["id"])
            if not entry:
                continue

            elapsed = time.time() - start
            rate = (i + 1) / elapsed if elapsed > 0 else 0
            eta = (total - i - 1) / rate / 60 if rate > 0 else 0

            print(f"[{i+1}/{total}] {result['thm_name'][:50]} (ETA: {eta:.1f}m)")

            v = verify_single(result, entry, args.docker_container, args.compile_timeout)
            if v["success"]:
                proved += 1
                print(f"  PROVED!")

            f.write(json.dumps(v) + "\n")
            if (i + 1) % args.save_every == 0:
                f.flush()
                os.fsync(f.fileno())
                pct = proved / (i + 1) * 100
                print(f"  [{i+1}/{total}] {proved} proved ({pct:.1f}%)")

    total_done = len(todo)
    pct = proved / total_done * 100 if total_done else 0
    print(f"\nDone: {proved}/{total_done} proved ({pct:.1f}%)")


if __name__ == "__main__":
    main()
