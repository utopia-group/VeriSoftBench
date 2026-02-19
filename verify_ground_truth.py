"""Verify all ground-truth proofs against the Docker container."""

import json
import os
import re
import sys
import time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

from core.lean_interface import LeanREPL

DATASET = Path("data/verisoftbench.jsonl")
LEAN_SRC_DIR = Path("/workspace/lean_repos")  # container path (used for path arithmetic)
DOCKER_CONTAINER = "verisoftbench-test"


def load_entries(path: Path):
    entries = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                entries.append(json.loads(line))
    return entries


def verify_one(repl: LeanREPL, entry: dict) -> dict:
    """Verify a single ground-truth proof. Returns a result dict."""
    task_id = entry["id"]
    thm_name = entry["thm_name"]
    lean_root = entry["lean_root"]
    rel_path = entry["rel_path"]
    imports = entry["imports"]
    local_ctx = entry.get("local_ctxs") or entry.get("local_ctx", "")
    thm_stmt = entry["thm_stmt"]
    gt_proof = entry.get("ground_truth_proof", "")
    suffix = entry.get("suffix", "")

    if not gt_proof.strip():
        return {
            "id": task_id, "thm_name": thm_name, "lean_root": lean_root,
            "success": False, "error": "empty ground_truth_proof"
        }

    # Fix mis-split thm_stmt / gt_proof where extraction split at a `let :=`
    # or where thm_stmt already includes a proof body.
    import utils.utils as utils
    sep_idx, sep_pat = utils.find_decl_body_separator(thm_stmt)
    gt_stripped = gt_proof.strip()

    # Body separator patterns that indicate proof/body content in thm_stmt
    _body_pats = {':=\\s+by\\b', ':=\\s+match\\b', ':=\\s+calc\\b',
                  ':=\\s+fun\\b', ':=\\s+λ\\b', ':=\\s+begin\\b',
                  '\\bwhere\\b', '(?<!<)\\|\\s+(?!<)\\S'}
    if sep_idx > 0 and sep_pat in _body_pats:
        # Case 1: thm_stmt has a specific body pattern (`:= match`, `| pat`, etc.)
        # If gt_proof is a broken fragment (starts mid-proof, e.g. `:= <ident>`
        # that doesn't match a standard proof start), use the proof from thm_stmt.
        proof_from_stmt = '\n  ' + thm_stmt[sep_idx:]
        thm_stmt = thm_stmt[:sep_idx].rstrip()
        if gt_stripped.startswith(':=') and not any(
            re.match(p, gt_stripped) for p in [
                r':=\s+by\b', r':=\s+match\b', r':=\s+calc\b',
                r':=\s+fun\b', r':=\s+λ\b', r':=\s+begin\b',
            ]
        ) and not gt_stripped.startswith(':= by'):
            # gt_proof is a fragment — use proof extracted from thm_stmt
            gt_proof = proof_from_stmt
    elif gt_stripped.startswith(':=') and not any(
        re.match(p, gt_stripped) for p in [
            r':=\s+by\b', r':=\s+match\b', r':=\s+calc\b',
            r':=\s+fun\b', r':=\s+λ\b', r':=\s+begin\b',
        ]
    ):
        # gt_proof starts with `:=` but is NOT a standard body start.
        # Two sub-cases:
        gt_sep_idx, gt_sep_pat = utils.find_decl_body_separator(gt_proof)
        if gt_sep_idx > 0 and gt_sep_pat not in (':=', ':'):
            # Case 2a: gt_proof has duplicated type + real proof (let-split).
            # The real proof starts at gt_sep_idx.
            gt_proof = gt_proof[gt_sep_idx:]
        elif sep_idx > 0 and thm_stmt[sep_idx:sep_idx+2] == ':=':
            # Case 2b: thm_stmt already contains a term-mode proof (e.g. `:= rfl`).
            # Strip the body from thm_stmt.
            thm_stmt = thm_stmt[:sep_idx].rstrip()

    # Strip trailing contamination from gt_proof: block comments or new
    # top-level declarations (example, def, theorem, ...) that were
    # accidentally included during extraction.  These appear after a blank
    # line at column 0.
    gt_proof = re.sub(
        r'\n\n(?=/--|/-|example\b|def\b|theorem\b|lemma\b|#|open\b|namespace\b|section\b).*',
        '', gt_proof, flags=re.DOTALL)

    # Fix formal-snarks-project: In newer Mathlib, `simp_rw [Def]` no longer
    # reduces structure field projections like `.check_poly`.  Insert extra
    # unfold steps so the subsequent `simp only` calls can make progress.
    if lean_root == "formal-snarks-project":
        _unfold_line = (
            "  unfold AGMProofSystemInstantiation.check_poly "
            "AGMProofSystemInstantiation.pairing_poly "
            "AGMProofSystemInstantiation.proof_element_G1_as_poly "
            "AGMProofSystemInstantiation.proof_element_G2_as_poly at eqn\n"
            "  simp only [] at eqn\n"
        )
        # Insert after `simp_rw [<Name>] at eqn` when the next line is `simp only [monomial_zero'`
        gt_proof = re.sub(
            r'(simp_rw \[\w+\] at eqn\n)(  simp only \[monomial_zero)',
            r'\1' + _unfold_line + r'\2',
            gt_proof)

    # Fix bad import prefixes in the dataset.
    # iris-lean uses srcDir="./src/" so imports should not have 'src.' prefix.
    if lean_root == "iris-lean":
        imports = [imp.replace("import src.", "import ") for imp in imports]

    # Always read the full file and extract content before the theorem.
    # Fall back to imports + local_ctx only if the file can't be read or
    # the theorem can't be located in the file.
    fallback_ctx = "\n".join(imports) + "\n" + local_ctx
    # Fix truncated definitions in fallback context.
    _decl_kw_re = (r'(?:def |structure |class |instance |theorem |lemma |'
                   r'namespace |section |end |@\[|private |protected |noncomputable |open |'
                   r'set_option |variable |abbrev |inductive |mutual\b)')
    # Lines ending with `:=` followed by blank line + new declaration
    fallback_ctx = re.sub(
        r':=\s*\n(\s*\n)*(?=\s*' + _decl_kw_re + r')',
        ':= sorry\n\n', fallback_ctx)
    # Fix type aliases in fallback context: convert `def` to `abbrev` so
    # typeclass instances (Fintype, BEq, DecidableEq, etc.) propagate through
    # the alias automatically via Lean's definitional unfolding.
    fallback_ctx = re.sub(
        r'^def\s+(\w+)\s+(\([^)]+:\s*Type\*?\))\s*:=',
        r'abbrev \1 \2 :=',
        fallback_ctx, flags=re.MULTILINE)
    full_file_content = repl._docker_read_file(
        f"/workspace/lean_repos/{lean_root}/{rel_path}"
    )
    if full_file_content:
        verif_local_context = utils.get_content_before_theorem(full_file_content, thm_stmt, thm_name=thm_name)
        if verif_local_context is None:
            # Theorem not found in file. Try to insert before the last closing
            # 'end <Namespace>' so the theorem stays in the right namespace scope.
            # Extract namespace from thm_name (e.g., "Foo.Bar.baz" → "Foo.Bar")
            ns_parts = thm_name.rsplit('.', 1)
            if len(ns_parts) > 1:
                ns_name = ns_parts[0]
                # Find last "end <ns_name>" or "end <last_component>"
                last_component = ns_name.rsplit('.', 1)[-1]
                # Try to find the position of the last matching 'end' line
                end_pattern = re.compile(
                    r'^end\s+' + re.escape(ns_name) + r'\s*$|^end\s+' + re.escape(last_component) + r'\s*$',
                    re.MULTILINE)
                matches = list(end_pattern.finditer(full_file_content))
                if matches:
                    # Insert before the last matching 'end' line
                    insert_pos = matches[-1].start()
                    verif_local_context = full_file_content[:insert_pos]
                else:
                    verif_local_context = fallback_ctx
            else:
                verif_local_context = fallback_ctx
    else:
        verif_local_context = fallback_ctx

    # Strip 'noncomputable' from lemma/theorem declarations in context.
    # In Lean 4, theorems are always erased (non-computable by nature),
    # so 'noncomputable theorem/lemma' is an error.
    verif_local_context = re.sub(
        r'^noncomputable\s+(theorem|lemma)\b',
        r'\1',
        verif_local_context, flags=re.MULTILINE)

    # Replace non-target proof blocks in context that might fail to compile
    # in isolation (e.g., loom's `prove_correct X by <tactics>`).
    # Replace their tactic bodies with `sorry` so the context compiles.
    verif_local_context = re.sub(
        r'(prove_correct\??\s+\w+)\s+by\n.*?(?=\n\n|\n(?:prove_correct|theorem|lemma|def|--[^\n]*\n\n))',
        r'\1 by sorry',
        verif_local_context,
        flags=re.DOTALL)

    # If thm_stmt starts with @[attr] and context ends with the same attribute,
    # strip it from thm_stmt to avoid duplication (format_generated_lean moves
    # trailing attributes from context to before the theorem stmt).
    stmt_lines = thm_stmt.split('\n')
    if stmt_lines and stmt_lines[0].strip().startswith('@[') and stmt_lines[0].strip().endswith(']'):
        attr = stmt_lines[0].strip()
        ctx_lines = verif_local_context.rstrip().split('\n')
        if ctx_lines and ctx_lines[-1].strip() == attr:
            thm_stmt = '\n'.join(stmt_lines[1:])

    # Fix maxRecDepth for files that need deep recursion (e.g., BLAKE3/ApplyRounds)
    # Insert AFTER imports (imports must come first in Lean 4)
    if "BLAKE3/ApplyRounds" in rel_path or "BLAKE3.ApplyRounds" in thm_name:
        lines = verif_local_context.split('\n')
        last_import = -1
        for i, line in enumerate(lines):
            if line.strip().startswith('import '):
                last_import = i
        if last_import >= 0:
            lines.insert(last_import + 1, '\nset_option maxRecDepth 16384\nset_option maxHeartbeats 0')
        else:
            lines.insert(0, 'set_option maxRecDepth 16384\nset_option maxHeartbeats 0')
        verif_local_context = '\n'.join(lines)
        # Sorry-out expensive multi-line `(by ...)` proof blocks in context.
        # Circuit definitions use deeply recursive proofs that take >5min to
        # type-check but are Prop-valued and don't affect the soundness proof.
        verif_local_context = re.sub(
            r'\(by\b\n.*?\)', '(by sorry)',
            verif_local_context, flags=re.DOTALL)

    t0 = time.time()
    try:
        success, error_msg = repl.verify_proof(
            thm_name=thm_name,
            repo_name=lean_root,
            rel_path=rel_path,
            local_context=verif_local_context,
            theorem_stmt=thm_stmt,
            theorem_proof=gt_proof,
            proof_id="gt",
            aux_lemmas="",
            suffix=suffix,
        )
    except Exception as e:
        success = False
        error_msg = f"Exception: {e}"

    elapsed = time.time() - t0

    return {
        "id": task_id,
        "thm_name": thm_name,
        "lean_root": lean_root,
        "success": success,
        "error": error_msg if not success else None,
        "time_s": round(elapsed, 1),
    }


def main():
    max_workers = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    # Optional: skip repos listed in SKIP_REPOS env var (comma-separated)
    skip_repos = set(filter(None, os.environ.get("SKIP_REPOS", "").split(",")))

    entries = load_entries(DATASET)
    if skip_repos:
        entries = [e for e in entries if e["lean_root"] not in skip_repos]
        print(f"Skipping repos: {skip_repos}")
    print(f"Loaded {len(entries)} tasks from {DATASET}")

    repl = LeanREPL(lean_src_dir=LEAN_SRC_DIR, docker_container=DOCKER_CONTAINER)

    results = []
    passed = 0
    failed = 0
    t_start = time.time()

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {
            executor.submit(verify_one, repl, entry): entry
            for entry in entries
        }

        for future in as_completed(futures):
            r = future.result()
            results.append(r)
            if r["success"]:
                passed += 1
                status = "PASS"
            else:
                failed += 1
                status = "FAIL"

            total_done = passed + failed
            print(
                f"[{total_done}/{len(entries)}] {status} | {r['lean_root']}/{r['thm_name']} "
                f"({r.get('time_s', '?')}s)"
                + (f" | {r['error'][:120]}" if r.get("error") else "")
            )

    elapsed_total = time.time() - t_start

    # Sort results by id for stable output
    results.sort(key=lambda x: x["id"])

    # Save full results
    out_path = Path("results/ground_truth_verification.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)

    # Print summary
    print("\n" + "=" * 70)
    print(f"GROUND TRUTH VERIFICATION SUMMARY")
    print(f"=" * 70)
    print(f"Total:  {len(results)}")
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")
    print(f"Rate:   {passed/len(results)*100:.1f}%")
    print(f"Time:   {elapsed_total:.0f}s")
    print(f"Results saved to: {out_path}")

    # Print failures grouped by repo
    if failed > 0:
        print(f"\n{'=' * 70}")
        print("FAILURES BY REPO:")
        print(f"{'=' * 70}")
        failures = [r for r in results if not r["success"]]
        by_repo = {}
        for f_result in failures:
            repo = f_result["lean_root"]
            by_repo.setdefault(repo, []).append(f_result)

        for repo in sorted(by_repo.keys()):
            items = by_repo[repo]
            print(f"\n  {repo} ({len(items)} failures):")
            for item in items:
                err_short = (item.get("error") or "")[:100]
                print(f"    - [{item['id']}] {item['thm_name']}: {err_short}")


if __name__ == "__main__":
    main()
