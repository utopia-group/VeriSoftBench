#!/usr/bin/env python3
"""
Generate a unified per-repo index of Lean declarations.

Uses the ProofChunker from PLProofBenchEval (vendored in scripts/chunking/)
to parse Lean files, capturing all declaration types including macros,
notations, syntax, elabs, etc.

Outputs one JSON file per repo at ``<output-dir>/<repo>.json``.

Designed to run inside the Docker container against the actual Lean sources,
then copied out:

    docker exec verisoftbench-test python3 /workspace/scripts/generate_repo_index.py \
        --repos-dir /workspace/lean_repos --output-dir /workspace/repo_index
    docker cp verisoftbench-test:/workspace/repo_index/ data/repo_index/

Can also be run locally:

    python3 scripts/generate_repo_index.py \
        --repos-dir data/lean_repos --output-dir data/repo_index
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from collections import defaultdict
from pathlib import Path
from typing import Dict, Iterable, List

# Add scripts/ to path so we can import the vendored chunking module
sys.path.insert(0, str(Path(__file__).parent))
from chunking import ProofChunker


# Kinds that go into definitions_by_file (everything except theorem/lemma)
THEOREM_KINDS = {"theorem", "lemma"}

# Scope-related kinds we skip (not real declarations)
SKIP_KINDS = {"import", "open", "variable", "section", "end", "export"}


def _canonical_name(decl: Dict) -> str:
    parent = decl.get("parent")
    simple = decl.get("simple") or decl["name"]
    if parent:
        return f"{parent}.{simple}"
    return decl["name"]


def _definition_aliases(decl: Dict) -> Iterable[str]:
    name = decl["name"]
    simple = decl.get("simple")
    aliases = {_canonical_name(decl), name, name.split(".")[-1]}
    if simple:
        aliases.add(simple)
    return aliases


def collect_repo_declarations(repo_path: Path) -> Dict[str, Dict[str, List[Dict]]]:
    """
    Return mapping of Lean file (relative) -> {definitions, theorems}.

    Each entry carries: name, aliases, kind, namespace, line, end_line, text.
    """
    chunker = ProofChunker(cache_enabled=False)

    file_defs: Dict[str, Dict[str, Dict]] = defaultdict(dict)
    file_thms: Dict[str, Dict[str, Dict]] = defaultdict(dict)

    lean_files = list(repo_path.rglob("*.lean"))
    for lean_file in lean_files:
        if ".lake" in lean_file.parts:
            continue

        try:
            result = chunker.chunk_file(lean_file)
        except Exception as e:
            print(f"  Warning: Could not parse {lean_file}: {e}")
            continue

        rel = str(lean_file.relative_to(repo_path))

        for chunk in result.chunks:
            if chunk.kind in SKIP_KINDS:
                continue

            decl = {
                "kind": chunk.kind,
                "name": chunk.name,
                "simple": chunk.simple_name,
                "namespace": chunk.namespace,
                "line": chunk.start_line,
                "end_line": chunk.end_line,
                "text": chunk.text,
            }
            if chunk.parent:
                decl["parent"] = chunk.parent

            if chunk.kind in THEOREM_KINDS:
                target = file_thms
            else:
                target = file_defs

            canon = _canonical_name(decl)
            entry = target[rel].setdefault(
                canon,
                {
                    "name": canon,
                    "aliases": set(),
                    "kind": decl["kind"],
                    "namespace": decl.get("namespace", ""),
                    "line": decl["line"],
                    "end_line": decl.get("end_line"),
                    "text": decl.get("text", ""),
                },
            )
            entry["aliases"].update(_definition_aliases(decl))
            if decl.get("parent"):
                entry.setdefault("parent", decl["parent"])

    def _finish(entries: Dict[str, Dict]) -> List[Dict]:
        out = []
        for entry in entries.values():
            entry["aliases"] = sorted(entry["aliases"])
            out.append(entry)
        return sorted(out, key=lambda e: (e["line"], e["name"]))

    return {
        "definitions_by_file": {f: _finish(defs) for f, defs in file_defs.items()},
        "theorems_by_file": {f: _finish(thms) for f, thms in file_thms.items()},
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def find_repos(root: Path, explicit: List[str] | None, include_all: bool) -> List[Path]:
    if explicit:
        return [root / r for r in explicit]
    if include_all:
        repos = []
        for item in sorted(root.iterdir()):
            if item.is_dir() and not item.name.startswith(".") and list(item.rglob("*.lean")):
                repos.append(item)
        return repos
    raise SystemExit("Please specify --repos or --all")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate unified repo index for VeriSoftBench."
    )
    parser.add_argument(
        "--repos-dir",
        type=Path,
        required=True,
        help="Root directory containing Lean repositories.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="Output directory for per-repo JSON index files.",
    )
    parser.add_argument(
        "--repos",
        nargs="+",
        help="Specific repositories to process (names, not full paths).",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        default=True,
        help="Process all Lean repositories (default).",
    )
    args = parser.parse_args()

    repos = find_repos(args.repos_dir, args.repos, args.all)
    args.output_dir.mkdir(parents=True, exist_ok=True)

    for repo in repos:
        if not repo.exists():
            print(f"Skipping missing repo: {repo}")
            continue
        data = collect_repo_declarations(repo)
        has_defs = bool(data["definitions_by_file"])
        has_thms = bool(data["theorems_by_file"])
        if not (has_defs or has_thms):
            print(f"No Lean declarations found in {repo.name}; skipping.")
            continue

        payload = {
            "repository": repo.name,
            **data,
        }
        out_path = args.output_dir / f"{repo.name}.json"
        with out_path.open("w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)

        n_files_defs = len(data["definitions_by_file"])
        n_files_thms = len(data["theorems_by_file"])
        print(f"  {repo.name}: {n_files_defs} def-files, {n_files_thms} thm-files -> {out_path.name}")


if __name__ == "__main__":
    main()
