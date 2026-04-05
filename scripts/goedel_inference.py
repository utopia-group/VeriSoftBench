#!/usr/bin/env python3
"""Standalone inference script for Goedel-Code-Prover-8B on VeriSoftBench.

Runs inference only (no Lean verification). Produces a JSONL file with raw
model outputs that can be verified separately.

Usage:
    # Start vLLM server first:
    #   vllm serve Goedel-LM/Goedel-Code-Prover-8B --port 8000
    #
    # Then run inference:
    python scripts/goedel_inference.py \
        --base-url http://localhost:8000/v1 \
        --output results/goedel_8b_inference.jsonl \
        [--subset 20] [--task-ids 1,50,100]
"""

import argparse
import json
import os
import random
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Any, List, Optional

import openai

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from config.paths import PROJECT_ROOT

GOEDEL_SYSTEM_PROMPT = """You are an expert in Lean 4 theorem proving and proof decomposition.

Given a formal problem in Lean 4, your task is to:
1. First, analyze and reason about how to decompose the proof into smaller lemmas
2. Then, provide the complete proof with all necessary lemmas

Requirements for the proof breakdown:
- Break down the theorem into the smallest possible lemmas
- Each lemma should ideally involve a single Lean 4 basic function operation
- The introduced lemmas should not involve universe types
- Ensure logical ordering: lemmas should be defined before they are used

Requirements for the format of the proof:
- The original theorem MUST be proved WITHOUT sorry (using the defined lemmas)
- Each lemma should be proved with a complete proof if possible
- Use the 'lemma' keyword for lemmas and the 'theorem' keyword for the original theorem
- Wrap all proof code in ```lean code blocks"""


def load_entries(data_dir: Path, filename: str = "verisoftbench.jsonl") -> List[Dict]:
    """Load benchmark entries from JSONL."""
    path = data_dir / filename
    entries = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    print(f"Loaded {len(entries)} entries from {path}")
    return entries


def build_goedel_user_prompt(entry: Dict[str, Any]) -> str:
    """Build Goedel-style 'Formal Problem:' prompt with VeriSoftBench context."""
    parts = []

    # Local context
    local_ctx = entry.get("local_ctx", "")
    if local_ctx and local_ctx.strip():
        parts.append(local_ctx.strip())

    # Library definitions (as comments for reference)
    lib_defs = entry.get("used_lib_defs", [])
    if lib_defs:
        defs_lines = []
        for item in lib_defs:
            name = item.get("name", "")
            module = item.get("module", "")
            if module:
                defs_lines.append(f"-- {name} from {module}")
            elif name:
                defs_lines.append(f"-- {name}")
        if defs_lines:
            parts.append("-- Available library definitions:\n" + "\n".join(defs_lines))

    # Repository definitions
    repo_defs = entry.get("used_repo_defs", [])
    if repo_defs:
        repo_parts = [item.get("content", "") for item in repo_defs
                       if item.get("content", "").strip()]
        if repo_parts:
            parts.append("-- Repository definitions:\n" + "\n\n".join(repo_parts))

    # Theorem with sorry
    thm_stmt = entry.get("thm_stmt", "") or entry.get("target_theorem", "")
    thm_with_sorry = thm_stmt.rstrip()
    if thm_with_sorry.endswith(":="):
        thm_with_sorry += " by sorry"
    elif not thm_with_sorry.endswith("sorry"):
        thm_with_sorry += " := by sorry"

    parts.append(thm_with_sorry)

    context_and_theorem = "\n\n".join(parts)
    return f"Formal Problem:\n{context_and_theorem}"


def run_inference(
    client: openai.OpenAI,
    model_id: str,
    entry: Dict[str, Any],
    temperature: float = 0.9,
    max_tokens: int = 16384,
    num_samples: int = 1,
) -> Dict[str, Any]:
    """Run inference for a single theorem entry."""
    user_prompt = build_goedel_user_prompt(entry)

    results = []
    # Use vLLM's n parameter for batched sampling (much faster than sequential)
    max_per_call = 8  # vLLM handles up to 8 well per request
    remaining = num_samples
    while remaining > 0:
        batch_n = min(max_per_call, remaining)
        try:
            response = client.chat.completions.create(
                model=model_id,
                messages=[
                    {"role": "system", "content": GOEDEL_SYSTEM_PROMPT},
                    {"role": "user", "content": user_prompt},
                ],
                temperature=temperature,
                max_tokens=max_tokens,
                n=batch_n,
            )

            for choice in response.choices:
                results.append({
                    "model_response": choice.message.content,
                    "finish_reason": choice.finish_reason,
                    "usage": {
                        "prompt_tokens": response.usage.prompt_tokens,
                        "completion_tokens": response.usage.completion_tokens,
                    } if response.usage else None,
                })
        except Exception as e:
            print(f"  ERROR on batch (n={batch_n}): {e}")
            for _ in range(batch_n):
                results.append({
                    "model_response": None,
                    "finish_reason": "error",
                    "error": str(e),
                })
        remaining -= batch_n

    return {
        "id": entry["id"],
        "thm_name": entry["thm_name"],
        "lean_root": entry["lean_root"],
        "rel_path": entry["rel_path"],
        "category": entry.get("category", ""),
        "thm_stmt": entry.get("thm_stmt", ""),
        "user_prompt": user_prompt,
        "system_prompt": GOEDEL_SYSTEM_PROMPT,
        "samples": results,
        "inference_params": {
            "model_id": model_id,
            "temperature": temperature,
            "max_tokens": max_tokens,
        },
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }


def parse_task_ids(task_ids_str: str) -> Optional[List[int]]:
    """Parse task ID string into list of ints."""
    if not task_ids_str:
        return None
    if ":" in task_ids_str:
        start, end = task_ids_str.split(":")
        return list(range(int(start), int(end) + 1))
    return [int(x.strip()) for x in task_ids_str.split(",")]


def stratified_sample(entries: List[Dict], n: int, seed: int = 42) -> List[Dict]:
    """Sample n entries stratified across repos, covering all categories."""
    rng = random.Random(seed)

    # Group by repo
    by_repo = {}
    for e in entries:
        by_repo.setdefault(e["lean_root"], []).append(e)

    # Allocate proportionally, minimum 1 per repo
    repos = sorted(by_repo.keys())
    n_repos = len(repos)

    if n >= len(entries):
        return entries

    # At least 1 per repo if possible
    per_repo = max(1, n // n_repos)
    sampled = []
    remaining_budget = n

    for repo in repos:
        pool = by_repo[repo]
        take = min(per_repo, len(pool), remaining_budget)
        if take <= 0:
            continue
        sampled.extend(rng.sample(pool, take))
        remaining_budget -= take

    # Fill remaining budget randomly from unsampled entries
    if remaining_budget > 0:
        sampled_ids = {e["id"] for e in sampled}
        unsampled = [e for e in entries if e["id"] not in sampled_ids]
        rng.shuffle(unsampled)
        sampled.extend(unsampled[:remaining_budget])

    return sampled


def main():
    parser = argparse.ArgumentParser(description="Goedel-Code-Prover-8B inference on VeriSoftBench")
    parser.add_argument("--base-url", type=str, default="http://localhost:8000/v1",
                        help="vLLM server URL (default: http://localhost:8000/v1)")
    parser.add_argument("--model-id", type=str, default="Goedel-LM/Goedel-Code-Prover-8B",
                        help="Model ID as served by vLLM")
    parser.add_argument("--output", type=str, required=True,
                        help="Output JSONL file path")
    parser.add_argument("--data-dir", type=str, default=str(PROJECT_ROOT / "data"),
                        help="Directory containing verisoftbench.jsonl")
    parser.add_argument("--temperature", type=float, default=0.9)
    parser.add_argument("--max-tokens", type=int, default=16384)
    parser.add_argument("--num-samples", type=int, default=1,
                        help="Samples per theorem (pass@k)")
    parser.add_argument("--task-ids", type=str, default=None,
                        help="Specific task IDs (e.g., '1,50,100' or '1:20')")
    parser.add_argument("--subset", type=int, default=None,
                        help="Stratified sample of N entries across repos")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--save-every", type=int, default=10,
                        help="Save intermediate results every N theorems")
    args = parser.parse_args()

    # Load entries
    entries = load_entries(Path(args.data_dir))

    # Filter
    if args.task_ids:
        ids = set(parse_task_ids(args.task_ids))
        entries = [e for e in entries if e["id"] in ids]
        print(f"Filtered to {len(entries)} entries by task IDs")
    elif args.subset:
        entries = stratified_sample(entries, args.subset, seed=args.seed)
        print(f"Stratified sample: {len(entries)} entries across {len(set(e['lean_root'] for e in entries))} repos")

    # Initialize client
    client = openai.OpenAI(api_key="dummy", base_url=args.base_url, timeout=3600)

    # Test connection
    print(f"Testing connection to {args.base_url}...")
    try:
        models = client.models.list()
        available = [m.id for m in models.data]
        print(f"Available models: {available}")
        if args.model_id not in available:
            print(f"WARNING: {args.model_id} not in available models. Using first: {available[0]}")
            args.model_id = available[0]
    except Exception as e:
        print(f"ERROR: Cannot connect to vLLM server: {e}")
        sys.exit(1)

    # Run inference
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    # Resume from existing output if present
    completed_ids = set()
    if output_path.exists():
        with open(output_path, "r") as f:
            for line in f:
                if line.strip():
                    r = json.loads(line)
                    completed_ids.add(r["id"])
        print(f"Resuming: {len(completed_ids)} already completed")
        entries = [e for e in entries if e["id"] not in completed_ids]

    total = len(entries)
    successes = 0
    truncations = 0
    errors = 0
    start_time = time.time()

    print(f"\nStarting inference: {total} theorems, {args.num_samples} sample(s) each")
    print(f"Output: {output_path}")
    print(f"Params: temp={args.temperature}, max_tokens={args.max_tokens}")
    print("=" * 60)

    with open(output_path, "a", encoding="utf-8") as f:
        for i, entry in enumerate(entries):
            thm_name = entry["thm_name"]
            elapsed = time.time() - start_time
            rate = (i + 1) / elapsed if elapsed > 0 else 0
            eta = (total - i - 1) / rate if rate > 0 else 0

            print(f"[{i+1}/{total}] {thm_name} (ETA: {eta/60:.1f}m)")

            result = run_inference(
                client, args.model_id, entry,
                temperature=args.temperature,
                max_tokens=args.max_tokens,
                num_samples=args.num_samples,
            )

            # Track stats
            for s in result["samples"]:
                if s.get("finish_reason") == "length":
                    truncations += 1
                    print(f"  WARNING: truncated (finish_reason=length)")
                elif s.get("finish_reason") == "error":
                    errors += 1
                elif s.get("model_response"):
                    successes += 1

            f.write(json.dumps(result, ensure_ascii=False) + "\n")

            # Periodic flush
            if (i + 1) % args.save_every == 0:
                f.flush()
                os.fsync(f.fileno())
                print(f"  [SAVED] {i+1}/{total} complete | "
                      f"{successes} ok, {truncations} truncated, {errors} errors")

    elapsed = time.time() - start_time
    print(f"\n{'='*60}")
    print(f"Done! {total} theorems in {elapsed/60:.1f} minutes")
    print(f"  Successes: {successes}")
    print(f"  Truncations: {truncations}")
    print(f"  Errors: {errors}")
    print(f"  Output: {output_path}")


if __name__ == "__main__":
    main()
