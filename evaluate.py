#!/usr/bin/env python3
"""
VeriSoftBench evaluation script.

Runs benchmark evaluation on the VeriSoftBench dataset using neural theorem provers.
"""

import argparse
from pathlib import Path
from typing import Dict, Any, List, Optional
import sys
import yaml
import json

# Add release directory to path for module imports
sys.path.insert(0, str(Path(__file__).parent))

from core.evaluator import BenchmarkEvaluator
import utils.utils as utils
from config.paths import (
    PROJECT_ROOT,
    EVAL_INPUT_DIR,
    LEAN_SRC_DIR,
    PROMPTS_DIR,
    RESULTS_DATA_DIR,
    RESULTS_CACHE_DIR,
    get_lean_src_dir
)


def load_config(config_path: Path) -> Dict[str, Any]:
    """Load configuration from YAML file."""
    if not config_path.exists():
        raise FileNotFoundError(f"Config file not found: {config_path}")

    with open(config_path, 'r') as f:
        config = yaml.safe_load(f)

    return config if config else {}


def merge_config_with_args(config: Dict[str, Any], args: argparse.Namespace) -> argparse.Namespace:
    """
    Merge config file values with command-line arguments.
    Config file values take precedence and override any command-line arguments.
    """
    config_to_arg_map = {
        'locator_data_dir': 'locator_data_dir',
        'lean_src_dir': 'lean_src_dir',
        'prompts_dir': 'prompts_dir',
        'output_dir': 'output_dir',
        'locator_file': 'locator_file',
        'fix_enabled': 'fix_enabled',  # from config file only
        'num_samples': 'num_samples',
        'model_name': 'model_name',
        'model_id': 'model_id',
        'temperature': 'temperature',
        'max_tokens': 'max_tokens',
        'api_key': 'api_key',
        'max_workers': 'max_workers',
        'max_fix_workers': 'max_fix_workers',
        'subset': 'subset',
        'category': 'category',
        'task_ids': 'task_ids',
        'run_name': 'run_name',
        'rate_limit_rpm': 'rate_limit_rpm',
        'mode': 'mode',
        'refresh_cache': 'refresh_cache',
        'save_debug_lean': 'save_debug_lean',
        'lean_backend': 'lean_backend',
        'docker_container': 'docker_container'
    }

    for config_key, arg_key in config_to_arg_map.items():
        if config_key in config:
            config_value = config[config_key]

            # Convert string paths to Path objects where appropriate
            if arg_key in ['locator_data_dir', 'lean_src_dir', 'prompts_dir', 'output_dir']:
                if isinstance(config_value, str):
                    config_value = Path(config_value)
                    if not config_value.is_absolute():
                        config_value = PROJECT_ROOT / config_value

            setattr(args, arg_key, config_value)

    return args


def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(
        description="Run VeriSoftBench evaluation for neural theorem proving",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Use a config file (recommended)
  python evaluate.py --config configs/openai_example.yaml

  # Use command-line arguments
  python evaluate.py --model-name openai --model-id gpt-4o --task-ids 1,2,3

  # Evaluate specific tasks
  python evaluate.py --config configs/default.yaml --task-ids 1:10

Note: When using --config, config file values take precedence over CLI args.
        """
    )

    # Config file option
    parser.add_argument(
        "--config", type=Path, default=None,
        help="Path to YAML configuration file"
    )

    # Required paths
    parser.add_argument(
        "--locator-data-dir", type=Path, default=EVAL_INPUT_DIR,
        help="Directory containing benchmark data files (default: data/)"
    )
    parser.add_argument(
        "--lean-src-dir", type=Path, default=None,
        help="Directory containing Lean source repositories (default: data/lean_repos, or VERISOFTBENCH_LEAN_SRC env var)"
    )
    parser.add_argument(
        "--prompts-dir", type=Path, default=PROMPTS_DIR,
        help="Directory containing prompt templates (default: prompts/templates)"
    )
    parser.add_argument(
        "--output-dir", type=Path, default=RESULTS_DATA_DIR,
        help="Directory to save evaluation results (default: results/data)"
    )

    # Input data
    parser.add_argument(
        "--locator-file", type=str, default="verisoftbench.jsonl",
        help="Name of benchmark JSONL file (default: verisoftbench.jsonl)"
    )
    parser.add_argument(
        "--no-fix", action="store_true", default=False,
        help="Disable proof fixing step (fixing is enabled by default)"
    )
    parser.add_argument(
        "--num-samples", type=int, default=1,
        help="Number of samples to generate per theorem (default: 1)"
    )

    # Model configuration
    parser.add_argument(
        "--model-name", type=str, default="openai",
        choices=["openai", "claude", "gemini"],
        help="Model provider (default: openai)"
    )
    parser.add_argument(
        "--model-id", type=str, default="gpt-4o",
        help="Model ID to use (default: gpt-4o)"
    )
    parser.add_argument(
        "--temperature", type=float, default=0.7,
        help="Sampling temperature (default: 0.7)"
    )
    parser.add_argument(
        "--max-tokens", type=int, default=8192,
        help="Maximum tokens to generate (default: 8192)"
    )
    parser.add_argument(
        "--api-key", type=str, default=None,
        help="API key for model (if not set via environment variable)"
    )

    # Parallelism settings
    parser.add_argument(
        "--max-workers", type=int, default=8,
        help="Number of parallel workers for benchmark tasks (default: 8)"
    )
    parser.add_argument(
        "--max-fix-workers", type=int, default=4,
        help="Number of parallel workers for fixing samples per task (default: 4)"
    )

    # Subset selection
    parser.add_argument(
        "--subset", type=int, default=None,
        help="Evaluate on a subset of N entries (default: all)"
    )
    parser.add_argument(
        "--category", type=str, default=None,
        help="Filter by category"
    )
    parser.add_argument(
        "--task-ids", type=str, default=None,
        help="Select specific tasks by ID. Comma-separated (e.g., '1,3,5') or range (e.g., '1:10')"
    )

    # Output naming
    parser.add_argument(
        "--run-name", type=str, default=None,
        help="Name for this evaluation run (default: auto-generated)"
    )

    # Rate limiting
    parser.add_argument(
        "--rate-limit-rpm", type=int, default=None,
        help="Rate limit per minute for API requests (default: None)"
    )

    # Mode selection
    parser.add_argument(
        "--mode", type=str, default="filtered_context",
        choices=["filtered_context", "full_context", "full_context_limited"],
        help="Context mode (default: filtered_context)"
    )
    parser.add_argument(
        "--refresh-cache", action="store_true",
        help="Re-run all tasks and overwrite cache entries"
    )
    parser.add_argument(
        "--save-debug-lean", action="store_true",
        help="Save postprocessed Lean files for debugging"
    )
    parser.add_argument(
        "--validate-repos", action="store_true",
        help="Check that all required Lean repos are built before starting evaluation"
    )
    parser.add_argument(
        "--lean-backend", type=str, default="local",
        choices=["local", "docker"],
        help="Lean compilation backend: 'local' runs lake/lean directly, "
             "'docker' uses docker exec against a running container (default: local)"
    )
    parser.add_argument(
        "--docker-container", type=str, default="verisoftbench-lean",
        help="Docker container name for --lean-backend docker (default: verisoftbench-lean)"
    )

    return parser.parse_args()


def parse_task_ids(task_ids_val) -> Optional[List[int]]:
    """Normalize task_ids to a list of ints."""
    if task_ids_val is None:
        return None

    if isinstance(task_ids_val, int):
        return [task_ids_val]

    if isinstance(task_ids_val, (list, tuple)):
        return [int(item) for item in task_ids_val]

    if isinstance(task_ids_val, str):
        task_ids_str = task_ids_val.strip()
        if not task_ids_str:
            return None

        if ':' in task_ids_str:
            parts = task_ids_str.split(':')
            if len(parts) != 2:
                raise ValueError(f"Invalid range format: {task_ids_str}")
            start = int(parts[0].strip())
            end = int(parts[1].strip())
            if start > end:
                raise ValueError(f"Invalid range: start ({start}) must be <= end ({end})")
            return list(range(start, end + 1))

        return [int(id_str.strip()) for id_str in task_ids_str.split(',') if id_str.strip()]

    raise ValueError(f"Unsupported task_ids type: {type(task_ids_val)}")


def load_entries(locator_data_dir: Path, locator_file: str) -> list:
    """Load entries from benchmark file (supports both .jsonl and .json formats)."""
    locator_path = locator_data_dir / locator_file

    if not locator_path.exists():
        raise FileNotFoundError(f"Benchmark file not found: {locator_path}")

    print(f"Loading entries from: {locator_path}")

    if locator_path.suffix == '.json':
        with open(locator_path, 'r', encoding='utf-8') as f:
            entries = json.load(f)
    else:
        entries = utils.load_jsonl(locator_path)

    print(f"Loaded {len(entries)} entries")
    return entries


def filter_entries(entries: list, category: str = None, subset: int = None, task_ids: list = None) -> list:
    """Filter entries by category, task IDs, and/or subset size."""
    filtered = entries

    if task_ids:
        task_ids_set = set(task_ids)
        filtered = [e for e in filtered if e.get("id") in task_ids_set]
        print(f"Filtered to {len(filtered)} entries with IDs: {sorted(task_ids)}")

    if category:
        filtered = [e for e in filtered if e.get("category") == category]
        print(f"Filtered to {len(filtered)} entries in category '{category}'")

    if subset and subset < len(filtered):
        filtered = filtered[:subset]
        print(f"Using subset of {len(filtered)} entries")

    return filtered


def create_model_config(args) -> Dict[str, Any]:
    """Create model configuration dictionary from arguments."""
    config = {
        "model_name": args.model_name,
        "model_id": args.model_id,
        "temperature": args.temperature,
        "max_tokens": args.max_tokens,
        "num_samples": args.num_samples,
        "rate_limit_rpm": args.rate_limit_rpm,
        "mode": args.mode
    }

    if args.api_key:
        config["api_key"] = args.api_key

    return config


def generate_run_name(args) -> str:
    """Generate a run name if not provided."""
    import datetime
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")

    if args.run_name:
        return args.run_name + f"_{timestamp}"

    components = [
        args.model_id.replace("/", "_"),
        timestamp
    ]

    if args.category:
        components.insert(1, args.category.replace(" ", "_"))

    if args.subset:
        components.insert(-1, f"n{args.subset}")

    return "_".join(components)


def get_cache_path(model_id: str, mode: str) -> Path:
    """Get the cache file path for a specific model."""
    if mode in ("full_context", "full_context_limited"):
        safe_model_id = model_id.replace("/", "_").replace(":", "_") + "_full_context"
    else:
        safe_model_id = model_id.replace("/", "_").replace(":", "_")
    return RESULTS_CACHE_DIR / f"{safe_model_id}.jsonl"


def load_cache(model_id: str, mode: str) -> Dict[tuple, Dict[str, Any]]:
    """Load cache entries for a specific model."""
    cache_path = get_cache_path(model_id, mode)
    cache = {}

    if cache_path.exists():
        try:
            with open(cache_path, 'r', encoding='utf-8') as f:
                for line in f:
                    if line.strip():
                        entry = json.loads(line)
                        key = (entry["thm_name"], entry["lean_root"], entry["rel_path"])
                        cache[key] = entry
            print(f"Loaded {len(cache)} cached results from {cache_path}")
        except Exception as e:
            print(f"Warning: Could not load cache from {cache_path}: {e}")

    return cache


def check_cache_match(cache_entry: Dict[str, Any], model_config: Dict[str, Any]) -> bool:
    """Check if a cached entry matches the current model configuration."""
    cached_config = cache_entry.get("model_config", {})
    keys_to_match = ["model_name", "model_id", "temperature", "max_tokens", "num_samples", "num_fixes"]

    for key in keys_to_match:
        if cached_config.get(key) != model_config.get(key):
            return False
    return True


def save_to_cache(
    model_id: str, task_id: int, thm_name: str, lean_root: str, rel_path: str,
    model_config: Dict[str, Any], run_name: str, success: bool, fix_success: bool, mode: str
) -> None:
    """Save a result to the cache."""
    cache_path = get_cache_path(model_id, mode)
    cache_path.parent.mkdir(parents=True, exist_ok=True)

    existing_cache = load_cache(model_id, mode)

    cache_entry = {
        "task_id": task_id,
        "thm_name": thm_name,
        "lean_root": lean_root,
        "rel_path": rel_path,
        "model_config": {
            "model_name": model_config.get("model_name"),
            "model_id": model_config.get("model_id"),
            "temperature": model_config.get("temperature"),
            "max_tokens": model_config.get("max_tokens"),
            "num_samples": model_config.get("num_samples"),
            "num_fixes": model_config.get("num_fixes", 3)
        },
        "run_name": run_name,
        "success": success,
        "fix_success": fix_success
    }

    existing_cache[task_id] = cache_entry

    try:
        with open(cache_path, 'w', encoding='utf-8') as f:
            for entry in existing_cache.values():
                f.write(json.dumps(entry) + '\n')
    except Exception as e:
        print(f"Warning: Could not save to cache: {e}")


def main():
    """Main execution function."""
    args = parse_args()

    # Load and merge config file if provided
    if args.config:
        print(f"Loading configuration from: {args.config}")
        try:
            config = load_config(args.config)
            args = merge_config_with_args(config, args)
            print(f"Configuration loaded successfully")
        except Exception as e:
            print(f"ERROR: Failed to load config file: {e}")
            return 1

    # Resolve fix_enabled: config file > CLI flag > default (True)
    if not hasattr(args, 'fix_enabled') or args.fix_enabled is None:
        args.fix_enabled = not args.no_fix

    # Resolve lean_src_dir: env var > CLI/config > default
    # Env var takes highest precedence (standard for Docker deployments)
    import os
    env_lean_src = os.environ.get("VERISOFTBENCH_LEAN_SRC")
    if env_lean_src:
        args.lean_src_dir = Path(env_lean_src)
    elif args.lean_src_dir is None:
        args.lean_src_dir = get_lean_src_dir()

    # Create output directory if it doesn't exist
    args.output_dir.mkdir(parents=True, exist_ok=True)

    # Generate run name
    run_name = generate_run_name(args)
    print(f"\n{'='*60}")
    print(f"Starting evaluation run: {run_name} {'with' if args.fix_enabled else 'without'} proof fixing")
    print(f"{'='*60}\n")

    # Validate Docker container if using docker backend
    if args.lean_backend == "docker":
        import subprocess as _sp
        try:
            result = _sp.run(
                ["docker", "inspect", "-f", "{{.State.Running}}", args.docker_container],
                capture_output=True, text=True
            )
            if result.returncode != 0 or "true" not in result.stdout.lower():
                print(f"ERROR: Docker container '{args.docker_container}' is not running.")
                print(f"Start it with: docker run -d --name {args.docker_container} verisoftbench/lean:latest")
                return 1
            print(f"Docker container '{args.docker_container}' is running.")
        except FileNotFoundError:
            print("ERROR: 'docker' command not found. Install Docker or use --lean-backend local.")
            return 1

    # Print configuration
    print("Configuration:")
    print(f"  Model: {args.model_id}")
    print(f"  Mode: {args.mode}")
    print(f"  Lean backend: {args.lean_backend}" + (f" ({args.docker_container})" if args.lean_backend == "docker" else ""))
    print(f"  Number of samples: {args.num_samples}")
    print(f"  Rate limit per Minute: {args.rate_limit_rpm if args.rate_limit_rpm else -1}")
    print(f"  Refresh cache: {'yes' if args.refresh_cache else 'no'}")
    print(f"  Configuration path: {args.config if args.config else 'N/A'}")
    print(f"  Output directory: {args.output_dir}")
    print()
    args.log_file = args.output_dir / f"{run_name}_evaluation.log"

    # Load entries
    try:
        entries = load_entries(args.locator_data_dir, args.locator_file)
        # _clean_thm_stmt in evaluator.py strips any embedded proof bodies
        # and appends the correct separator (:=, where, or nothing for |).
    except Exception as e:
        print(f"ERROR: Failed to load entries: {e}")
        return 1

    # Parse task IDs if provided
    task_ids = None
    if args.task_ids:
        try:
            task_ids = parse_task_ids(args.task_ids)
            print(f"Selected task IDs: {sorted(task_ids) if len(task_ids) <= 20 else f'{sorted(task_ids[:10])}...{sorted(task_ids[-10:])}'}")
        except ValueError as e:
            print(f"ERROR: {e}")
            return 1

    # Filter entries
    entries = filter_entries(entries, args.category, args.subset, task_ids)

    if len(entries) == 0:
        print("ERROR: No entries to evaluate after filtering")
        return 1

    # Validate repos if requested
    if args.validate_repos:
        required_repos = set(e["lean_root"] for e in entries)
        missing = []
        if args.lean_backend == "docker":
            print(f"\nValidating Lean repos in container '{args.docker_container}'...")
            for repo in sorted(required_repos):
                container_repo = f"/workspace/lean_repos/{repo}"
                result = _sp.run(
                    ["docker", "exec", args.docker_container, "test", "-d", f"{container_repo}/.lake"],
                    capture_output=True
                )
                if result.returncode != 0:
                    missing.append(f"  {repo}: .lake/ not found in container")
        else:
            print(f"\nValidating Lean repos in: {args.lean_src_dir}")
            for repo in sorted(required_repos):
                repo_path = args.lean_src_dir / repo
                if not repo_path.exists():
                    missing.append(f"  {repo}: directory not found")
                elif not (repo_path / ".lake").exists():
                    missing.append(f"  {repo}: .lake/ not found (not built)")
        if missing:
            print("ERROR: The following repos are missing or not built:")
            for m in missing:
                print(m)
            print(f"\nRun setup_repos.sh or use the Docker image to build repos.")
            return 1
        print(f"  All {len(required_repos)} required repos validated.")

    # Create model configuration
    model_config = create_model_config(args)
    model_config["run_name"] = run_name
    model_config["num_fixes"] = 3

    use_cache = not args.refresh_cache

    # Load cache and filter entries
    if use_cache:
        print("\nChecking cache for previously evaluated tasks...")
        full_cache = load_cache(args.model_id, args.mode)
    else:
        print("\nRefresh cache enabled: all tasks will be re-evaluated.")
        full_cache = {}

    valid_theorems = set(
        (e.get("thm_name"), e.get("lean_root"), e.get("rel_path"))
        for e in entries
        if e.get("thm_name") and e.get("lean_root") and e.get("rel_path")
    )

    cache = {key: entry for key, entry in full_cache.items() if key in valid_theorems} if use_cache else {}

    entries_to_evaluate = []
    cached_results = []

    for entry in entries:
        thm_name = entry.get("thm_name")
        lean_root = entry.get("lean_root")
        rel_path = entry.get("rel_path")

        if not thm_name or not lean_root or not rel_path:
            entries_to_evaluate.append(entry)
            continue

        cache_key = (thm_name, lean_root, rel_path)

        if use_cache and cache_key in cache and check_cache_match(cache[cache_key], model_config):
            cached_entry = cache[cache_key]
            task_id = entry.get("id", "N/A")
            print(f"  Using cached result for task {task_id} ({thm_name})")

            cached_result = {
                "thm_name": cached_entry["thm_name"],
                "lean_root": cached_entry["lean_root"],
                "rel_path": cached_entry["rel_path"],
                "success": cached_entry["success"],
                "fix_success": cached_entry["fix_success"],
                "cached": True,
                "cached_run_name": cached_entry["run_name"]
            }
            cached_results.append(cached_result)
        else:
            entries_to_evaluate.append(entry)

    print(f"\nCache summary:")
    print(f"  Total entries: {len(entries)}")
    print(f"  Cached (skipped): {len(cached_results)}")
    print(f"  To evaluate: {len(entries_to_evaluate)}")

    # Initialize evaluator
    if len(entries_to_evaluate) > 0:
        print("\nInitializing evaluator...")
        debug_output_dir = args.output_dir / run_name / "debug_lean" if args.save_debug_lean else None
        try:
            docker_container = args.docker_container if args.lean_backend == "docker" else None
            evaluator_instance = BenchmarkEvaluator(
                locator_data_dir=args.locator_data_dir,
                context_data_dir=args.locator_data_dir,  # not used in release
                lean_src_dir=args.lean_src_dir,
                prompts_dir=args.prompts_dir,
                output_dir=args.output_dir,
                model_config=model_config,
                fix_enabled=args.fix_enabled,
                max_fix_workers=args.max_fix_workers,
                log_file=args.log_file,
                debug_output_dir=debug_output_dir,
                docker_container=docker_container
            )
        except Exception as e:
            print(f"ERROR: Failed to initialize evaluator: {e}")
            import traceback
            traceback.print_exc()
            return 1

        # Run evaluation
        print(f"\nStarting evaluation on {len(entries_to_evaluate)} entries...")

        incremental_save_dir = args.output_dir / run_name
        incremental_save_dir.mkdir(parents=True, exist_ok=True)
        print(f"Results will be saved incrementally to: {incremental_save_dir}")

        try:
            summary, new_results = evaluator_instance.evaluate_full_benchmark(
                entries=entries_to_evaluate,
                use_retrieval=False,
                retrieve_top_k=0,
                max_workers=args.max_workers,
                incremental_save_dir=incremental_save_dir
            )
        except Exception as e:
            print(f"\nERROR: Evaluation failed: {e}")
            import traceback
            traceback.print_exc()
            return 1

        # Save new results to cache
        print("\nSaving results to cache...")
        for entry, result in zip(entries_to_evaluate, new_results):
            task_id = entry.get("id")
            if task_id is not None:
                save_to_cache(
                    model_id=args.model_id,
                    task_id=task_id,
                    thm_name=result["thm_name"],
                    lean_root=result["lean_root"],
                    rel_path=result["rel_path"],
                    model_config=model_config,
                    run_name=run_name,
                    success=result["success"],
                    fix_success=result.get("fix_success", False),
                    mode=args.mode
                )

        results = cached_results + new_results

        total = len(results)
        proved_wo_fix = sum(1 for r in results if r["success"])
        proved_w_fix = sum(1 for r in results if r["success"] or r.get("fix_success", False))

        summary = {
            "total_theorems": total,
            "theorems_proved_wo_fix": proved_wo_fix,
            "theorems_proved_w_fix": proved_w_fix,
            "proof_success_rate_wo_fix": proved_wo_fix / total if total > 0 else 0.0,
            "proof_success_rate_w_fix": proved_w_fix / total if total > 0 else 0.0,
            "cached_results": len(cached_results),
            "new_results": len(new_results)
        }
    else:
        print("\nAll entries found in cache, no evaluation needed!")
        results = cached_results

        total = len(results)
        proved_wo_fix = sum(1 for r in results if r["success"])
        proved_w_fix = sum(1 for r in results if r["success"] or r.get("fix_success", False))

        summary = {
            "total_theorems": total,
            "theorems_proved_wo_fix": proved_wo_fix,
            "theorems_proved_w_fix": proved_w_fix,
            "proof_success_rate_wo_fix": proved_wo_fix / total if total > 0 else 0.0,
            "proof_success_rate_w_fix": proved_w_fix / total if total > 0 else 0.0,
            "cached_results": len(cached_results),
            "new_results": 0
        }

    # Save final summary
    output_dir = args.output_dir / run_name
    output_dir.mkdir(parents=True, exist_ok=True)
    print(f"\nSaving final summary to: {output_dir}")
    try:
        summary_file = output_dir / "summary.json"
        utils.save_json(summary, summary_file)

        details_dir = output_dir / "details"
        details_dir.mkdir(parents=True, exist_ok=True)
        cached_saved = 0
        for result in results:
            if result.get("cached", False):
                thm_name = result["thm_name"]
                safe_name = thm_name.replace("/", "_").replace("\\", "_")
                rel_path = result.get("rel_path", "")
                file_stem = Path(rel_path).stem if rel_path else ""
                if file_stem:
                    detail_file = details_dir / f"{safe_name}__{file_stem}.json"
                else:
                    detail_file = details_dir / f"{safe_name}.json"
                if not detail_file.exists():
                    utils.save_json(result, detail_file)
                    cached_saved += 1

        print(f"Summary saved. {cached_saved} cached results added to details.")
    except Exception as e:
        print(f"ERROR: Failed to save results: {e}")
        return 1

    # Print summary
    print(f"\n{'='*60}")
    print("Evaluation Complete!")
    print(f"{'='*60}")
    print(f"Total entries evaluated: {len(results)}")
    print(f"Results saved to: {output_dir}")

    if results and isinstance(results, list):
        successes = sum(1 for r in results if r.get("success", False))
        fix_successes = sum(1 for r in results if r.get("fix_success", False))
        print(f"Success rate w/o fix: {successes}/{len(results)} ({100*successes/len(results):.1f}%)")
        print(f"Success rate w fix: {fix_successes}/{len(results)} ({100*fix_successes/len(results):.1f}%)")

    return 0


if __name__ == "__main__":
    sys.exit(main())
