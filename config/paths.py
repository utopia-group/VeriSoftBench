"""
Centralized path configuration for the VeriSoftBench evaluation pipeline.

All paths are defined relative to the project root directory.
Environment variable VERISOFTBENCH_LEAN_SRC overrides the default lean_repos path.
"""

import os
from pathlib import Path

# Project root directory (2 levels up from this file: config/paths.py -> release/)
PROJECT_ROOT = Path(__file__).parent.parent

# Docker default path for lean repos
DOCKER_LEAN_SRC_DIR = Path("/workspace/lean_repos")

# Data directories
DATA_DIR = PROJECT_ROOT / "data"
EVAL_INPUT_DIR = DATA_DIR  # verisoftbench.jsonl lives directly in data/
LEAN_SRC_DIR = DATA_DIR / "lean_repos"
REPO_INDEX_DIR = DATA_DIR / "repo_index"
FULL_CONTEXT_DIR = DATA_DIR / "full_context"

# Prompts directory
PROMPTS_DIR = PROJECT_ROOT / "prompts" / "templates"
FULL_LIMITED_PROMPTS_DIR = PROJECT_ROOT / "prompts" / "full_limited"

# Results directory
RESULTS_DIR = PROJECT_ROOT / "results"
RESULTS_DATA_DIR = RESULTS_DIR / "data"
RESULTS_CACHE_DIR = RESULTS_DIR / "cache"

# Config directory
CONFIGS_DIR = PROJECT_ROOT / "configs"

# Debug directories
DEBUG_DIR = PROJECT_ROOT / "debug"
DEBUG_PROMPTS_DIR = DEBUG_DIR / "prompts"
DEBUG_LLM_OUTPUT_DIR = DEBUG_DIR / "llm_output"


def get_lean_src_dir() -> Path:
    """Get the Lean source directory, respecting VERISOFTBENCH_LEAN_SRC env var."""
    env_path = os.environ.get("VERISOFTBENCH_LEAN_SRC")
    if env_path:
        return Path(env_path)
    return LEAN_SRC_DIR


def get_lean_repo_path(repo_name: str) -> Path:
    """Get the path to a specific Lean repository."""
    return get_lean_src_dir() / repo_name


def get_result_dir(run_name: str) -> Path:
    """Get the results directory for a specific run."""
    return RESULTS_DATA_DIR / run_name


def get_debug_prompt_dir(run_name: str) -> Path:
    """Get the debug prompt directory for a specific run."""
    return DEBUG_PROMPTS_DIR / run_name


def get_debug_output_dir(run_name: str) -> Path:
    """Get the debug LLM output directory for a specific run."""
    return DEBUG_LLM_OUTPUT_DIR / run_name
