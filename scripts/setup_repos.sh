#!/usr/bin/env bash
#
# setup_repos.sh — Build all Lean repositories for VeriSoftBench evaluation.
#
# Usage (clone from GitHub — recommended for release users):
#   ./setup_repos.sh --clone --config-dir <path> --output-dir <path> [options]
#
# Usage (local source — for developers with pre-cloned repos):
#   ./setup_repos.sh --source-dir <path> --config-dir <path> --output-dir <path> [options]
#
# Required arguments:
#   --config-dir  — Directory containing build configs (e.g., build_config)
#   --output-dir  — Target directory for built repos (e.g., data/lean_repos)
#
# Source (one of):
#   --clone       — Clone repos from GitHub at pinned commits (uses repos.json)
#   --source-dir  — Directory containing pre-cloned repo source code
#
# Options:
#   --repos       — Comma-separated list of specific repos to build (default: all)
#   --skip-if-built  — Skip repos that already have .lake/ directory
#   --no-mathlib  — Only build repos without mathlib dependency (fast)
#   --mathlib-only — Only build repos with mathlib dependency
#   --help        — Show this help message
#
# Examples:
#   # Clone and build all repos (recommended)
#   ./setup_repos.sh \
#     --clone \
#     --config-dir build_config \
#     --output-dir data/lean_repos
#
#   # Clone and build only non-mathlib repos (quick start)
#   ./setup_repos.sh \
#     --clone \
#     --config-dir build_config \
#     --output-dir data/lean_repos \
#     --no-mathlib
#
#   # Build from local source (developer mode)
#   ./setup_repos.sh \
#     --source-dir ../BuildScripts/LeanSrc \
#     --config-dir ../BuildScripts/build_config \
#     --output-dir data/lean_repos
#
#   # Resume a partial build (skip already-built repos)
#   ./setup_repos.sh \
#     --clone \
#     --config-dir build_config \
#     --output-dir data/lean_repos \
#     --skip-if-built
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPOS_JSON="${SCRIPT_DIR}/../repos.json"
BUILD_REPO_SCRIPT="${SCRIPT_DIR}/build_repo.sh"

# --- Defaults ---
SOURCE_DIR=""
CONFIG_DIR=""
OUTPUT_DIR=""
CLONE_MODE=false
SELECTED_REPOS=""
SKIP_IF_BUILT=false
NO_MATHLIB=false
MATHLIB_ONLY=false

# --- Argument parsing ---
show_help() {
    head -50 "$0" | tail -48 | sed 's/^# \?//'
    exit 0
}

while [ "$#" -gt 0 ]; do
    case "$1" in
        --source-dir)  SOURCE_DIR="$2"; shift 2 ;;
        --config-dir)  CONFIG_DIR="$2"; shift 2 ;;
        --output-dir)  OUTPUT_DIR="$2"; shift 2 ;;
        --clone)       CLONE_MODE=true; shift ;;
        --repos)       SELECTED_REPOS="$2"; shift 2 ;;
        --skip-if-built) SKIP_IF_BUILT=true; shift ;;
        --no-mathlib)  NO_MATHLIB=true; shift ;;
        --mathlib-only) MATHLIB_ONLY=true; shift ;;
        --help|-h)     show_help ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

# Validate required args
if [ -z "${CONFIG_DIR}" ] || [ -z "${OUTPUT_DIR}" ]; then
    echo "ERROR: --config-dir and --output-dir are required"
    echo "Run with --help for usage information"
    exit 1
fi

if [ "${CLONE_MODE}" = false ] && [ -z "${SOURCE_DIR}" ]; then
    echo "ERROR: Either --clone or --source-dir is required"
    echo "Run with --help for usage information"
    exit 1
fi

if [ ! -f "${REPOS_JSON}" ]; then
    echo "ERROR: repos.json not found at ${REPOS_JSON}"
    echo "Run generate_repos_manifest.py first"
    exit 1
fi

if [ ! -f "${BUILD_REPO_SCRIPT}" ]; then
    echo "ERROR: build_repo.sh not found at ${BUILD_REPO_SCRIPT}"
    exit 1
fi

# --- Check for required tools ---
if ! command -v python3 &> /dev/null; then
    echo "ERROR: python3 is required (for JSON parsing)"
    exit 1
fi

if ! command -v lake &> /dev/null && ! command -v elan &> /dev/null; then
    echo "WARNING: Neither lake nor elan found in PATH."
    echo "Install elan: curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh"
fi

if [ "${CLONE_MODE}" = true ] && ! command -v git &> /dev/null; then
    echo "ERROR: git is required for --clone mode"
    exit 1
fi

# --- Parse repos.json to get repo list ---
echo "Reading repository manifest from ${REPOS_JSON}..."

# Extract repo list with mathlib status using Python
REPO_LIST=$(python3 -c "
import json, sys
with open('${REPOS_JSON}') as f:
    data = json.load(f)
for name, info in sorted(data['repos'].items()):
    print(f'{name}:{\"mathlib\" if info.get(\"has_mathlib\") else \"no_mathlib\"}')
")

# --- Filter repos ---
REPOS_TO_BUILD=()
while IFS=: read -r repo_name mathlib_status; do
    # Filter by selected repos
    if [ -n "${SELECTED_REPOS}" ]; then
        if ! echo ",${SELECTED_REPOS}," | grep -q ",${repo_name},"; then
            continue
        fi
    fi

    # Filter by mathlib status
    if [ "${NO_MATHLIB}" = true ] && [ "${mathlib_status}" = "mathlib" ]; then
        continue
    fi
    if [ "${MATHLIB_ONLY}" = true ] && [ "${mathlib_status}" = "no_mathlib" ]; then
        continue
    fi

    REPOS_TO_BUILD+=("${repo_name}:${mathlib_status}")
done <<< "${REPO_LIST}"

TOTAL=${#REPOS_TO_BUILD[@]}

# Determine source mode label
if [ "${CLONE_MODE}" = true ]; then
    SOURCE_LABEL="GitHub (clone at pinned commits)"
else
    SOURCE_LABEL="${SOURCE_DIR}"
fi

echo ""
echo "========================================"
echo "VeriSoftBench Repository Setup"
echo "========================================"
echo "Source:  ${SOURCE_LABEL}"
echo "Config:  ${CONFIG_DIR}"
echo "Output:  ${OUTPUT_DIR}"
echo "Repos:   ${TOTAL}"
echo "========================================"
echo ""

mkdir -p "${OUTPUT_DIR}"

# --- Build repos (non-mathlib first, then mathlib) ---
SUCCEEDED=0
FAILED=0
SKIPPED=0
FAILED_REPOS=()

# Sort: no_mathlib first
NO_MATHLIB_REPOS=()
MATHLIB_REPOS=()
for entry in "${REPOS_TO_BUILD[@]}"; do
    repo_name="${entry%%:*}"
    status="${entry##*:}"
    if [ "${status}" = "no_mathlib" ]; then
        NO_MATHLIB_REPOS+=("${repo_name}")
    else
        MATHLIB_REPOS+=("${repo_name}")
    fi
done

ORDERED_REPOS=("${NO_MATHLIB_REPOS[@]}" "${MATHLIB_REPOS[@]}")

# Determine source arg for build_repo.sh
if [ "${CLONE_MODE}" = true ]; then
    BUILD_SOURCE_ARG="--clone"
else
    BUILD_SOURCE_ARG="${SOURCE_DIR}"
fi

CURRENT=0
for repo_name in "${ORDERED_REPOS[@]}"; do
    CURRENT=$((CURRENT + 1))
    echo "[${CURRENT}/${TOTAL}] Building ${repo_name}..."

    BUILD_ARGS=("${repo_name}" "${BUILD_SOURCE_ARG}" "${CONFIG_DIR}" "${OUTPUT_DIR}")
    if [ "${SKIP_IF_BUILT}" = true ]; then
        BUILD_ARGS+=("--skip-if-built")
    fi

    if bash "${BUILD_REPO_SCRIPT}" "${BUILD_ARGS[@]}"; then
        # Check if it was actually skipped
        if [ "${SKIP_IF_BUILT}" = true ] && [ -d "${OUTPUT_DIR}/${repo_name}/.lake" ]; then
            # Was already built before we started
            SKIPPED=$((SKIPPED + 1))
        fi
        SUCCEEDED=$((SUCCEEDED + 1))
    else
        echo "FAILED: ${repo_name}"
        FAILED=$((FAILED + 1))
        FAILED_REPOS+=("${repo_name}")
    fi
done

# --- Summary ---
echo ""
echo "========================================"
echo "Build Summary"
echo "========================================"
echo "Total:     ${TOTAL}"
echo "Succeeded: ${SUCCEEDED}"
echo "Failed:    ${FAILED}"
if [ "${SKIP_IF_BUILT}" = true ]; then
    echo "Skipped:   ${SKIPPED} (already built)"
fi

if [ ${FAILED} -gt 0 ]; then
    echo ""
    echo "Failed repos:"
    for r in "${FAILED_REPOS[@]}"; do
        echo "  - ${r}"
    done
    echo ""
    echo "Re-run with --skip-if-built to retry only failed repos."
    exit 1
fi

echo ""
echo "All repos built successfully!"

# --- Validate ---
echo ""
echo "Validating builds..."
VALID=0
INVALID=0
for entry in "${REPOS_TO_BUILD[@]}"; do
    repo_name="${entry%%:*}"
    if [ -d "${OUTPUT_DIR}/${repo_name}/.lake" ]; then
        VALID=$((VALID + 1))
    else
        echo "  MISSING .lake/ for: ${repo_name}"
        INVALID=$((INVALID + 1))
    fi
done
echo "Validation: ${VALID}/${TOTAL} repos have .lake/ directory"

if [ ${INVALID} -gt 0 ]; then
    echo "WARNING: ${INVALID} repos missing .lake/ directory"
    exit 1
fi

# --- Apply post-build patches ---
PATCH_SCRIPT="${SCRIPT_DIR}/docker_repo_patches.sh"
if [ -f "${PATCH_SCRIPT}" ]; then
    echo ""
    echo "Applying post-build patches..."
    bash "${PATCH_SCRIPT}" --repos-dir "${OUTPUT_DIR}" --config-dir "${CONFIG_DIR}"
fi

echo "Done!"
