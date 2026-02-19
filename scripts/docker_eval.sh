#!/usr/bin/env bash
#
# docker_eval.sh — Run VeriSoftBench evaluation using Docker for Lean compilation.
#
# This script:
#   1. Starts the verisoftbench-lean Docker container (if not running)
#   2. Runs the eval pipeline locally with --lean-backend docker
#
# Usage:
#   ./docker_eval.sh [evaluate.py arguments...]
#
# Examples:
#   # Run with default config
#   ./docker_eval.sh --config configs/default.yaml
#
#   # Run specific tasks with Claude
#   ./docker_eval.sh --config configs/claude_example.yaml --task-ids 1:10
#
# Prerequisites:
#   - Docker installed and running
#   - verisoftbench/lean:latest image built (see Dockerfile)
#   - Python 3 with requirements.txt installed locally
#
# Environment variables:
#   VERISOFTBENCH_IMAGE     — Docker image name (default: verisoftbench/lean:latest)
#   VERISOFTBENCH_CONTAINER — Container name (default: verisoftbench-lean)
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RELEASE_DIR="$(dirname "${SCRIPT_DIR}")"

IMAGE="${VERISOFTBENCH_IMAGE:-verisoftbench/lean:latest}"
CONTAINER="${VERISOFTBENCH_CONTAINER:-verisoftbench-lean}"

# --- Ensure container is running ---
if docker inspect -f '{{.State.Running}}' "${CONTAINER}" 2>/dev/null | grep -q true; then
    echo "Container '${CONTAINER}' is already running."
else
    echo "Starting container '${CONTAINER}'..."
    # Remove stopped container if it exists
    docker rm -f "${CONTAINER}" 2>/dev/null || true
    docker run -d --name "${CONTAINER}" "${IMAGE}"
    echo "Container started."
    # Brief pause to let it initialize
    sleep 1
fi

# --- Run eval pipeline locally with Docker backend ---
echo ""
echo "Running evaluation with Docker Lean backend..."
echo ""

cd "${RELEASE_DIR}"
python3 evaluate.py \
    --lean-backend docker \
    --docker-container "${CONTAINER}" \
    "$@"
