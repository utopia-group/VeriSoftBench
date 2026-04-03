#!/bin/bash
#SBATCH --job-name=goedel-canary
#SBATCH --output=%x-%j.out
#SBATCH --error=%x-%j.err
#SBATCH --partition=gh-dev
#SBATCH --account=ASC26006
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --time=02:00:00

# ============================================================================
# Goedel-Code-Prover-8B Canary Job — VeriSoftBench Inference Only
#
# Uses NGC PyTorch container via Apptainer (aarch64/GH200 needs pre-built
# CUDA+PyTorch — pip wheels don't exist for this platform).
# ============================================================================

# Load modules before set -u (module scripts have unbound variables)
module load tacc-apptainer
module load cuda/12.5

set -euo pipefail

# Directories
WORK_DIR="${WORK}/verisoftbench-goedel"
MODEL_ID="Goedel-LM/Goedel-Code-Prover-8B"
VLLM_PORT=8000
RESULTS_DIR="${WORK_DIR}/results"
SIF_PATH="${WORK_DIR}/pytorch_24.10-py3.sif"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_FILE="${RESULTS_DIR}/canary_${TIMESTAMP}.jsonl"

mkdir -p "${WORK_DIR}" "${RESULTS_DIR}"

echo "============================================"
echo "Goedel-Code-Prover-8B Canary — VeriSoftBench"
echo "Node: $(hostname)"
echo "Date: $(date)"
echo "Arch: $(uname -m)"
echo "Work dir: ${WORK_DIR}"
echo "Output: ${OUTPUT_FILE}"
echo "============================================"

# --- Step 1: Pull NGC container if needed ---
echo "[1/4] Setting up NGC container..."

if [ ! -f "${SIF_PATH}" ]; then
    echo "Pulling NGC PyTorch container (this takes ~10 min first time)..."
    apptainer pull "${SIF_PATH}" docker://nvcr.io/nvidia/pytorch:24.10-py3
fi
echo "Container ready: ${SIF_PATH}"

# --- Step 2: Install vLLM + openai inside container overlay ---
echo "[2/4] Installing vLLM in container..."

# Install vLLM to a separate directory — don't use --user to avoid
# polluting ~/.local and conflicting with the container's PyTorch
SITE_PACKAGES="${WORK_DIR}/site-packages"
mkdir -p "${SITE_PACKAGES}"

# Clean any previous conflicting user installs
rm -rf "${HOME}/.local/lib/python3.10/site-packages/torch"* 2>/dev/null || true

# Install vllm+deps to target dir, then remove torch/torchvision so the
# container's pre-built aarch64 CUDA torch is used instead
apptainer exec --nv \
    --bind "${WORK_DIR}:${WORK_DIR}" \
    --bind "${HOME}:${HOME}" \
    "${SIF_PATH}" \
    bash -c "
        pip install --quiet --target '${SITE_PACKAGES}' 'vllm==0.6.6.post1' openai 2>&1 | tail -5
        rm -rf '${SITE_PACKAGES}'/torch '${SITE_PACKAGES}'/torch-* \
               '${SITE_PACKAGES}'/torchvision '${SITE_PACKAGES}'/torchvision-* \
               '${SITE_PACKAGES}'/nvidia* '${SITE_PACKAGES}'/triton*
        echo 'Cleaned torch from target — using container torch'
    "

echo "vLLM installed to ${SITE_PACKAGES}"

# --- Step 3: Start vLLM server inside container ---
echo "[3/4] Starting vLLM server..."

if [ ! -d "${WORK_DIR}/VeriSoftBench" ]; then
    echo "ERROR: VeriSoftBench not found at ${WORK_DIR}/VeriSoftBench"
    exit 1
fi

apptainer exec --nv \
    --bind "${WORK_DIR}:${WORK_DIR}" \
    --bind "${HOME}:${HOME}" \
    --env "VLLM_WORKER_MULTIPROC_METHOD=spawn" \
    --env "HF_HOME=${WORK_DIR}/hf_cache" \
    --env "PYTHONPATH=${SITE_PACKAGES}" \
    "${SIF_PATH}" \
    python -m vllm.entrypoints.openai.api_server \
        --model "${MODEL_ID}" \
        --port ${VLLM_PORT} \
        --dtype bfloat16 \
        --max-model-len 32768 \
        --gpu-memory-utilization 0.90 \
        --download-dir "${WORK_DIR}/models" \
    &

VLLM_PID=$!
echo "vLLM PID: ${VLLM_PID}"

# Wait for server to be ready
echo "Waiting for vLLM server..."
for i in $(seq 1 120); do
    if curl -s http://localhost:${VLLM_PORT}/health > /dev/null 2>&1; then
        echo "vLLM server ready after $((i * 5))s"
        break
    fi
    if ! kill -0 ${VLLM_PID} 2>/dev/null; then
        echo "ERROR: vLLM server died. Check stderr for details."
        exit 1
    fi
    sleep 5
done

if ! curl -s http://localhost:${VLLM_PORT}/health > /dev/null 2>&1; then
    echo "ERROR: vLLM server not ready after 600s"
    kill ${VLLM_PID} 2>/dev/null || true
    exit 1
fi

# --- Step 4: Run inference (inside container for Python compatibility) ---
echo "[4/4] Running canary inference (20 theorems, stratified)..."

cd "${WORK_DIR}/VeriSoftBench"

apptainer exec --nv \
    --bind "${WORK_DIR}:${WORK_DIR}" \
    --bind "${HOME}:${HOME}" \
    --env "PYTHONPATH=${SITE_PACKAGES}" \
    "${SIF_PATH}" \
    python scripts/goedel_inference.py \
        --base-url "http://localhost:${VLLM_PORT}/v1" \
        --model-id "${MODEL_ID}" \
        --output "${OUTPUT_FILE}" \
        --data-dir data \
        --temperature 0.9 \
        --max-tokens 16384 \
        --num-samples 1 \
        --subset 20 \
        --save-every 5

echo ""
echo "============================================"
echo "Canary inference complete!"
echo "Results: ${OUTPUT_FILE}"
echo "Theorems processed: $(wc -l < ${OUTPUT_FILE})"
echo "============================================"

# Cleanup
kill ${VLLM_PID} 2>/dev/null || true
wait ${VLLM_PID} 2>/dev/null || true
