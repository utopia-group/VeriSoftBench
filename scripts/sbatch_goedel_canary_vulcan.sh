#!/bin/bash
#SBATCH --job-name=goedel-canary
#SBATCH --output=%x-%j.out
#SBATCH --error=%x-%j.err
#SBATCH --partition=gpubase_bygpu_b1
#SBATCH --account=aip-qchen
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --gres=gpu:l40s:1
#SBATCH --mem=48G
#SBATCH --time=02:00:00

# ============================================================================
# Goedel-Code-Prover-8B Canary Job — VeriSoftBench Inference Only (Vulcan)
# ============================================================================

set -euo pipefail

export VLLM_WORKER_MULTIPROC_METHOD=spawn

WORK_DIR="/scratch/qchen/verisoftbench-goedel"
MODEL_ID="Goedel-LM/Goedel-Code-Prover-8B"
VLLM_PORT=8000
RESULTS_DIR="${WORK_DIR}/results"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_FILE="${RESULTS_DIR}/canary_${TIMESTAMP}.jsonl"

mkdir -p "${WORK_DIR}" "${RESULTS_DIR}"

echo "============================================"
echo "Goedel-Code-Prover-8B Canary — VeriSoftBench"
echo "Node: $(hostname)"
echo "Date: $(date)"
echo "Arch: $(uname -m)"
echo "GPU: $(nvidia-smi --query-gpu=name --format=csv,noheader 2>/dev/null || echo unknown)"
echo "Work dir: ${WORK_DIR}"
echo "Output: ${OUTPUT_FILE}"
echo "============================================"

# --- Step 1: Set up Python environment ---
echo "[1/4] Setting up Python environment..."

if [ ! -d "${WORK_DIR}/venv" ]; then
    python3 -m venv "${WORK_DIR}/venv"
fi
source "${WORK_DIR}/venv/bin/activate"

pip install --quiet vllm openai

# --- Step 2: Check VeriSoftBench ---
echo "[2/4] Checking VeriSoftBench..."

if [ ! -d "${WORK_DIR}/VeriSoftBench" ]; then
    echo "ERROR: VeriSoftBench not found at ${WORK_DIR}/VeriSoftBench"
    exit 1
fi

cd "${WORK_DIR}/VeriSoftBench"

# --- Step 3: Start vLLM server ---
echo "[3/4] Starting vLLM server..."

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

echo "Waiting for vLLM server..."
for i in $(seq 1 120); do
    if curl -s http://localhost:${VLLM_PORT}/health > /dev/null 2>&1; then
        echo "vLLM server ready after $((i * 5))s"
        break
    fi
    if ! kill -0 ${VLLM_PID} 2>/dev/null; then
        echo "ERROR: vLLM server died. Check stderr."
        exit 1
    fi
    sleep 5
done

if ! curl -s http://localhost:${VLLM_PORT}/health > /dev/null 2>&1; then
    echo "ERROR: vLLM server not ready after 600s"
    kill ${VLLM_PID} 2>/dev/null || true
    exit 1
fi

# --- Step 4: Run inference ---
echo "[4/4] Running canary inference (20 theorems, stratified)..."

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

kill ${VLLM_PID} 2>/dev/null || true
wait ${VLLM_PID} 2>/dev/null || true
