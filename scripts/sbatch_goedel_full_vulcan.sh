#!/bin/bash
#SBATCH --job-name=goedel-full
#SBATCH --output=%x-%j.out
#SBATCH --error=%x-%j.err
#SBATCH --account=aip-qchen
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --gres=gpu:l40s:1
#SBATCH --mem=48G
#SBATCH --time=02:50:00

# ============================================================================
# Goedel-Code-Prover-8B Full Run — VeriSoftBench (Vulcan)
#
# Fully self-contained and resumable. Submit repeatedly until all 500 done.
# The inference script auto-skips completed theorems via output JSONL.
#
# Usage:
#   sbatch scripts/sbatch_goedel_full_vulcan.sh
#   # Check progress:
#   wc -l $SCRATCH/verisoftbench-goedel/results/goedel_full_pass8.jsonl
#   # Resubmit if not all 500 done:
#   sbatch scripts/sbatch_goedel_full_vulcan.sh
# ============================================================================

set -euo pipefail
export VLLM_WORKER_MULTIPROC_METHOD=spawn

WORK_DIR="/scratch/qchen/verisoftbench-goedel"
PROJECT_DIR="/project/aip-qchen/qchen/verisoftbench-goedel"
MODEL_ID="Goedel-LM/Goedel-Code-Prover-8B"
VLLM_PORT=8000
# Results go to persistent project storage; scratch is working space only
OUTPUT_FILE="${PROJECT_DIR}/results/goedel_full_pass8.jsonl"

mkdir -p "${WORK_DIR}/results" "${PROJECT_DIR}/results"

DONE=$(wc -l < "${OUTPUT_FILE}" 2>/dev/null || echo 0)
echo "============================================"
echo "Goedel-Code-Prover-8B Full Run — VeriSoftBench"
echo "Node: $(hostname)"
echo "GPU: $(nvidia-smi --query-gpu=name --format=csv,noheader 2>/dev/null)"
echo "Previously completed: ${DONE}/500 theorems"
echo "Output: ${OUTPUT_FILE}"
echo "============================================"

if [ "${DONE}" -ge 500 ]; then
    echo "All 500 theorems already complete!"
    exit 0
fi

# --- Setup ---
source "${WORK_DIR}/venv/bin/activate"
cd "${WORK_DIR}/VeriSoftBench"

# --- Start vLLM ---
python -m vllm.entrypoints.openai.api_server \
    --model "${MODEL_ID}" --port ${VLLM_PORT} --dtype bfloat16 \
    --max-model-len 32768 --gpu-memory-utilization 0.90 \
    --download-dir "${WORK_DIR}/models" &
VLLM_PID=$!

for i in $(seq 1 120); do
    curl -s http://localhost:${VLLM_PORT}/health > /dev/null 2>&1 && break
    kill -0 ${VLLM_PID} 2>/dev/null || { echo "ERROR: vLLM died"; exit 1; }
    sleep 5
done
curl -s http://localhost:${VLLM_PORT}/health > /dev/null 2>&1 || { echo "ERROR: timeout"; exit 1; }
echo "vLLM ready"

# --- Run inference (resumes from existing output) ---
# 2h50m walltime, ~2m vLLM startup = ~2h48m for inference
# At ~3min/theorem with pass@8, expect ~55 theorems per job
python scripts/goedel_inference.py \
    --base-url "http://localhost:${VLLM_PORT}/v1" \
    --model-id "${MODEL_ID}" \
    --output "${OUTPUT_FILE}" \
    --temperature 0.6 --max-tokens 24576 \
    --model-context-length 32768 --frequency-penalty 0.1 \
    --num-samples 8 \
    --save-every 5

FINAL=$(wc -l < "${OUTPUT_FILE}" 2>/dev/null || echo 0)
echo ""
echo "============================================"
echo "Job complete. ${FINAL}/500 theorems done."
if [ "${FINAL}" -lt 500 ]; then
    echo "Resubmit to continue: sbatch scripts/sbatch_goedel_full_vulcan.sh"
fi
echo "============================================"

kill ${VLLM_PID} 2>/dev/null || true
wait ${VLLM_PID} 2>/dev/null || true

# Backup to scratch as well
cp "${OUTPUT_FILE}" "${WORK_DIR}/results/goedel_full_pass8.jsonl" 2>/dev/null || true
