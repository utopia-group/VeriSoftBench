#!/bin/bash
# Live verification: polls Vulcan for new inference results and verifies locally.
# Usage: ./scripts/goedel_live_verify.sh <remote_jsonl_path> <local_output> [poll_interval_sec]
#
# Example:
#   ./scripts/goedel_live_verify.sh \
#     /scratch/qchen/verisoftbench-goedel/results/pass8_run.jsonl \
#     results/pass8_verified.jsonl \
#     30

set -euo pipefail

REMOTE_FILE="${1:?Usage: $0 <remote_jsonl> <local_verified_output> [poll_sec]}"
LOCAL_OUTPUT="${2:?Usage: $0 <remote_jsonl> <local_verified_output> [poll_sec]}"
POLL_SEC="${3:-30}"
CLUSTER="${4:-vulcan}"
LOCAL_INFERENCE="results/.live_inference_cache.jsonl"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_DIR"

echo "=== Live Verify ==="
echo "  Remote: ${CLUSTER}:${REMOTE_FILE}"
echo "  Output: ${LOCAL_OUTPUT}"
echo "  Poll every: ${POLL_SEC}s"
echo ""

PREV_LINES=0

while true; do
    # Download latest inference results
    raca ssh "$CLUSTER" "cat ${REMOTE_FILE} 2>/dev/null" 2>&1 \
        | grep -v '^\[2;' > "$LOCAL_INFERENCE" 2>/dev/null || true

    CUR_LINES=$(wc -l < "$LOCAL_INFERENCE" 2>/dev/null || echo 0)

    if [ "$CUR_LINES" -gt "$PREV_LINES" ]; then
        NEW=$((CUR_LINES - PREV_LINES))
        echo "[$(date +%H:%M:%S)] ${NEW} new theorem(s) (total: ${CUR_LINES}). Verifying..."

        python3 scripts/goedel_verify.py \
            --input "$LOCAL_INFERENCE" \
            --output "$LOCAL_OUTPUT" \
            --lean-backend docker \
            --docker-container verisoftbench-test \
            --save-every 1 \
            2>&1 | grep -E 'PROVED|CHECKPOINT|complete'

        # Show running totals
        if [ -f "$LOCAL_OUTPUT" ]; then
            python3 -c "
import json
results = [json.loads(l) for l in open('${LOCAL_OUTPUT}') if l.strip()]
proved = sum(1 for r in results if r['success'])
total = len(results)
pct = proved/total*100 if total else 0
print(f'  -> {proved}/{total} proved ({pct:.1f}%) pass@k so far')
"
        fi

        PREV_LINES=$CUR_LINES
    fi

    # Check if job is still running
    JOB_DONE=$(raca ssh "$CLUSTER" "[ -f ${REMOTE_FILE} ] && [ \$(wc -l < ${REMOTE_FILE}) -eq ${CUR_LINES} ] && ! squeue -u \$(whoami) --name=goedel-pass8 -h 2>/dev/null | grep -q . && echo DONE || echo RUNNING" 2>&1 | grep -o 'DONE\|RUNNING' | tail -1)

    if [ "$JOB_DONE" = "DONE" ] && [ "$CUR_LINES" -gt 0 ]; then
        echo ""
        echo "[$(date +%H:%M:%S)] Job complete. Final results:"
        python3 -c "
import json
results = [json.loads(l) for l in open('${LOCAL_OUTPUT}') if l.strip()]
proved = sum(1 for r in results if r['success'])
total = len(results)
pct = proved/total*100 if total else 0
print(f'  {proved}/{total} theorems proved ({pct:.1f}%)')
for r in results:
    n_s = len(r['samples'])
    n_p = sum(1 for s in r['samples'] if s.get('compilation_success'))
    status = 'PASS' if r['success'] else 'FAIL'
    print(f'  {status:4s} {r[\"lean_root\"]:22s} {r[\"thm_name\"][:40]:40s} {n_p}/{n_s}')
"
        break
    fi

    sleep "$POLL_SEC"
done
