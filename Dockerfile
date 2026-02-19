# VeriSoftBench Lean Proof Environment
#
# Pre-built Lean repositories for proof verification.
# This image contains ONLY the Lean toolchains and compiled repos —
# the evaluation pipeline runs locally on the host.
#
# Build (from the repository root):
#   docker build -t verisoftbench/lean:latest .
#
# Start the container (keep running for docker exec):
#   docker run -d --name verisoftbench-test verisoftbench/lean:latest
#
# The eval pipeline uses --lean-backend docker to invoke:
#   docker exec verisoftbench-test lake build <module> ...
#
# Build time: ~1 hour (mathlib cache downloads dominate)
# Image size: ~110 GB
#
# Alternative: build repos locally without Docker:
#   ./scripts/setup_repos.sh --clone --config-dir build_config --output-dir data/lean_repos
#   python evaluate.py --lean-backend local --lean-src-dir data/lean_repos ...

FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive
ENV LANG=C.UTF-8

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    git \
    ca-certificates \
    python3 \
    g++ \
    make \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /workspace

# Copy build infrastructure
COPY repos.json /workspace/repos.json
COPY scripts/build_repo.sh /workspace/scripts/build_repo.sh
RUN chmod +x /workspace/scripts/build_repo.sh
COPY build_config/ /workspace/build_config/
COPY THIRD_PARTY_NOTICES.txt /workspace/THIRD_PARTY_NOTICES.txt

# ---- Build ALL repos in a single layer ----
# All repos are built in one RUN to avoid Docker layer accumulation.
RUN set -e; \
    B="/workspace/scripts/build_repo.sh"; \
    CFG="/workspace/build_config"; \
    OUT="/workspace/lean_repos"; \
    \
    echo "==== Non-mathlib repos ===="; \
    $B IntroEffects                   --clone $CFG $OUT; \
    $B iris-lean                      --clone $CFG $OUT; \
    $B lean-hoare                     --clone $CFG $OUT; \
    $B LeanExprEvaluator              --clone $CFG $OUT; \
    $B Lentil                         --clone $CFG $OUT; \
    $B LeroyCompilerVerificationCourse --clone $CFG $OUT; \
    $B verified-compiler              --clone $CFG $OUT; \
    \
    echo "==== Mathlib-dependent repos ===="; \
    $B CvxLean                        --clone $CFG $OUT; \
    $B pcf-lean                       --clone $CFG $OUT; \
    $B lean-formal-reasoning-program  --clone $CFG $OUT; \
    $B wadray_verification            --clone $CFG $OUT; \
    $B formal-snarks-project          --clone $CFG $OUT \
      || echo "WARNING: formal-snarks-project build failed (known issues)"; \
    $B splean                         --clone $CFG $OUT; \
    $B TTBFL                          --clone $CFG $OUT; \
    $B FVIntmax                       --clone $CFG $OUT; \
    $B juvix-lean                     --clone $CFG $OUT; \
    $B capless-lean                   --clone $CFG $OUT; \
    $B ArkLib                         --clone $CFG $OUT; \
    $B loom                           --clone $CFG $OUT \
      || echo "WARNING: loom build had partial failures (known issue)"; \
    $B clean                          --clone $CFG $OUT \
      || echo "WARNING: clean build had partial failures"; \
    $B veil                           --clone $CFG $OUT \
      || echo "WARNING: veil build had partial failures"; \
    $B VCV-io                         --clone $CFG $OUT \
      || echo "WARNING: VCV-io build had partial failures"; \
    $B lean-mlir                      --clone $CFG $OUT \
      || echo "WARNING: lean-mlir build had partial failures"; \
    \
    echo "==== Collecting licenses ===="; \
    mkdir -p /workspace/THIRD_PARTY_LICENSES; \
    for repo_dir in $OUT/*/; do \
        repo_name=$(basename "$repo_dir"); \
        for lf in LICENSE LICENSE.md LICENSE.txt COPYING COPYING.md; do \
            if [ -f "$repo_dir/$lf" ]; then \
                cp "$repo_dir/$lf" "/workspace/THIRD_PARTY_LICENSES/${repo_name}_${lf}"; \
            fi; \
        done; \
    done; \
    \
    echo "==== Build complete ===="

# ---- Apply post-build patches ----
# Fix API changes, add missing files, and build additional modules
# needed for ground-truth proof verification.
COPY scripts/docker_repo_patches.sh /workspace/scripts/docker_repo_patches.sh
RUN chmod +x /workspace/scripts/docker_repo_patches.sh && \
    /workspace/scripts/docker_repo_patches.sh \
        --repos-dir /workspace/lean_repos \
        --config-dir /workspace/build_config

# ---- Generate repository index ----
COPY scripts/generate_repo_index.py /workspace/scripts/generate_repo_index.py
COPY scripts/chunking/ /workspace/scripts/chunking/
RUN python3 /workspace/scripts/generate_repo_index.py \
    --repos-dir /workspace/lean_repos \
    --output-dir /workspace/repo_index

WORKDIR /workspace/lean_repos

# Keep container alive for `docker exec` calls from the host eval pipeline.
CMD ["sleep", "infinity"]
