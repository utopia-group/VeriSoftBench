#!/bin/bash
# Repository Patches
# Apply post-build patches to fix API changes, add missing files, and build
# additional modules needed for ground-truth proof verification.
#
# Usage:
#   ./scripts/docker_repo_patches.sh --repos-dir <path> --config-dir <path>
#
# Arguments:
#   --repos-dir   Directory containing built Lean repositories
#   --config-dir  Directory containing build configs (with patch files)
#
# Examples:
#   # Local build
#   ./scripts/docker_repo_patches.sh \
#     --repos-dir data/lean_repos --config-dir build_config
#
#   # Inside Docker container
#   ./scripts/docker_repo_patches.sh \
#     --repos-dir /workspace/lean_repos --config-dir /workspace/build_config

set -e

# --- Argument parsing ---
REPOS_DIR=""
CONFIG_DIR=""

while [ "$#" -gt 0 ]; do
    case "$1" in
        --repos-dir)   REPOS_DIR="$2"; shift 2 ;;
        --config-dir)  CONFIG_DIR="$2"; shift 2 ;;
        --help|-h)
            head -20 "$0" | tail -18 | sed 's/^# \?//'
            exit 0
            ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

if [ -z "${REPOS_DIR}" ] || [ -z "${CONFIG_DIR}" ]; then
    echo "ERROR: --repos-dir and --config-dir are required"
    echo "Run with --help for usage information"
    exit 1
fi

# Resolve to absolute paths
REPOS_DIR="$(cd "${REPOS_DIR}" && pwd)"
CONFIG_DIR="$(cd "${CONFIG_DIR}" && pwd)"

echo "=== Applying repository patches ==="
echo "Repos:  ${REPOS_DIR}"
echo "Config: ${CONFIG_DIR}"
echo ""

# --- 1. clean repo: Fix simps! config API change ---
# The Mathlib `Simps.Config` `attrs` field changed from `List Name` to `Array Syntax`.
# Use python3 to avoid backtick escaping issues in bash.
echo "[clean] Fixing simps! config in Gadgets/Equality.lean..."
python3 -c "
old = '@[simps! (config := {isSimp := false, attrs := [\x60circuit_norm]})]'
new = '@[circuit_norm, simps! -isSimp]'
with open('${REPOS_DIR}/clean/Clean/Gadgets/Equality.lean') as f:
    c = f.read()
if old in c:
    with open('${REPOS_DIR}/clean/Clean/Gadgets/Equality.lean', 'w') as f:
        f.write(c.replace(old, new))
    print('  Fixed simps! config')
else:
    print('  Pattern not found (may already be fixed)')
"

# --- 1b. clean repo: Add SourceSinkPath.lean (from branch commit d8c947e6) ---
# This file doesn't exist at the pinned commit (a134f91f, Nov 17 2025) but the dataset
# references it. It was added on Nov 18 (as StateTransition.lean) and renamed Nov 20.
# The dataset proofs match commit d8c947e6 (channel-proof-merged branch, Jan 23 2026).
# The file only imports Mathlib, no deps on other clean files.
echo "[clean] Adding SourceSinkPath.lean..."
if [ -f "${CONFIG_DIR}/clean/SourceSinkPath.lean" ]; then
    cp "${CONFIG_DIR}/clean/SourceSinkPath.lean" "${REPOS_DIR}/clean/Clean/Utils/SourceSinkPath.lean"
    echo "  Copied from build_config"
else
    echo "  WARNING: ${CONFIG_DIR}/clean/SourceSinkPath.lean not found, skipping"
fi

# --- 2. Build missing modules in clean ---
echo "[clean] Building missing modules..."
cd "${REPOS_DIR}/clean"
timeout 900 lake build \
    Clean.Utils.SourceSinkPath \
    Clean.Gadgets.Equality \
    Clean.Circuit \
    Clean.Types.U32 \
    Clean.Types.U64 \
    Clean.Table.Inductive \
    Clean.Gadgets.ByteDecomposition.Theorems \
    Clean.Gadgets.Addition32.Addition32 \
    Clean.Gadgets.BLAKE3.BLAKE3State \
    Clean.Gadgets.BLAKE3.Permute \
    Clean.Gadgets.BLAKE3.Round \
    Clean.Gadgets.Keccak.AbsorbBlock \
    Clean.Gadgets.ByteDecomposition.ByteDecomposition \
    2>&1 | tail -5
echo "[clean] Build done."

# --- 3. Build missing modules in lean-formal-reasoning-program ---
echo "[lean-formal-reasoning-program] Building missing modules..."
cd "${REPOS_DIR}/lean-formal-reasoning-program"
timeout 300 lake build Frap.SmallStep Frap.Equiv Frap.Trans 2>&1 | tail -5
echo "[lean-formal-reasoning-program] Build done."

# --- 4. Build missing modules in loom ---
echo "[loom] Building missing modules..."
cd "${REPOS_DIR}/loom"
timeout 300 lake build CaseStudies.Velvet.Std 2>&1 | tail -5
echo "[loom] Build done."

# --- 5. Build missing modules in VCV-io ---
echo "[VCV-io] Building missing modules..."
cd "${REPOS_DIR}/VCV-io"
timeout 300 lake build ToMathlib.PFunctor.Basic 2>&1 | tail -5
echo "[VCV-io] Build done."

# --- 6a. Build cadical from source for lean-mlir nightly toolchain ---
# The cadical binary bundled with lean4-nightly-2025-12-01 requires GLIBC 2.38,
# which is not available on Ubuntu 22.04 (GLIBC 2.35). Build cadical 2.1.2 from
# source and replace the bundled binary so that bv_decide/omega tactics work.
NIGHTLY_TC="/root/.elan/toolchains/leanprover--lean4-nightly---nightly-2025-12-01"
if [ -d "${NIGHTLY_TC}" ]; then
    BUNDLED_CADICAL="${NIGHTLY_TC}/bin/cadical"
    if ! "${BUNDLED_CADICAL}" --version > /dev/null 2>&1; then
        echo "[lean-mlir] Building cadical from source (bundled binary incompatible with system GLIBC)..."
        cd /tmp
        git clone --depth 1 --branch rel-2.1.2 https://github.com/arminbiere/cadical.git
        cd cadical && ./configure && make -j"$(nproc)"
        cp build/cadical "${BUNDLED_CADICAL}"
        cd /tmp && rm -rf cadical
        echo "  Installed cadical $("${BUNDLED_CADICAL}" --version)"
    else
        echo "[lean-mlir] Bundled cadical works, skipping rebuild."
    fi
fi

# --- 6b. Fix lean-mlir Blase MultiWidth stale source files ---
# The Blase subdirectory has its own .lake with stale dependency caches that
# cause the wrong version of MultiWidth files to be used during Docker build.
# The pinned commit (72aca6a6) has the correct 6-param NatFSM/StateSpace types,
# but the container may have 4-param versions from the stale subdirectory build.
echo "[lean-mlir] Fixing Blase MultiWidth source files..."
if [ -d "${CONFIG_DIR}/lean-mlir/MultiWidth" ]; then
    for f in Defs GoodFSM Tactic; do
        if [ -f "${CONFIG_DIR}/lean-mlir/MultiWidth/${f}.lean" ]; then
            cp "${CONFIG_DIR}/lean-mlir/MultiWidth/${f}.lean" \
               "${REPOS_DIR}/lean-mlir/Blase/Blase/MultiWidth/${f}.lean"
            echo "  Updated MultiWidth/${f}.lean"
        fi
    done
    # Clear stale olean cache
    rm -rf "${REPOS_DIR}/lean-mlir/Blase/.lake/build/lib/Blase/MultiWidth/"
    rm -rf "${REPOS_DIR}/lean-mlir/.lake/build/lib/Blase/MultiWidth/"
else
    echo "  WARNING: ${CONFIG_DIR}/lean-mlir/MultiWidth not found, skipping"
fi

# Build Blase and CIRCT modules from root project (NOT Blase subdirectory)
echo "[lean-mlir] Building Blase and CIRCT modules..."
cd "${REPOS_DIR}/lean-mlir"
timeout 600 lake build \
    Blase.Fast.BitStream \
    Blase.Fast.Defs \
    Blase.Fast.Circuit \
    Blase.Fast.FiniteStateMachine \
    Blase.AutoStructs.FiniteStateMachine \
    Blase.MultiWidth.Defs \
    Blase.MultiWidth.GoodFSM \
    Blase.MultiWidth.Tactic \
    Blase.MultiWidth.Preprocessing \
    Blase.MultiWidth.OfExpr \
    SSA.Projects.CIRCT.Stream.Stream \
    SSA.Projects.CIRCT.Stream.WeakBisim \
    2>&1 | tail -5
echo "[lean-mlir] Build done."

# --- 7. Fix iris-lean: Add missing DFrac.update_discard theorem ---
# The theorem DFrac.update_discard doesn't exist at the pinned commit (36d042d, Oct 2025)
# but was added in c9d7a75 (Dec 2025). The theorem and its dependencies (CMRA.Discrete instance)
# can be appended to the existing DFrac.lean since all required imports exist at pinned commit.
echo "[iris-lean] Patching DFrac.lean..."
if [ -f "${CONFIG_DIR}/iris-lean/DFrac.lean" ]; then
    cp "${CONFIG_DIR}/iris-lean/DFrac.lean" "${REPOS_DIR}/iris-lean/src/Iris/Algebra/DFrac.lean"
    cd "${REPOS_DIR}/iris-lean"
    timeout 120 lake build Iris.Algebra.DFrac 2>&1 | tail -3
    echo "[iris-lean] Build done."
else
    echo "  WARNING: ${CONFIG_DIR}/iris-lean/DFrac.lean not found, skipping"
fi

# --- 8. Install SageMath and patch polyrith_sage.py for local Sage ---
# The `polyrith` tactic calls Sage via web API (sagecell.sagemath.org) which is unreliable.
# Install local SageMath and patch the script to use it instead.
if command -v sage &> /dev/null; then
    echo "[formal-snarks-project] SageMath already installed, skipping install."
else
    echo "[formal-snarks-project] Installing SageMath for polyrith..."
    if command -v apt-get &> /dev/null; then
        DEBIAN_FRONTEND=noninteractive apt-get update -qq 2>/dev/null
        DEBIAN_FRONTEND=noninteractive apt-get install -y -qq sagemath 2>&1 | tail -3
    elif command -v brew &> /dev/null; then
        echo "  Install SageMath manually: brew install --cask sage"
        echo "  Or: pip install sage (if available)"
        echo "  Skipping — polyrith will fall back to web API."
    else
        echo "  WARNING: Cannot install SageMath (no apt-get or brew). polyrith will use web API."
    fi
fi

POLYRITH_SCRIPT="${REPOS_DIR}/formal-snarks-project/.lake/packages/mathlib/scripts/polyrith_sage.py"
if [ -f "${POLYRITH_SCRIPT}" ]; then
    echo "[formal-snarks-project] Patching polyrith_sage.py to use local Sage..."
    python3 -c "
script = '${POLYRITH_SCRIPT}'
with open(script) as f:
    content = f.read()
old = '''def evaluate_in_sage(query: str) -> str:
    data = {'code': query}
    headers = {'content-type': 'application/x-www-form-urlencoded'}
    response = requests.post('https://sagecell.sagemath.org/service', data, headers=headers).json()'''
new = '''def evaluate_in_sage(query: str) -> str:
    # Try local sage first
    import subprocess, tempfile, os
    try:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.sage', delete=False) as f:
            f.write(query)
            tmpfile = f.name
        result = subprocess.run(['sage', tmpfile], capture_output=True, text=True, timeout=300)
        os.unlink(tmpfile)
        if result.returncode == 0 and result.stdout.strip():
            return parse_response(result.stdout.strip())
    except Exception:
        pass
    # Fall back to web API
    data = {'code': query}
    headers = {'content-type': 'application/x-www-form-urlencoded'}
    response = requests.post('https://sagecell.sagemath.org/service', data, headers=headers).json()'''
if old in content:
    content = content.replace(old, new)
    with open(script, 'w') as f:
        f.write(content)
    print('  Patched successfully')
else:
    print('  Pattern not found (may already be patched)')
"
fi

echo ""
echo "=== All patches applied ==="
echo "All 500 ground-truth tasks should now verify."
