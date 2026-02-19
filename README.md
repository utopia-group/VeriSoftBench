# VeriSoftBench

A benchmark for evaluating neural theorem provers on software verification tasks in Lean 4.

VeriSoftBench contains 500 theorem-proving tasks drawn from 23 real-world Lean 4 repositories spanning compiler verification, type system formalization, applied verification (zero-knowledge proofs, smart contracts), semantic frameworks, and more.

## Quick Start

### 1. Install dependencies

```bash
pip install -r requirements.txt
```

### 2. Get the dataset

The dataset (`data/verisoftbench.jsonl`) is included in this repository.

### 3. Build Lean repositories

Proofs are verified against the actual Lean repositories. You need either Docker (recommended) or a local build.

**Option A: Docker (recommended)**

```bash
# Build the image (~1 hour, downloads Mathlib caches)
docker build -t verisoftbench/lean:latest .

# Start the container
docker run -d --name verisoftbench-test verisoftbench/lean:latest
```

**Option B: Local build**

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager, which provides `lake`):

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
./scripts/setup_repos.sh --clone --config-dir build_config --output-dir data/lean_repos
```

### 4. Run evaluation

```bash
# With a config file (recommended)
python evaluate.py --config configs/openai_example.yaml

# Or with CLI arguments
python evaluate.py \
  --model-name openai \
  --model-id gpt-4o \
  --lean-backend docker \
  --task-ids 1:10
```

## Configuration

### Config files

YAML config files in `configs/` are the recommended way to configure runs. Config values override CLI arguments.

| File | Description |
|------|-------------|
| `configs/default.yaml` | Full reference config with all options documented |
| `configs/openai_example.yaml` | OpenAI (GPT-4o) |
| `configs/claude_example.yaml` | Anthropic (Claude) |
| `configs/gemini_example.yaml` | Google (Gemini) |

### API keys

Set your API key via environment variable (preferred) or in the config file:

```bash
# OpenAI
export OPENAI_API_KEY=sk-...

# Anthropic
export ANTHROPIC_API_KEY=sk-ant-...

# Google
export GOOGLE_API_KEY=...
```

### Key options

| Option | Default | Description |
|--------|---------|-------------|
| `model_name` | `openai` | Provider: `openai`, `claude`, or `gemini` |
| `model_id` | `gpt-4o` | Model identifier |
| `mode` | `filtered_context` | Context mode (see below) |
| `fix_enabled` | `true` | Enable proof fixing (3 rounds) |
| `num_samples` | `1` | Proof attempts per theorem |
| `max_workers` | `8` | Parallel evaluation workers |
| `lean_backend` | `local` | `local` or `docker` |
| `task_ids` | all | Filter tasks: `"1:10"` (range) or `"1,5,10"` (list) |
| `category` | all | Filter by category (exact match) |
| `refresh_cache` | `false` | Re-evaluate cached tasks |

### Context modes

- **`filtered_context`** (default): Each task gets only the definitions and lemmas identified as relevant by static analysis. This is the primary evaluation mode.
- **`full_context`**: Each task gets all definitions and lemmas from its repository. Useful for testing models with richer context.
- **`full_context_limited`**: Pre-generated full-context prompts for ArkLib and lean-mlir (the two largest repos). Avoids token limits by capping context size.

## Task selection

```bash
# Evaluate specific task IDs
python evaluate.py --config configs/default.yaml --task-ids 1,5,10,15

# Evaluate a range
python evaluate.py --config configs/default.yaml --task-ids 1:50

# Evaluate a category (exact match on category field)
python evaluate.py --config configs/default.yaml --category "Transformation Correctness"

# Evaluate a random subset
python evaluate.py --config configs/default.yaml --subset 50
```

## Results

Results are saved to `results/data/<run_name>/`:

```
results/data/gpt-4o_20250210_120000/
  summary.json         # Overall statistics
  details/             # Per-theorem results
    theorem_name__file.json
```

`summary.json` contains:
```json
{
  "total_theorems": 500,
  "theorems_proved_wo_fix": 120,
  "theorems_proved_w_fix": 145,
  "proof_success_rate_wo_fix": 0.24,
  "proof_success_rate_w_fix": 0.29
}
```

Results are cached per model in `results/cache/`. Subsequent runs skip already-evaluated tasks unless `--refresh-cache` is set.

## Docker details

The Docker image contains pre-built Lean repositories with all dependencies compiled. The evaluation pipeline runs on the host and uses `docker exec` to invoke Lean compilation inside the container.

```bash
# Build (from the repository root)
docker build -t verisoftbench/lean:latest .

# Start (stays running for docker exec calls)
docker run -d --name verisoftbench-test verisoftbench/lean:latest

# Run evaluation against the container
python evaluate.py --config configs/openai_example.yaml --lean-backend docker

# Stop when done
docker stop verisoftbench-test
```

The image is ~110 GB and takes ~1 hour to build (Mathlib cache downloads dominate build time).

## Project structure

```
VeriSoftBench/
  evaluate.py              # Main evaluation entry point
  requirements.txt         # Python dependencies
  configs/                 # YAML configuration files
  core/                    # Evaluation pipeline
    evaluator.py           #   Benchmark orchestrator
    lean_interface.py      #   Lean compilation (local/Docker)
    prover_interface.py    #   LLM API abstraction
  prompts/                 # Prompt templates and examples
    templates/             #   System/user prompt templates
    full_limited/          #   Pre-generated full-context prompts
    prompt_builder.py      #   Prompt construction
  analysis/                # Proof output analysis
  config/                  # Path configuration
  utils/                   # Shared utilities
  scripts/                 # Build and setup scripts
  build_config/            # Per-repo build configs (lean-toolchain, lakefile, etc.)
  data/                    # Dataset and supplementary files
    verisoftbench.jsonl    #   Benchmark tasks (500 theorems)
  Dockerfile               # Lean proof environment image
  repos.json               # Repository metadata (URLs, commits, licenses)
  THIRD_PARTY_NOTICES.txt  # Third-party license information
  LICENSE                  # MIT License (evaluation code)
```

## Dataset

Each task in `verisoftbench.jsonl` contains:
- Theorem name, statement, and source location
- Filtered dependencies (library defs, repo defs, local context, lemmas)
- Ground truth proof
- Metadata (category, difficulty metrics, Aristotle subset membership)

## License

The evaluation code is released under the [MIT License](LICENSE).

The benchmark repositories are redistributed under their original licenses. See [THIRD_PARTY_NOTICES.txt](THIRD_PARTY_NOTICES.txt) for details.

## Citation

Coming soon.
