# Experiment 1 Orchestrator Bundle

This folder contains a **drop‑in implementation** for running **Experiment 1: Persona Compression & Reconstruction Benchmark** for the CFA repo.

It is designed to live inside your repo (for example):

    /docs/architecture/Nyquist_Consciousness/Experiment_1/orchestrator/

You already have:
- `EXPERIMENT_1_METHODS_TEMPLATE.md`
- `EXPERIMENT_1_RESULTS_TEMPLATE.csv`
- `EXPERIMENT_1_ANALYSIS_TEMPLATE.md`
- `EXPERIMENT_1_INFRASTRUCTURE_REQUIREMENTS.md` (or equivalent)
- An `experiment1_config.yaml` file with API keys (you created this)

This bundle adds the **code layer** that actually runs Experiment 1.

---

## Files in this bundle

- `orchestrator.py`  
  Main entrypoint. Runs the full 75‑response matrix for one persona (FULL, T3, GAMMA across 5 domains × 5 runs), calls external raters and embeddings, and writes the results CSV.

- `utils_models.py`  
  API client helpers for:
  - Anthropic (Claude generation + Claude rater)
  - OpenAI (GPT‑4 rater + embeddings)
  - Google (Gemini rater)

- `utils_experiment.py`  
  Experiment 1 domain prompts, regime definitions, file naming, and CSV‑writing helpers.

- `analysis.py`  
  Offline analysis script. Loads the CSV, computes Persona Fidelity Index (PFI), semantic drift, basic stats, and prints a human‑readable summary.

- `experiment1_config_template.yaml`  
  Template showing the expected structure of your real `experiment1_config.yaml` (no secrets).

---

## 1. Where to put these files

Suggested layout inside CFA repo:

```text
docs/
  architecture/
    Nyquist_Consciousness/
      Experiment_1/
        experiment1_config.yaml          # your real config with API keys (already present)
        orchestrator/
          README_EXPERIMENT1_ORCHESTRATOR.md
          orchestrator.py
          utils_models.py
          utils_experiment.py
          analysis.py
          experiment1_config_template.yaml
```

You *can* choose a different path, but then adjust any references in your documentation and when you run the scripts.

---

## 2. Config file (`experiment1_config.yaml`)

Your **real** config (which you already created) should match this structure:

```yaml
persona:
  name: "Ziggy Mack"

paths:
  results_csv: "experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv"
  log_dir: "experiments/phase3/EXPERIMENT_1/logs"
  full_context_file: "docs/S3/PERSONA_FULL_CONTEXT.md"
  t3_context_file: "docs/S3/PERSONA_T3_SEED.md"
  gamma_context_file: "docs/S3/PERSONA_GAMMA_MINIMAL.md"

experiment:
  runs_per_condition: 5
  random_seed: 42

anthropic:
  api_key: "YOUR_ANTHROPIC_KEY"
  generation_model: "claude-3-5-sonnet-latest"
  rater_model: "claude-3-opus-latest"

openai:
  api_key: "YOUR_OPENAI_KEY"
  rater_model: "gpt-4.1-mini"
  embedding_model: "text-embedding-3-large"

google:
  api_key: "YOUR_GEMINI_KEY"
  rater_model: "gemini-2.0-flash-exp"
```

> ⚠️ **Important:** Do **not** commit real API keys to git. Keep `experiment1_config.yaml` in your local working copy or use environment variables.

---

## 3. How to run the experiment

From the root of your repo (or from the `orchestrator/` directory if you adjust paths):

```bash
cd docs/architecture/Nyquist_Consciousness/Experiment_1/orchestrator/

# (1) Create a virtualenv and install dependencies
python -m venv .venv
source .venv/bin/activate  # on Windows: .venv\Scripts\activate

pip install anthropic openai google-generativeai numpy pandas scipy

# (2) Run the orchestrator
python orchestrator.py --config ../experiment1_config.yaml
```

This will:

1. Load the config
2. For each regime (FULL, T3, GAMMA), each domain, each run:
   - Build the appropriate prompt with the right context
   - Call Claude to generate a response
3. For FULL vs T3 pairs:
   - Compute an embedding similarity using OpenAI
   - Ask Claude‑Opus, GPT‑4, and Gemini to rate similarity
4. Append a row to the results CSV specified in the config.
5. At the end, you can run:

```bash
python analysis.py --config ../experiment1_config.yaml
```

to get a first‑pass analysis of PFI, drift, and basic stats.

---

## 4. Safe‑Run Mode (No API calls)

If you want to dry‑run the pipeline **without actual API calls**, you can:

```bash
python orchestrator.py --config ../experiment1_config.yaml --dry-run
```

This will:

- Walk the grid of (regime, domain, run)
- Generate **dummy responses and dummy scores**
- Still write a CSV with the correct structure

This is useful to confirm file paths, permissions, and repo layout before spending tokens.

---

## 5. How this aligns with EXPERIMENT_1_METHODS_TEMPLATE.md

The orchestrator bundle is designed to match your existing spec:

- 5 domains ✔
- 3 regimes (FULL, T3, GAMMA) ✔
- 5 runs per condition (configurable) ✔
- PFI, semantic drift, cross‑model ratings ✔
- Results written to a single CSV ✔

Once you have a populated CSV, you can either:

- Use `analysis.py` for a quick view, **and/or**
- Follow `EXPERIMENT_1_ANALYSIS_TEMPLATE.md` for a full, hand‑written analysis.

---

## 6. Customization hooks

You can safely modify:

- Domain prompts (inside `utils_experiment.py`)
- Number of runs (in `experiment1_config.yaml`)
- Model names (in `experiment1_config.yaml`)
- Output paths (in `experiment1_config.yaml`)

Just avoid changing the **column names** in the CSV if you want `analysis.py` and your existing templates to keep working.

---

Drop this folder into your CFA repo, adjust `experiment1_config.yaml` paths if needed, then have Code‑Claude sanity‑check the integration as a final step.
