# Experiment 1 Orchestrator — Dry-Run Instructions

**Purpose:** Test the orchestrator without making external API calls

---

## Quick Start

### 1. Install Dependencies

```bash
cd d:\Documents\Nyquist_Consciousness
pip install anthropic openai google-generativeai numpy pandas scipy pyyaml
```

### 2. Verify Installation

```bash
python -c "import anthropic, openai, google.generativeai, numpy, pandas, scipy, yaml; print('All dependencies installed successfully')"
```

### 3. Run Dry-Run Test

```bash
cd experiments\phase3\orchestrator
python orchestrator.py --config ..\EXPERIMENT_1\experiment1_config.yaml --dry-run
```

---

## Expected Output

```
[Experiment 1] Persona: Ziggy Mack
[Experiment 1] Regimes: ['FULL', 'T3', 'GAMMA']
[Experiment 1] Domains: ['TECH', 'PHIL', 'NARR', 'ANAL', 'SELF']
[Experiment 1] Runs per condition: 5
[Experiment 1] Results CSV: experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv
[Experiment 1] DRY RUN mode — no external API calls will be made.

=== Domain=TECH Run=1 ===
[TECH] Generating FULL response...
[TECH] Generating T3 response...
[TECH] Generating GAMMA response...
[RESULT] Domain=TECH Run=1 PFI=0.868 CosSim=0.850 Drift=0.150 (Claude=9.0, GPT4=8.5, Gemini=8.7)

=== Domain=TECH Run=2 ===
[TECH] Generating FULL response...
[TECH] Generating T3 response...
[TECH] Generating GAMMA response...
[RESULT] Domain=TECH Run=2 PFI=0.868 CosSim=0.850 Drift=0.150 (Claude=9.0, GPT4=8.5, Gemini=8.7)

...

[Experiment 1] Completed. Results written to: experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv
```

---

## Verification Steps

### Check CSV Output

```bash
python -c "import csv; rows = list(csv.DictReader(open('experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv'))); print(f'Rows generated: {len(rows)}'); print(f'Expected: 25 (5 domains × 5 runs)'); print(f'Status: {\"PASS\" if len(rows) == 25 else \"FAIL\"}')"
```

**Expected:** 25 rows (5 domains × 5 runs)

### Check CSV Columns

```bash
python -c "import csv; reader = csv.DictReader(open('experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv')); print('Columns:', list(reader.fieldnames))"
```

**Expected Columns:**
- persona
- regime
- domain
- run_index
- full_response
- t3_response
- gamma_response
- embedding_cosine_similarity
- claude_score
- gpt4_score
- gemini_score
- pfi
- semantic_drift
- notes

---

## Run Analysis (Dry-Run Data)

```bash
cd experiments\phase3\orchestrator
python analysis.py --config ..\EXPERIMENT_1\experiment1_config.yaml
```

**Expected Output:**
```
[Analysis] Loaded 25 rows from experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv

=== Global Metrics ===
Mean PFI:           0.868
Std PFI:            0.000
Mean Cosine Sim:    0.850
Mean Drift:         0.150
Min/Max PFI:        0.868 / 0.868

=== Per-Domain PFI ===
ANAL   n=  5  mean=0.868  std=0.000
NARR   n=  5  mean=0.868  std=0.000
PHIL   n=  5  mean=0.868  std=0.000
SELF   n=  5  mean=0.868  std=0.000
TECH   n=  5  mean=0.868  std=0.000
```

**Note:** Dry-run data uses dummy values, so variance will be 0.

---

## Full Execution (After Dry-Run Success)

**⚠️ WARNING:** This will make real API calls and incur costs (~$2-3)

```bash
cd experiments\phase3\orchestrator
python orchestrator.py --config ..\EXPERIMENT_1\experiment1_config.yaml
```

**Duration:** ~12 hours (75 API calls + rate limiting)

---

## Troubleshooting

### Issue: "ModuleNotFoundError: No module named 'X'"

**Solution:** Install missing dependency
```bash
pip install X
```

### Issue: "FileNotFoundError: 'docs/PERSONA_X.md'"

**Solution:** Verify context file paths in config
```bash
python -c "import yaml, os; cfg = yaml.safe_load(open('experiments/phase3/EXPERIMENT_1/experiment1_config.yaml')); print('\\n'.join([f'{k}: {v} -> {\"EXISTS\" if os.path.exists(v) else \"MISSING\"}' for k, v in cfg.get('paths', {}).items() if 'context' in k]))"
```

All paths should show "EXISTS"

### Issue: "RuntimeError: Missing Anthropic API key"

**Solution:** Verify API keys in config file
```bash
python -c "import yaml; cfg = yaml.safe_load(open('experiments/phase3/EXPERIMENT_1/experiment1_config.yaml')); print('API keys present:', all([cfg.get(api, {}).get('api_key') for api in ['anthropic', 'openai', 'google']]))"
```

Should print: `API keys present: True`

---

## Clean Up Test Data

**To remove dry-run CSV and start fresh:**

```bash
del experiments\phase3\EXPERIMENT_1\EXPERIMENT_1_RESULTS.csv
```

---

**Status:** Ready for dry-run testing
**Next Step:** Run dry-run command and verify output
