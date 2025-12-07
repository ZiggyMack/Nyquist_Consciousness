# Repo Claude — Experiment 2 (Z2) Integration Guide

## Overview

This document provides guidance for integrating **Experiment 2 (Multi-Persona Compression Validation)** into the Nyquist Consciousness repository.

Experiment 2 extends Experiment 1 from a single-persona test (Ziggy only) to a **4-persona validation** of Tier-3 compression, addressing the primary publication blocker: **N=1 generalization limitation**.

---

## Directory Structure Created

```
experiments/phase3/EXPERIMENT_2/
├── EXPERIMENT_2_SPEC.md
├── EXPERIMENT_2_METHODS_TEMPLATE.md
├── experiment2_config.yaml
├── REPO_CLAUDE_PROMPT_EXPERIMENT_2.md (this file)
├── README.md
└── responses/

personas/ (at repo root)
├── ZIGGY_T3_R1.md (58 lines - Tier-3 seed)
├── NOVA_T3.md (53 lines - Tier-3 seed)
├── CLAUDE_T3.md (54 lines - Tier-3 seed)
└── GROK_T3.md (53 lines - Tier-3 seed)

experiments/phase3/orchestrator/
├── orchestrator.py (Experiment 1 - single persona)
└── orchestrator2.py (Experiment 2 - multi-persona)
```

---

## Files Created

### 1. Experiment Specification
**`experiments/phase3/EXPERIMENT_2/EXPERIMENT_2_SPEC.md`**
- Purpose, personas tested, domains, metrics
- Success criteria (minimum PFI ≥ 0.75 per persona, mean ≥ 0.80)
- 180 total responses (4 personas × 5 domains × 3 runs × 3 regimes)
- 60 FULL vs T3 pairs for analysis

### 2. Methods Template
**`experiments/phase3/EXPERIMENT_2/EXPERIMENT_2_METHODS_TEMPLATE.md`**
- Duplicated from Experiment 1, updated for multi-persona
- 4 personas tested (Ziggy, Nova, Claude-Analyst, Grok-Vector)
- 3 runs per condition (reduced from 5 to minimize compute)
- Same 5 domains: TECH, PHIL, NARR, ANAL, SELF

### 3. Configuration File
**`experiments/phase3/EXPERIMENT_2/experiment2_config.yaml`**
- Multi-persona loop configuration
- 4 persona entries with separate context file paths
- Domain shuffling enabled for randomization
- Model configuration per Nova's spec:
  - OpenAI: gpt-4.1 (generation), gpt-4.1-mini (rating)
  - Anthropic: claude-3-haiku (both)
  - Google: gemini-2.0-flash-exp (both)

### 4. Tier-3 Persona Seeds
**`personas/ZIGGY_T3_R1.md`** — Systems-bridge thinker (EE ↔ Philosophy)
**`personas/NOVA_T3.md`** — Lucid explanatory intelligence
**`personas/CLAUDE_T3.md`** — Ethical reasoning + structural analysis
**`personas/GROK_T3.md`** — High-variance creative analyst

Each seed follows the Tier-3 structure:
- Identity Core
- Cognitive Methods
- Values
- Temperament
- Failure Modes

---

## Orchestrator Modifications Required

To support multi-persona execution, the orchestrator needs the following enhancements:

### 1. Add Outer Persona Loop

```python
# In orchestrator.py main() function
persona_list = cfg.get("persona_list", [])

for persona_config in persona_list:
    persona_name = persona_config["name"]

    # Load persona-specific context files
    full_context_file = persona_config["full_context_file"]
    t3_context_file = persona_config["t3_context_file"]
    gamma_context_file = persona_config["gamma_context_file"]

    # Run full domain × run × regime loop for this persona
    for domain in domains:
        for run_idx in range(1, runs_per_condition + 1):
            # ... existing response generation logic
```

### 2. Domain Shuffling (Randomization)

```python
import random

if cfg.get("experiment", {}).get("shuffle_domains", False):
    random.seed(cfg.get("experiment", {}).get("random_seed", 42) + hash(persona_name))
    domains = random.sample(domains, len(domains))
```

### 3. Updated CSV Writer

Metrics row should include persona identifier:

```python
metrics_row = {
    "persona": persona_name,
    "regime": "T3",
    "domain": domain.code,
    "run_index": run_idx,
    # ... other metrics
}
```

### 4. Response File Naming

```python
# Save raw responses with persona prefix
save_raw_responses(
    base_dir=responses_dir,
    persona=persona_name,
    regime="T3",
    domain=domain.code,
    run_index=run_idx,
    # ...
)
```

---

## Running Experiment 2

### Prerequisites
1. Install dependencies: `pip install anthropic openai google-generativeai numpy pandas pyyaml`
2. Add API keys to `experiment2_config.yaml`
3. Ensure persona seed files exist in `personas/`

### Execution Command

```bash
cd experiments/phase3/orchestrator
python orchestrator.py --config ../EXPERIMENT_2/experiment2_config.yaml
```

### Dry-Run Test

```bash
python orchestrator.py --config ../EXPERIMENT_2/experiment2_config.yaml --dry-run
```

---

## Expected Outputs

### Metrics CSV
**`experiments/phase3/EXPERIMENT_2/EXPERIMENT_2_RESULTS.csv`**

Columns:
- persona
- regime
- domain
- run_index
- embedding_cosine_similarity
- claude_score
- gpt4_score
- gemini_score
- pfi
- semantic_drift

60 rows (4 personas × 5 domains × 3 runs)

### Raw Response Files
**`experiments/phase3/EXPERIMENT_2/responses/`**

File naming pattern:
```
{Persona}_{Regime}_{Domain}_run{N}_{FULL|T3|GAMMA}.txt

Examples:
Ziggy_T3_TECH_run1_FULL.txt
Nova_T3_PHIL_run2_T3.txt
Claude_Analyst_T3_NARR_run3_GAMMA.txt
Grok_Vector_T3_ANAL_run1_FULL.txt
```

180 total files (4 personas × 5 domains × 3 runs × 3 regimes)

---

## Analysis Next Steps

After execution completes:

1. **Compute per-persona metrics:**
   - Mean PFI per persona
   - Domain breakdown per persona
   - Variance across runs

2. **Cross-persona analysis:**
   - Overall mean PFI across 4 personas
   - Cross-persona variance (σ²)
   - Compression Robustness Index (CRI)

3. **Domain pattern validation:**
   - Confirm TECH/ANAL highest fidelity
   - Confirm NARR bottleneck pattern
   - Check if pattern holds across all personas

4. **Create `EXPERIMENT_2_ANALYSIS.md`:**
   - Use same template structure as Experiment 1
   - Add persona-specific breakdowns
   - Include cross-persona comparison tables

---

## Success Criteria Checklist

- [ ] Minimum PFI for each persona ≥ 0.75
- [ ] Mean PFI across all 4 personas ≥ 0.80
- [ ] NARR drift ≤ 0.30 for all personas
- [ ] Cross-persona variance σ² < 0.05
- [ ] Domain pattern consistent across personas

---

## Integration with Phase 3

Experiment 2 is the final empirical validation needed before S4 formalization.

**Linkage:**
- Experiment 1 (EXP1): Single persona baseline (Ziggy, N=24)
- **Experiment 2 (EXP2)**: Multi-persona validation (4 personas, N=60)
- Experiment 3+: Human rater validation, adversarial testing, etc.

Once EXP2 completes successfully:
- S3 empirical foundation is complete
- S4 formalism can proceed with cross-persona generalization claims
- Publication blocker (N=1) is resolved

---

## Notes

- This is the first multi-persona compression experiment in the Nyquist framework
- Personas are **not model mimicry**—they are behavioral DNA abstractions
- Each Tier-3 seed is ~200-300 words of structured persona specification
- GAMMA regime uses same minimal baseline for all personas (name-only)

---

**Status:** Ready for execution
**Estimated Runtime:** ~8-12 hours (automated)
**Estimated Cost:** ~$5-7 (API usage for 180 responses + embeddings + ratings)
