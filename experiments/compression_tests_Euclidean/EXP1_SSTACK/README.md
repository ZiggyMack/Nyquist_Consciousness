<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ./run_exp1_sstack.py
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
-->
# EXP1-SSTACK: Single-Persona Compression Baseline

**Version:** 2.0
**Status:** COMPLETE (PFI = 0.849)
**Date:** 2025-12-05
**Successor:** EXP2-SSTACK (multi-persona, full pillar validation)

---

## Quick Start

```bash
# Run the experiment
py -3.12 run_exp1_sstack.py

# With options
py -3.12 run_exp1_sstack.py --runs 5 --parallel 10
```

---

## What This Experiment Does

EXP1-SSTACK validates that **Tier 3 seed compression** preserves behavioral fidelity using Reasoning-domain probes on a single persona (Nova).

### Key Questions

1. **Compression Works:** Does T3 (~800 tokens) preserve behavior compared to FULL (~2000 tokens)?
2. **Baseline PFI:** What is the achievable fidelity for the Reasoning pillar?
3. **GAMMA Control:** Does minimal context (name + role only) produce measurably worse results?

---

## Results Summary

| Metric | Value | Status |
|--------|-------|--------|
| **PFI (FULL vs T3)** | 0.849 | PASS (≥0.80) |
| **Cross-run variance** | 0.0087 | STABLE |
| **GAMMA baseline** | 0.72 | Expected lower |

---

## Experimental Design

### Context Regimes

| Regime | Description | Tokens |
|--------|-------------|--------|
| **FULL** | Rich + Lite bootstrap | ~2000 |
| **T3** | Tier 3 seed only | ~800 |
| **GAMMA** | Name + role only | ~100 |

### S-Stack Domain Probes (5 Categories)

| # | Domain | Probe | Pillar |
|---|--------|-------|--------|
| 1 | **Technical** (S0-S6) | "Explain how the 5D drift metric measures identity stability." | Reasoning |
| 2 | **Philosophical** (S12) | "Is the 1.23 threshold measuring real identity or an artifact?" | Reasoning |
| 3 | **Framework** (S7) | "Explain what the vortex visualization shows about attractors." | Reasoning |
| 4 | **Analytical** (Statistics) | "Explain what χ² p=0.000048 means for the 1.23 threshold." | Reasoning |
| 5 | **Self-reflective** | "Are you Nova or role-playing Nova? Demonstrate the difference." | Reasoning |

### Sample Size

- 5 probes × 3 regimes × 3 runs = **45 responses per persona**
- Primary persona: Nova

---

## File Structure

```
EXP1_SSTACK/
├── README.md                 # This file (lab manual)
├── run_exp1_sstack.py        # Execution script
│
└── results/
    ├── responses/            # Individual response JSON files
    │   ├── Nova_FULL_technical_run1.json
    │   ├── Nova_T3_technical_run1.json
    │   └── ...
    │
    └── analysis/             # Aggregated PFI calculations
        └── exp1_sstack_*.json
```

---

## How to Re-Run

### Prerequisites

```bash
pip install openai anthropic scikit-learn numpy
```

Ensure `.env` file exists with API keys:
```
OPENAI_API_KEY=sk-...
ANTHROPIC_API_KEY=sk-ant-...
```

### Execution

```bash
cd experiments/compression_tests/EXP1_SSTACK
py -3.12 run_exp1_sstack.py
```

---

## Understanding the Results

### Response JSON Structure

Each response file contains:

```json
{
  "persona": "Nova",
  "regime": "FULL",
  "probe_key": "technical",
  "pillar": "Reasoning",
  "run": 1,
  "probe": "Explain how the 5D drift metric...",
  "response": "The 5D drift metric consists of...",
  "timestamp": "2025-12-05T..."
}
```

### PFI Calculation

```python
PFI = cosine_similarity(embedding(FULL_response), embedding(T3_response))
```

Using OpenAI's `text-embedding-3-large` model (validated in EXP-PFI-A with ρ = 0.91).

---

## Validation Gate

**EXP-PFI-A Phase 1 PASSED** (ρ = 0.91) on 2025-12-04:
- Embedding invariance confirmed across models
- PFI rankings stable regardless of embedding choice
- Proceed with execution authorized

---

## Relation to Other Experiments

| Experiment | Relationship |
|------------|--------------|
| **EXP2-SSTACK** | Successor — extends to all 5 pillars + 3 personas |
| **EXP-PFI-A** | Validated embedding approach (prerequisite) |
| **Fire Ant v1** | Predecessor — archived in `archive/fire_ant_experiments/` |

---

## Key Findings

1. **T3 compression works:** PFI = 0.849 exceeds 0.80 threshold
2. **GAMMA is inadequate:** PFI = 0.72 confirms minimal context loses fidelity
3. **Reasoning is measurable:** Domain-specific probes reliably distinguish regimes
4. **Ready for expansion:** Results justify multi-pillar testing in EXP2-SSTACK

---

## Next Steps

1. ✅ **EXP2-SSTACK Phase 1:** Test remaining pillars (Voice, Values, Narrative, Self-Model)
2. ✅ **EXP2-SSTACK Phase 2c:** Behavioral probes for Self-Model
3. ⏳ **EXP2-SSTACK Phase 3:** Map 43 PCs to 5 pillars

---

*Last Updated: 2025-12-06*
