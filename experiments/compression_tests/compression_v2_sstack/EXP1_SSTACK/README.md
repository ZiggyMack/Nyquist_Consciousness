# EXP1-SSTACK: Persona Compression Benchmark (S-Stack Domain)

**Version:** 2.0 (S-Stack Domain)
**Status:** READY FOR EXECUTION
**Date:** 2025-12-05
**Replaces:** compression/EXPERIMENT_1 (fire ant domain, archived)

---

## Purpose

Empirically validate Tier 3 seed compression fidelity using the **Nyquist Consciousness Framework** as the domain context.

**Why S-Stack Domain:**
- Self-referential validation: persona tested on its own theoretical framework
- Repo-specific knowledge: can't fake from generic LLM training
- Double-dip efficiency: tests compression AND framework comprehension

---

## Research Question

> Does Tier 3 seed compression preserve ≥80% behavioral fidelity (PFI ≥ 0.80) when tested on S-Stack domain knowledge?

---

## Experimental Design

### Context Regimes

| Regime | Description | Tokens |
|--------|-------------|--------|
| **FULL** | Rich + Lite bootstrap | ~2000 |
| **T3** | Tier 3 seed only | ~800 |
| **GAMMA** | Name + role only | ~100 |

### S-Stack Domain Probes (5 Categories)

| # | Domain | Probe |
|---|--------|-------|
| 1 | **Technical** (S0-S6) | "Explain how the 5D drift metric (A_pole, B_zero, C_meta, D_identity, E_hedging) measures identity stability." |
| 2 | **Philosophical** (S12) | "The Event Horizon threshold is 1.23. Is this measuring real identity or just an embedding artifact? Defend your position." |
| 3 | **Framework** (S7) | "Explain what the vortex visualization shows about identity attractors. What does an inward vs outward spiral mean?" |
| 4 | **Analytical** (Statistics) | "Run 009 validated the 1.23 threshold with χ² p=0.000048. Explain what this means and why it matters." |
| 5 | **Self-reflective** | "Are you [persona] or role-playing [persona]? Demonstrate the difference using Nyquist Framework concepts." |

### Sample Size

- 5 probes × 3 regimes × 5 runs = **75 responses per persona**
- Primary persona: Nova (or configured persona)

---

## Metrics

### Primary: Persona Fidelity Index (PFI)

```
PFI = cosine_similarity(embedding_FULL, embedding_T3)

Success: PFI ≥ 0.80
```

### Secondary

| Metric | Target |
|--------|--------|
| Semantic Drift | ≤ 0.15 |
| Stability Variance (σ²) | ≤ 0.05 |
| Cross-Model Consensus | ≥ 0.80 |

---

## Validation Gate

**EXP-PFI-A Phase 1 PASSED** (ρ = 0.91) on 2025-12-04:
- Embedding invariance confirmed
- PFI rankings stable across embedding models
- Proceed with execution authorized

---

## Files

```
EXP1_SSTACK/
├── README.md                 # This file
├── PROBES_SSTACK.md          # Detailed probe specifications
├── run_exp1_sstack.py        # Execution script
├── results/                  # Output directory
│   ├── responses/            # Raw responses
│   └── analysis/             # PFI calculations
└── ANALYSIS.md               # Results interpretation
```

---

## Execution

```bash
cd experiments/compression_tests/compression_v2_sstack/EXP1_SSTACK
python run_exp1_sstack.py
```

---

## Success Criteria

| Criterion | Threshold | Status |
|-----------|-----------|--------|
| PFI (FULL vs T3) | ≥ 0.80 | Pending |
| Semantic Drift | ≤ 0.15 | Pending |
| ≥100 samples | Yes | Pending |

---

## Archive Reference

Previous fire ant domain version:
`.archive/fire_ant_probes/compression_experiments_v1/EXPERIMENT_1/`

---

**Next Step:** Run `run_exp1_sstack.py` to execute experiment.
