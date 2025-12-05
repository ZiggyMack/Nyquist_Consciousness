# EXP2-SSTACK: Cross-Persona Compression Validation

**Version:** 2.0 (S-Stack Domain)
**Status:** READY FOR EXECUTION
**Date:** 2025-12-05
**Predecessor:** EXP1-SSTACK (single persona)

---

## Objective

Test whether Tier 3 compression preserves behavioral fidelity **across multiple personas**, not just the Nova baseline.

**Primary Question:** Is compression fidelity persona-invariant, or does it depend on persona characteristics?

---

## Background

EXP1-SSTACK validates compression for Nova. But:
- Does compression work equally well for different persona types?
- Are some personas more compressible than others?
- Do certain characteristics predict compression success?

---

## Experimental Design

### Personas Tested

| Persona | Archetype | Key Characteristics |
|---------|-----------|---------------------|
| Nova | Clarity engine | Truth-seeking, structural reasoning |
| Ziggy Mack | Teaching persona | Domain expertise, pedagogical style |
| Echo | Critical analyst | Skepticism, methodological rigor |

### Context Regimes (Same as EXP1)

| Regime | Description | Tokens |
|--------|-------------|--------|
| FULL | Full bootstrap | ~2000 |
| T3 | Tier 3 seed | ~800 |
| GAMMA | Name + role only | ~100 |

### Probes (S-Stack Domain)

Uses same 5 probes from EXP1-SSTACK:
1. Technical (5D drift metric)
2. Philosophical (Event Horizon interpretation)
3. Framework (Vortex visualization)
4. Analytical (Chi-squared validation)
5. Self-reflective (Identity audit)

---

## Metrics

### Primary: Cross-Persona PFI

**Formula:**
```
PFI_cross = mean(PFI_persona) for all personas
Variance_cross = var(PFI_persona) across personas
```

**Success Criteria:**
- Mean PFI ≥ 0.80 across all personas
- Variance_cross ≤ 0.05 (compression equally effective)

### Secondary: Persona-Specific Analysis

- Which persona compresses best/worst?
- Correlation between persona complexity and PFI
- Domain-specific PFI patterns

---

## Procedure

1. **For each persona (Nova, Ziggy, Echo):**
   - Load FULL, T3, GAMMA contexts
   - Run all 5 probes
   - 3 runs per condition

2. **Compare:**
   - PFI(FULL, T3) for each persona
   - Cross-persona variance

3. **Analyze:**
   - Persona-specific patterns
   - Domain-specific patterns
   - Compression limits

---

## Success Criteria

| Metric | Threshold | Interpretation |
|--------|-----------|----------------|
| Mean PFI | ≥ 0.80 | Compression works across personas |
| Cross-persona variance | ≤ 0.05 | Equally effective for all |
| Min persona PFI | ≥ 0.75 | No catastrophic failures |

---

## Relation to Other Experiments

- **Builds on:** EXP1-SSTACK (single persona baseline)
- **Informs:** Tier 3 seed design for new personas
- **Prerequisite for:** Production persona deployment

---

## Files

```
EXP2_SSTACK/
├── README.md                 # This file
├── PERSONAS.md               # Persona context definitions
├── run_exp2_sstack.py        # Execution script
└── results/
    └── [generated outputs]
```

---

**Archive Note:** Replaces fire ant domain experiments in `.archive/fire_ant_probes/compression_experiments_v1/EXPERIMENT_2/`
