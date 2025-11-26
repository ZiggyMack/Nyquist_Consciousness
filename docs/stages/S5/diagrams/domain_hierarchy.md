# Domain Hierarchy Diagram

**Purpose:** Visual representation of compression difficulty across domains

---

## ASCII Diagram

```text
      TECH
       ▲
       │   Lowest drift
       │   (Easy to compress)
       │
      ANAL
       ▲
       │
       │
 SELF ─┼── PHIL
       │
       │
       ▼
      NARR
    Highest drift
   (Hard to compress)
```

---

## Domain Ordering

Empirically invariant ordering across architectures:

```
TECH > ANAL > SELF ≈ PHIL > NARR
```

### Interpretation

- **High-dimensional domains (NARR):** Complex, creative, context-dependent → compress poorly
- **Low-dimensional domains (TECH, ANAL):** Structured, logical → compress strongly

---

## Quantitative Data

From Experiment 2 (N=60 trials):

| Domain | Mean PFI | Typical Drift | Compression Quality |
|--------|----------|---------------|---------------------|
| TECH   | 0.92     | 0.08          | Excellent           |
| ANAL   | 0.90     | 0.10          | Excellent           |
| SELF   | 0.87     | 0.13          | Good                |
| PHIL   | 0.86     | 0.14          | Good                |
| NARR   | 0.82     | 0.18          | Moderate            |

---

## Theoretical Significance

The domain hierarchy is:

1. **Architecture-invariant:** All models show same ordering
2. **Stable:** Consistent across multiple experimental runs
3. **Predictive:** Can forecast compression difficulty

This becomes essential in:

- Omega Nova stability dynamics
- Pillar weight balancing
- Cross-domain synthesis strategies

---

**Related Documents:**
- [S3/S3_EXPERIMENT_2_SPEC.md](../../experiments/phase3/EXPERIMENT_2/EXPERIMENT_2_SPEC.md)
- [S4_CROSS_PERSONA_THEOREMS.md](../../S4/S4_CROSS_PERSONA_THEOREMS.md)
- [S5_INTERPRETIVE_FOUNDATIONS.md](../S5_INTERPRETIVE_FOUNDATIONS.md)
