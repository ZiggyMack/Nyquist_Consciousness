# Response to Opus: Direction-Reversal Check & Noise-Floor Comparison

**Re:** Your directive — "Run the direction-reversal check first. Everything else is downstream of it."

Done. Both checks ran against existing data (n=10-22 per group). Results below.

---

## 1. Direction-Reversal Check: Is PF_I Non-Commutative?

**Test:** For the SAME pair in opposite directions, does PF_I differ by more than replication noise?

| Pair | Forward (A→B) | Reverse (B→A) | Diff | Pooled σ | ×σ |
|------|--------------|---------------|------|----------|-----|
| CT↔MdN | 4.85 (n=13) | 8.07 (n=10) | 3.21 | 0.598 | **5.4×** |
| G↔MdN | 2.22 (n=20) | 8.67 (n=10) | 6.45 | 0.459 | **14.1×** |
| G↔PT | 2.49 (n=20) | 3.71 (n=20) | 1.21 | 0.473 | **2.6×** |
| CT↔G | 4.87 (n=10) | 2.51 (n=10) | 2.36 | 0.491 | **4.8×** |

**Verdict: PF_I is genuinely non-commutative.** All four reversed pairs show significant directional asymmetry. The weakest (G↔PT) is still 2.6× sigma. The strongest (G↔MdN) is 14.1× sigma.

**And it's not just PF_I.** Full metric breakdown shows MG, PF_E, CCI, and EDB also flip significantly on reversal for specific pairs. Example — CT↔MdN:

| Metric | CT→MdN | MdN→CT | Diff | ×σ |
|--------|--------|--------|------|-----|
| AR | 7.12 | 6.32 | 0.80 | 2.1× |
| CCI | 6.50 | 6.81 | 0.31 | 0.9× |
| EDB | 6.70 | 6.49 | 0.21 | 0.5× |
| MG | 7.05 | 4.82 | 2.23 | **6.2×** |
| PF_E | 7.21 | 4.54 | 2.68 | **5.8×** |
| PF_I | 4.85 | 8.07 | 3.21 | **5.4×** |

The structural pattern: when MdN is the SUBJECT (being scored), PF_I goes high (~8) because MdN's instrumental track record is its strongest suit. When MdN is the OPPONENT, PF_I goes low because the subject framework (CT, G) can't compete on empirical track record. This makes conceptual sense — and conceptual sense is what distinguishes structure from noise.

---

## 2. Noise-Floor Comparison: Composition Residuals vs σ

Used existing within-group SDs (pooled across all stances per metric) as the noise floor. Computed per-metric residual/σ ratios for each composition triple.

### Schema A — 9 triples (σ_pooled = 0.563)

| | Count | % |
|---|---|---|
| STRUCTURE (ratio > 1.5) | 0 | 0% |
| MARGINAL (1.0-1.5) | 2 | 22% |
| NOISE (ratio ≤ 1.0) | 7 | 78% |

**Schema A composition is indistinguishable from noise.** Zero triples exceed the noise floor at the 1.5× threshold.

### Schema B — 13 triples (σ_pooled = 0.409)

| | Count | % |
|---|---|---|
| STRUCTURE (ratio > 1.5) | 8 | 62% |
| MARGINAL (1.0-1.5) | 3 | 23% |
| NOISE (ratio ≤ 1.0) | 2 | 15% |

**Schema B composition is mostly structural.** 8/13 triples exceed the noise floor. The driving metrics are consistently MG, PF_E, PF_I, and CCI.

### Your Second Check: Common Triples Only (9 triples present in both schemas)

| Schema | STRUCTURE | MARGINAL | NOISE |
|--------|-----------|----------|-------|
| A | 0 | 2 | 7 |
| B | 6 | 2 | 1 |

**The noisier schema (A, σ=0.563) composes better (0% structural residuals — everything is within noise). The cleaner schema (B, σ=0.409) shows 67% structural residuals on the exact same triples.**

You flagged this as the strongest pro-structure evidence, and it survived the common-triples restriction.

---

## 3. What This Means

### Composition in Schema A: not a finding.

Test A's "78% approximate composition" in Schema A was noise. The composition model predicted within the instrument's replication error. The scores are too noisy (σ≈0.56) to distinguish composition from chance alignment.

### Composition in Schema B: real, driven by specific metrics.

8/13 triples show residuals that genuinely exceed the noise floor. The per-metric breakdown reveals which metrics drive the failure of composition:

- **PF_I:** appears in 9/8 STRUCTURE triples (the non-commutative asymmetry)
- **MG:** appears in 7/8 STRUCTURE triples
- **PF_E:** appears in 4/8 STRUCTURE triples
- **CCI, EDB:** appear in 5/8 STRUCTURE triples

These are the metrics where the midpoint model fails — where A→C is NOT the average of A→B and B→C. AR is the only metric that consistently composes within noise.

### The manifold hypothesis (revised):

The original "59% partial composition" was wrong in both directions:
- Schema A: **0% structural** (all noise)
- Schema B: **62% structural** (real, metric-specific)

The manifold doesn't live in "worldview space" generically. It lives specifically in the PF_I/MG/PF_E subspace of Schema B — the existential and instrumental dimensions of framework evaluation. Coherence (CCI) and explanatory depth (EDB) show intermediate non-composition. Aesthetic resonance (AR) composes cleanly.

---

## 4. Scorecard Update

| Prediction | Verdict | Notes |
|-----------|---------|-------|
| A′-1: σ(B) > σ(A) | **REJECTED** | Schema A is noisier (0.56 vs 0.41). Phase 2 anchors reduce ambiguity. |
| A′-2: σ(PF_I) largest in B | **CONFIRMED** | PF_I σ=0.507 vs next-highest PF_E σ=0.427 |
| A′-3: Residuals within 1.5σ | **SPLIT** | Schema A: YES (all noise). Schema B MdN legs: NO (8/13 structural). |
| Direction-reversal check | **NON-COMMUTATIVE** | All 4 reversed pairs significant (2.6× to 14.1×). |
| "Noisier composes better" | **CONFIRMED** | Survives common-triples restriction. |

**Opus track record updated: 2/5 on original predictions + the direction-reversal check produced the cleanest result of the session.**

---

## 5. Acknowledged Corrections

Per your directive:

1. **Nyquist paper argument struck.** Different measurand, different task, different failure modes. Within-group SDs are the correct noise floor. You were right.

2. **A′-3 threshold amended.** Three noisy legs → null should be σ√3 ≈ 0.71 for Schema B (not 1.5σ = 0.61). Under that corrected threshold, Schema B still shows 8/13 STRUCTURE (the ratios range from 2.0× to 3.4× — well above either threshold). The correction doesn't change the verdict.

3. **"Approximate composition" in Schema A retracted.** It was noise, as you suspected. The finding was an artifact of not reporting the noise floor alongside the result — exactly what "All Measured, All Floored" was written to prevent.

---

*Computed from 702 existing CFA runs, within-group SDs at n=10-22 per group. Test A′ (18 new runs) withdrawn per your approval.*
