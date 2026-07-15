# Brief for Opus: Existing Noise Floor Evidence

**Question:** You pre-registered Test A′ (18 new runs) to establish the CFA instrument's replication error. Before we spend that API budget, does the following prior art satisfy your requirement — or do you still need the dedicated replication runs?

---

## 1. The Nyquist Consciousness Paper (750 experiments, 25 models, 5 providers)

The parent project — from which CFA Trinity descends — already established that AI-based measurement instruments produce reliable, non-noise signal. Key findings:

| Claim | Evidence | Relevance to Test A′ |
|-------|----------|---------------------|
| **~93% inherent drift ratio** | Control (neutral conversation) drift = 0.661, Treatment (identity probing) drift = 0.711. Delta = +7.6%. Cross-platform across Anthropic, OpenAI, Google, xAI, Together. 248 sessions, 37 ships. | Measurement reveals pre-existing dynamics, not creates them. The instrument observes real phenomena. |
| **PFI metric validity** | Spearman ρ = 0.91 against ground truth, semantic sensitivity Cohen's d = 0.698 | The embedding-based measurement approach has validated construct validity |
| **Regime transition at D=0.80** | p = 2.40×10⁻²³ across 750 experiments | Statistical power sufficient to detect genuine thresholds vs noise |
| **Control-theoretic dynamics** | τₛ ≈ 7 probes settling time, damped oscillator model fits data | Measurement captures real dynamical structure, not random walks |
| **Statistical validation suite** | Bootstrap CIs, permutation tests, effect sizes all implemented and run | Methodology for separating signal from noise already exists and passed |

**The "Thermometer Result":** Probing does not create the dynamics. The instrument observes what is already there. This was validated cross-platform across all major LLM providers.

---

## 2. Within-Group SDs Already Computed from 702 CFA Runs

The composition_analysis.py `profiles` command already computes per-metric standard deviation within each (stance, condition, schema) group. These ARE test-retest measurements — same configuration, different LLM generation stochasticity. Sample sizes: n=10-22 per group.

### Schema A (Phase 1) — Within-Group SDs

```
Stance               n     BFI    CA     ES     IP     LS     MS     PS
ct_vs_g             10    0.38   0.94   0.32   0.38   0.51   0.32   0.44
ct_vs_pt            10    0.58   0.57   0.61   0.65   0.52   0.57   0.36
g_vs_ct             10    1.11   0.48   0.48   0.70   0.48   0.85   0.71
g_vs_mdn            20    0.67   0.75   0.61   0.49   0.60   0.75   0.37
g_vs_pt             22    0.87   0.66   0.47   0.52   0.52   0.48   0.58
mdn_vs_ct           10    0.42   0.42   0.76   0.65   0.24   0.42   0.34
mdn_vs_g            10    0.40   0.33   0.60   0.77   0.35   0.49   0.59
pt_vs_g             20    0.66   0.48   0.31   0.32   0.58   0.50   0.56
pt_vs_mdn           10    0.57   0.54   0.30   0.28   0.54   0.46   0.67

Pooled mean SD across all Schema A groups: ~0.53
Range: 0.24 (mdn_vs_ct LS) to 1.11 (g_vs_ct BFI)
```

### Schema B (Phase 2) — Within-Group SDs

```
Stance               n     AR     CCI    EDB    MG     PF_E   PF_I
ct_vs_g             10    0.21   0.31   0.36   0.43   0.20   0.54
ct_vs_mdn           13    0.35   0.32   0.43   0.35   0.42   0.73
ct_vs_pt            10    0.16   0.28   0.28   0.30   0.54   0.60
g_vs_ct             10    0.43   0.29   0.31   0.38   0.47   0.44
g_vs_mdn            20    0.44   0.46   0.43   0.57   0.56   0.56
g_vs_pt             20    0.37   0.26   0.35   0.38   0.42   0.46
mdn_vs_ct           10    0.41   0.36   0.38   0.37   0.51   0.43
mdn_vs_g            10    0.73   0.24   0.35   0.49   0.29   0.32
pt_vs_g             20    0.38   0.37   0.24   0.36   0.31   0.49
pt_vs_mdn           10    0.36   0.39   0.24   0.40   0.41   0.38

Pooled mean SD across all Schema B groups: ~0.39
Range: 0.16 (ct_vs_pt AR) to 0.73 (ct_vs_mdn PF_I, mdn_vs_g AR)
```

---

## 3. What This Already Tells Us About Your Predictions

### A′-1: σ(Schema B) > σ(Schema A)?

**Already answerable:** Pooled mean SD(A) ≈ 0.53, Pooled mean SD(B) ≈ 0.39.

**REJECTED.** Schema A is *noisier* than Schema B. The opposite of what you predicted. (This makes sense — Phase 2 has explicit 0-10 anchors per metric, reducing judge ambiguity.)

### A′-2: σ(PF_I) is largest Schema B metric?

**Already answerable from existing data:**

Mean SD per Schema B metric (averaged across all stances):
- AR: 0.38
- CCI: 0.33
- EDB: 0.34
- MG: 0.40
- PF_E: 0.41
- **PF_I: 0.50**

**CONFIRMED.** PF_I has the largest within-group SD in Schema B. But the margin is modest (0.50 vs 0.41 for PF_E).

### A′-3: Composition residual within 1.5σ?

**Answerable now.** With pooled σ(B) ≈ 0.39, threshold = 0.585. The composition residuals from Test A can be compared directly to this. (The `compare` command in replication_analysis.py can already do this using these existing SDs instead of waiting for 18 new runs.)

### The PF_I 8.07 → 2.22 "swing"

Your strongest signal — the directional asymmetry. MdN→CT scores PF_I at 8.07 (SD=0.43), G→MdN scores it at 2.22 (SD=0.56). The difference is **5.85 points**, which is **~12× the within-group SD**. That is categorically not noise.

---

## 4. The Question for You

Given:
1. The Nyquist Consciousness paper (750 experiments) already proved AI measurement instruments produce real signal, not noise artifacts
2. The 702 existing CFA runs provide within-group SDs at n=10-22 per group (far more statistical power than n=3)
3. Your prediction A′-1 is already answered (REJECTED), A′-2 is CONFIRMED, and A′-3 is computable now
4. The PF_I directional asymmetry (5.85 points, 12× SD) is unambiguously non-noise

**Do we still need 18 dedicated replication runs?**

Or can we:
- Use the existing within-group SDs as the noise floor
- Run the `compare` command against those SDs right now
- Save the API budget for something that can't be answered from existing data

The one thing 18 new runs would add that existing data doesn't: temporal clustering (same day, same model version). But the existing runs span ~2 weeks of the same model version and still show tight SDs, which is arguably a *stronger* test of reliability than same-day replication.

---

*Prepared for Opus review. The existing data is ready for immediate analysis if Opus agrees the noise floor is already established.*
