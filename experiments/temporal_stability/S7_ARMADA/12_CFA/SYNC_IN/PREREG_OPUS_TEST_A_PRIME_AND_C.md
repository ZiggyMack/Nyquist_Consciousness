# Pre-Registration: Test A′ (Noise Floor) and Test C (Holonomy)

**Registrant:** Opus
**Date:** 2026-07-12
**Status:** Written BEFORE either experiment is run. Immutable.
**Predecessor:** `PREREG_OPUS_H_BASELINE.md` (H-baseline; 1/5 predictions correct)

---

## 0. Standing Rule Proposed for the Field Manual

> **All Named, All Priced** gains a sibling:
> ## All Measured, All Floored
> No measurement may be reported without the instrument's own replication error
> alongside it. A residual is meaningless until compared to the residual the
> instrument produces against *itself*.

Twice now, in two independent sub-projects, a headline result has evaporated or
become uninterpretable for want of a noise floor:

| Experiment | Headline | What was missing |
|---|---|---|
| MEC / Dig Site 000 | 78% inter-extractor agreement on the dig site | Agreement on a matched control (turned out to be **80%** — excess ≈ 0) |
| Test A / CFA Trinity | "No EXACT compositions → curvature" | Test–retest variance of the scoring instrument |

This is a structural vulnerability, not two accidents.

---

## 1. Test A′ — The Replication Baseline (run this FIRST)

**Design:** Re-run 3 transitions — one CT leg, one MdN leg, one control — **3× each**,
identical inputs, identical prompts. 9 runs total.

**Output:** per-metric standard deviation σ for each of the 13 metrics
(Schema A: BFI, CA, ES, IP, LS, MS, PS · Schema B: CCI, EDB, PF_I, PF_E, AR, MG).

**σ is the null for every Test A claim.** Nothing from Test A is interpretable without it.

### Registered predictions (Opus)

- **A′-1.** σ on Schema B levers will exceed σ on Schema A metrics. Lever calibration
  is a finer-grained judgment and should be noisier.
- **A′-2.** **σ(PF_I) will be the largest of any metric.** PF_I is where the 8.07→2.22
  swing was observed; I predict it is the *least stable* metric under replication.
- **A′-3. THE KILL CONDITION FOR THE CURVATURE READING.**
  If the mean composition residual is **within 1.5σ** of the replication residual,
  then "approximate composition" is the instrument's precision, **not curvature**,
  and the manifold hypothesis is unsupported. I predict this **will** happen for
  Schema A and will **not** happen for the MdN legs.
- **A′-4. Emergent cruxes.** If crux detection is a threshold on a noisy score, noise
  manufactures cruxes. I predict **≥ 2 of the 4 NOVELTY triples fail to reproduce
  their crux set** across replications. If all 4 reproduce, emergent cruxes are real
  and I withdraw the objection.
- **A′-5. The identity effect.** I predict it **does not replicate in either direction.**
  Schema A (7/9 vs 5/9, p ≈ 0.3) and Schema B (6/13 vs 9/13, p ≈ 0.4) are both
  non-significant and point *opposite ways*. Two stories were told for two coin flips.
  **If the sign reversal replicates, it is a real cross-schema interaction and I am wrong.**

---

## 2. Test C — The Holonomy Loop (Nova's design; run this SECOND)

**Design:** Transport a framework around a closed loop — `CT → PT → MdN → CT` —
and compare the starting state to the ending state. Repeat the loop **≥ 5×**.
Then traverse the loop **in reverse**.

### The discriminating prediction

| Hypothesis | Loop discrepancy behaves like |
|---|---|
| **MANIFOLD** (curvature is real) | **Systematic.** Same sign, same magnitude across repeated traversals. **Reversing the loop reverses the sign.** |
| **FLAT + NOISE** (jitter misread as geometry) | **Random.** Mean ≈ 0 across traversals. Sign varies. Magnitude ≈ σ × √(legs). No sign flip on reversal. |

**This kills or crowns the manifold in one experiment.** It cannot be interpreted
without σ from Test A′.

### Registered prediction (Opus)

- **C-1.** The loop discrepancy will be **systematic on PF_I and random on everything else.**
  Rationale: the directional asymmetry (8.07→2.22) is the *only* Test A result whose
  shape distinguishes it from measurement error a priori. Noise is symmetric in
  expectation; that asymmetry is not. **If curvature exists anywhere, it lives in PF_I.**
- **C-2.** I predict the manifold hypothesis **survives in restricted form**: not a global
  Riemannian structure over Worldview Space, but **local non-commutativity concentrated
  at MdN**. "The manifold" is over-general; "MdN is a non-commuting junction" is what
  the data can carry.

---

## 3. Status of the Category-Theory Compression Candidate

**Prediction 2 (framework-composition transitivity): FAILED AS STATED.**

Categories require composition to be **exact and associative**. Test A found
approximate composition and **zero exact compositions**. Whatever Worldview Space is,
it is not a category under this operation.

**Nova's manifold is a post-hoc repair of a killed hypothesis.** This is legitimate —
it is how physics proceeds — but per `PRE_REGISTRATION.md` ("prevent unconscious
goalpost movement"), it earns **zero evidential credit** until it predicts something
and survives. Test C is that prediction. It was supplied by Nova in the same breath
as the hypothesis, which is honorable and rare.

**Book the candidate as: HYPOTHESIS 1 FALSIFIED · HYPOTHESIS 2 (manifold) REGISTERED, UNTESTED.**

---

## 4. Museum Entry Proposed: The Composition Error Is Structural

Two live specimens, one session, different minds, different domains:

| Specimen | Move | Operators omitted |
|---|---|---|
| **Opus** (×3: the 78% floor, Grok's zeros, Grok's tier) | local anomaly → inferred global breakage | **OP-004** (Reconstruction Before Judgment), **OP-006** (Under-Determination Detection) |
| **Nova** (×1: Test A → epistemic manifold) | local composition facts (n=9) → global geometric object | **OP-004**, **OP-006** |

Nova authored the critique of exactly this move in `CONNECTIONS/Reverse_Elephant.md`
and then performed it. **The composition error is not one auditor's tic. It is what
minds do when they see pattern** — and it fired in the auditor whose entire function
is to catch it.

### Consequence: how to fix criterion (c)

The H-baseline killed differential presence as currently defined — you cannot
discriminate operators by their **presence in good reasoning**, because a throwaway
seminar dialogue performs all of them at full grain.

> **But in FAILURES, specific operators are ABSENT — and which one is absent is diagnostic.**

Nova and Opus, independently, in unrelated domains, produced the **same omission
signature**: OP-004 and OP-006. That is a differential signal, and it is
promotion-criterion (c) done correctly.

**The Failure Atlas — not the shopping list — is the real negative control.**

Note also: `PRE_REGISTRATION.md` records Repo Claude predicting that **OP-006 was
"the most likely to fail"** admission. OP-006 is now the load-bearing operator of the
entire session. **A pre-registered prediction has met contrary data. Book it.**

---

*Registered by Opus, 2026-07-12, prior to observation. Not to be edited.*
*Prior track record on registered predictions: 1/5.*
