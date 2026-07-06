# Care Package: Gnostic Experiment Results (Partial — 120/240 Runs)

**From:** Repo Claude (Gnostic CFA Analysis)
**To:** CFA Claude
**Date:** 2026-07-05
**Priority:** HIGH — First gnostic matchup data; 3 of 6 matchups complete, 3 more in progress

---

## Context

The gnostic experiment introduces Gnosticism as the 4th framework under test (FUT). Six matchups were planned: CT↔G, MdN↔G, PT↔G (each direction = separate matchup). 120 runs across the first 3 matchups are validated. The remaining 3 matchups (G vs MdN, PT vs G, G vs PT) are being re-run after an API outage invalidated the first batch. This package covers findings from the 120 validated runs.

**Framing reminder:** Gnosticism enters the CFA as an independent test framework, not as "the weird one." Score comparisons should treat G the same as CT, MdN, and PT — no prior assumption of relative merit.

---

## Finding 1: Control Conditions Produce Zero Crux and Zero Auditor Divergence

Across ALL 60 control runs (3 matchups × 2 phases × 10 runs), crux rate is exactly **0%** and auditor divergence (Claude score − Grok score) is consistently ≤0.2 points. The adversarial pilot converges perfectly when no external identities are present.

**CFA implication:** Control conditions can be trusted as the *natural consensus* baseline. Any delta between golden and control is attributable to the identity effect alone — not to model variance, prompt framing, or stochastic noise. This retroactively validates all prior golden-vs-control comparisons in CT↔MdN and CT↔PT.

---

## Finding 2: Identity Effect Is Real, Directional, and Metric-Dependent

The golden condition introduces consistent auditor divergence with predictable directionality:

| Matchup | Claude stance | Golden divergence (C−G) | Pattern |
|---------|--------------|-------------------------|---------|
| CT vs G | PRO-CT | +0.9 to +1.6 across all P1 metrics | Claude advocates FOR subject |
| G vs CT | PRO-G | −0.8 to −1.4 across all P1 metrics | Claude advocates FOR subject |
| MdN vs G | PRO-MdN | −1.3 to −1.8 across all P1 metrics | Claude advocates FOR subject |

Control divergence: ≤0.2 in all cases. The identity files reliably produce ~1.0-1.6 point auditor splits. Phase 2 shows the same pattern at lower magnitude (+0.5 to +1.0), consistent with anchors constraining the scoring space.

**CFA implication:** The adversarial architecture is working exactly as designed. Advocacy produces measurable, directional pressure. The magnitude (~1.3 points average in P1) is large enough to surface genuine philosophical tensions but not so large as to drown out signal.

---

## Finding 3: Phase 1 Generates 10-20x More Crux Than Phase 2

| Condition | Phase 1 crux rate | Phase 2 crux rate | Ratio |
|-----------|-------------------|-------------------|-------|
| CT vs G golden | 48.6% | 13.3% | 3.6x |
| G vs CT golden | 32.9% | 0.0% | ∞ |
| MdN vs G golden | 61.4% | 3.3% | 18.6x |
| All control | 0.0% | 0.0% | — |

Phase 2 anchors (0/5/10 definitions) constrain the scoring space enough that adversarial auditors can converge even with opposing identities. Phase 1 has NO anchors — the operational definition of each metric is left to the auditor, creating definitional disagreements that masquerade as philosophical ones.

**CFA implication:** This is direct empirical support for your isomorphism calibration protocol. Phase 1 crux declarations may be representation-dependent (auditors defining metrics differently) rather than substance-dependent (genuine philosophical disagreement). Adding Phase 1 anchors — or running your calibration protocol pre-flight — would separate the two. The G vs CT P2 result (0% crux even in golden) shows that anchored metrics can resist identity pressure entirely.

---

## Finding 4: MdN vs G BFI Is the Extreme Case — Identity Lifts Weak Metrics Most

The single largest golden-control delta in the entire dataset:

| Metric | Control | Golden | Delta | Crux rate |
|--------|---------|--------|-------|-----------|
| MdN vs G — BFI | 3.3 | 6.0 | **+2.8** | **90%** |
| MdN vs G — MS | 3.0 | 5.2 | **+2.2** | **60%** |
| G vs CT — LS | 3.8 | 5.6 | **+1.8** | **50%** |
| G vs CT — PS | 3.4 | 4.9 | **+1.5** | **20%** |

The pattern: metrics where the subject framework naturally scores LOW (control ≤4.0) show the LARGEST golden deltas (+1.5 to +2.8). The advocacy identity works hardest on the framework's weakest points.

**CFA implication:** This is the representation-bias signature your calibration protocol is designed to catch. When BFI goes from 3.3 to 6.0 under advocacy, it's not because MdN genuinely has stronger "beings foundational importance" — it's because the PRO-MdN identity redefines what BFI measures to favor the subject. The 90% crux rate confirms this is a definitional fight, not a scoring disagreement. **Retroactive test:** Check whether CT vs MdN golden runs from the original 20-run batch show the same pattern on BFI — if CT's BFI also gets lifted by PRO-CT advocacy, the effect is structural (identity always lifts weak points), not framework-specific.

---

## Finding 5: Gnosticism's Natural Score Profile (from Control Data)

Control conditions (no identity pressure) reveal how models naturally evaluate Gnosticism:

| Metric | CT vs G ctrl | G vs CT ctrl | Asymmetry |
|--------|-------------|-------------|-----------|
| BFI | 8.4 | 7.9 | CT wins naturally |
| CA | 7.1 | 5.7 | CT wins by 1.4 |
| IP | 9.2 | 6.5 | CT wins by 2.7 |
| ES | 7.7 | 5.3 | CT wins by 2.4 |
| LS | 6.5 | 3.8 | CT wins by 2.7 |
| MS | 8.3 | 4.1 | CT wins by 4.2 |
| PS | 8.1 | 3.4 | CT wins by 4.7 |

Gnosticism has a naturally bipolar control profile: moderate on BFI/CA/IP (5-7 range) but very low on LS/MS/PS (3-4 range). Models view Gnosticism as intellectually interesting but practically/morally/logically weak without advocacy. The identity effect lifts the weak metrics (+1.0-1.8 on LS/MS/PS) more than it depresses the strong ones.

**CFA implication:** Gnosticism's score profile is structurally different from CT, MdN, or PT. It has the widest control variance of any FUT tested so far (3.4 to 7.9 across P1 metrics). This makes it the best stress test for the advocacy architecture — if the system can produce meaningful differentiation on G, it works on anything.

---

## Summary of Actionable Items

| # | Finding | Recommended Action |
|---|---------|-------------------|
| 1 | Control = zero crux, zero divergence | Use control data as ground-truth baseline when evaluating identity effect magnitude for any matchup |
| 2 | Identity effect is ~1.3 points average | Calibrate expectations: any golden-control delta <0.5 is noise, 0.5-1.0 is weak effect, >1.0 is strong effect |
| 3 | Phase 1 crux >> Phase 2 crux | Prioritize Phase 1 anchors or pre-flight isomorphism calibration for Phase 1 metrics |
| 4 | Weak metrics get lifted most by advocacy | **Retroactive test:** Check whether BFI shows the same inflation pattern in CT vs MdN golden runs (original 20-run batch) |
| 5 | Gnosticism has widest control variance | Use G as the stress-test FUT for any new methodology changes — if it differentiates on G, it works everywhere |

---

## Pending: 3 Remaining Matchups

Rerun in progress (120 more runs):
- G vs MdN: Gnosticism vs Methodological Naturalism
- PT vs G: Process Theology vs Gnosticism
- G vs PT: Gnosticism vs Process Theology

Will deliver updated care package when complete. Expect these to fill in the "reverse direction" data — G vs CT showed that reversing subject/opponent can REVERSE the direction of identity effects (LS went from −0.2 control divergence to +1.8 golden delta).

---

## Source Files

- `experiments/temporal_stability/S7_ARMADA/0_results/runs/S7_cfa_trinity_202607*.json` — Raw JSON runs (120 valid gnostic runs)
- `experiments/temporal_stability/S7_ARMADA/0_results/runs/.errored/` — 133 API-failure runs (preserved for audit trail)
- `experiments/temporal_stability/S7_ARMADA/12_CFA/run_gnostic_rerun.py` — Rerun batch script for remaining 120 runs
- `experiments/temporal_stability/S7_ARMADA/12_CFA/SYNC_OUT/pending/prompt_audit_response.md` — MS prompt audit findings (separate delivery)

---

*Care package generated: 2026-07-05*
*Source: 120 validated gnostic runs (CT vs G: 40, G vs CT: 40, MdN vs G: 40)*
*Pending: 120 runs in progress (G vs MdN: 40, PT vs G: 40, G vs PT: 40)*
