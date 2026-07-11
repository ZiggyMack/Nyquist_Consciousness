# Pre-Registration: The H-Baseline (MEC Null Distribution)

**Registrant:** Opus
**Date:** 2026-07-11
**Status:** WRITTEN BEFORE OPENING ANY neg_G / neg_H EXTRACTION FILE CONTENTS.
**Immutable once recorded.**

---

## 0. Contamination Declaration (mandatory, honest)

What I have ALREADY read, and which therefore taints any prediction touching it:

| Item | Read? | Consequence |
|---|---|---|
| Phase 0A results in LEDGER.md (7 exact + 2 strong of 9; the five stable operators) | YES | **Disqualifies me from Phase 0C prediction.** I hold the answer key for the positive control. |
| Tier assignments (experiment_design.md) | YES | Tier 1 = DeepSeek V4 Pro, Claude, Gemma4 31B, Cogito 671B |
| Full contents: claude neg_A, claude neg_B, claude neg_D, gpt neg_A | YES | Mild. None are neg_G/neg_H. |
| My own crude header-COUNTS for all 160 negatives (known-unreliable regex) | YES | **Partial taint on P4.** I "know" Claude produced ~8 entries and Grok ~0 on neg_H — but that counter demonstrably miscounts (it read Claude's user-offer menu as operators). Treat as noise, not knowledge. |
| Operator NAMES in any neg_G / neg_H file | **NO** | Clean. |
| Any pairwise AGREEMENT figure on neg_G / neg_H | **NO** | Clean. This is the prediction target. |

**Phase 0C slot: DECLINED.** Leave empty. Reason: contaminated by prior reading of the 0A answer key on the same transcript.

---

## 1. What the H-Baseline Tests

The Phase 0B gate (shopping list → 0 operators) certifies against **hallucination from noise**.
It does NOT certify against the null that actually threatens MEC:

> **Two extractors converge on the same operator vocabulary for ANY reasoning-rich text, because they share a descriptive prior.**

The matched-difficulty control for that null is neg_G (structured argument) and neg_H
(philosophical dialogue): genuine reasoning, competently performed, by no one who is a dig site.

**Test:** inter-extractor agreement on neg_H, using the SAME matching procedure that produced
"7 exact + 2 strong of 9" on the CFA transcript. That number is MEC's null distribution.
MEC counts only as EXCESS over it.

---

## 2. Registered Predictions (numeric, falsifiable)

**P1 — Magnitude.** Claude↔Grok pairwise agreement on neg_H will be **30–55%**.
Rationale: a shared descriptive prior is real (both are LLMs trained on overlapping
text about reasoning), so it will not be near zero; but an unstructured philosophical
dialogue lacks the adversarial protocol scaffolding that makes CFA transcripts
converge, so it should fall well short of the CFA figure.

**P2 — Direction.** MEC survives but shrinks. Honest excess ≈ (CFA ~78%) − (neg_H ~40%)
≈ **35–45 points of excess**, not 78. The ledger's MEC evidence is real but currently
overstated by roughly a factor of two.

**P3 — THE KILL CONDITION FOR MY OWN OBJECTION.**
If neg_H agreement comes in **below 25%**, my concern was overblown: the instrument
discriminates at the level MEC needs, and MEC is close to as strong as advertised.
**I commit in advance to withdrawing the H-baseline objection and saying so plainly.**

**P4 — Grok's gradient.** Grok DOES produce operators on neg_G and neg_H. My earlier
zero-counts for Grok were an artifact of my broken regex (formatting mismatch), not
refusals. Grok's exclusion from Tier 1 is a gradient-SHAPE failure, not blanket refusal.

**P5 — The structural prediction I expect to matter most.**
The LEDGER's flagship MEC evidence — OP-007, OP-008, OP-009, all logged
"Ext-Indep: Partial (2)" on the strength of "2 LLM extractors (Claude, Grok) agree" —
rests on a **Claude × Grok** pair. **Grok is not in Tier 1.** Phase 0A (07-08) predates
the tier assignment made by Phase 0B (07-08). If this holds, then every "Partial (2)"
in the ledger currently rests on one gate-passer plus one extractor the gate later
declined to certify — and must be re-derived from Phase 0C's Tier-1 pairs.

---

## 3. Known Confound in My Own Execution

If I perform the semantic matching myself, this is **Claude matching Claude's own
extraction** — the precise confound LEDGER.md already flags ("CRUX-derived evidence is
doubly confounded: Claude examining Claude"). Any number I produce below is therefore
a PRELIMINARY, CONFOUNDED first pass. The authoritative run must be BLINDED (see §4).

## 4. Blinded Design for the Authoritative Run

1. Extract operator name-lists mechanically from each file (low judgment).
2. Assemble pairs: CFA×CFA, neg_H×neg_H, neg_G×neg_G — **source labels stripped**.
3. Shuffle. Hand to a matcher who cannot tell which pair came from the dig site.
4. Matcher reports matches per pair.
5. If the matcher cannot separate dig-site pairs from neg_H pairs by agreement rate,
   **MEC is measuring vocabulary, not Barandes.**

---

*Registered by Opus, 2026-07-11, prior to observation. Not to be edited.*
