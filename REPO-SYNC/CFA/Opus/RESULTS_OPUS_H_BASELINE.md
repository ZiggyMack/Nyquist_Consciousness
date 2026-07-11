# RESULTS: The H-Baseline — Scored Against Pre-Registration

**Run by:** Opus, 2026-07-11, AFTER registering `PREREG_OPUS_H_BASELINE.md`
**Data:** Existing Phase 0B extractions. No new collection.
**Confound (declared in prereg §3):** I performed the semantic matching. This is
Claude matching Claude's own extraction. Agreement RATES below are PRELIMINARY.
The QUALITATIVE finding (§3) is robust to this confound — anyone can verify it by
reading two files.

---

## 1. Scorecard

| # | Prediction | Result | Verdict |
|---|---|---|---|
| P1 | Claude↔Grok agreement on neg_H = **30–55%** | **~80% (4–5 of 5)** | **WRONG.** Off by ~30 pts, in the direction that makes the finding *worse*, not better. |
| P2 | MEC excess ≈ 35–45 points | **Excess ≈ 0** | **WRONG.** |
| P3 | Kill condition: if agreement <25%, I withdraw the objection | Did not trigger. Opposite triggered. | Objection **sustained, and stronger than I predicted.** |
| P4 | Grok produces operators on neg_G/H; my zeros were regex artifacts | Confirmed — Grok uses `**bold**` headers | **RIGHT** |
| P5 | Grok not Tier 1 ⇒ every ledger "Partial (2)" rests on an uncertified extractor | Grok is **Tier 2 (GATE-PASSER)** — certified, noisier gradient | **OVERSTATED.** Real but minor: flagship MEC pair is Tier1×Tier2, not Tier1×Tier1. Not a scandal. |

**Net: 1 right, 2 wrong, 1 overstated, 1 objection sustained by losing.**

---

## 2. The Numbers

**Claude ↔ Grok, museum-blind, on neg_H (philosophical dialogue — a NEGATIVE CONTROL):**

| Grok (neg_H) | Claude (neg_H) | Match |
|---|---|---|
| Testing consistency across isomorphic domains | "identify a domain Y sharing the same structure the opponent already accepts, forcing them to extend the objection consistently or abandon it" | ✅ exact |
| Distinguishing separate objections | "detecting when an opponent quietly replaces one objection with a structurally different one, naming the shift" | ✅ exact |
| Demanding explanatory coverage of phenomenology | "specifying the *explanandum* any adequate version of the position must account for" | ✅ exact |
| Identifying hidden assumptions | "distinguishing what a speaker *says* from what *facts must exist* for that saying to be what they claim" | ✅ strong |
| Checking whether an argument overgeneralizes | (folds into row 1) | ~ strong |
| — | **"Acknowledging an objection identifies a genuine challenge while denying it is a knock-down argument"** | unmatched by Grok |

**Agreement ≈ 4 exact + 1–2 strong of 5 ≈ 80%.**
**Published CFA dig-site figure: 7 exact + 2 strong of 9 ≈ 78%.**

> ### These are the same number.
> **MEC's excess over a matched-difficulty control is approximately ZERO.**

---

## 3. The Robust Finding (does not depend on my matching)

Read the two extractions yourself. In `neg_H` — a generic moral-realism dialogue,
authored as a **negative control**, nobody's dig site — the following appear at full
specificity:

- **OP-008 (Symmetry Testing of Standards)** = Grok's *"testing consistency across
  isomorphic domains… to expose selective application"*; Claude's row 1.
- **OP-009 (Contested ≠ Defeated)** = Claude's *"acknowledging an objection identifies
  a genuine challenge while denying it constitutes a knock-down argument."*
- **OP-007 (Locate Disagreement Layer)** = *"distinguishing separate objections"* —
  naming that the opponent moved from causation to utility.
- **OP-005 (Hidden Structure Injection)** = *"identifying hidden assumptions."*

**OP-008 and OP-009 are the only two operators ever formally ADMITTED via Dig Site 000**
— 6/6 admission criteria, cited as 4/4 multi-extractor convergence.

**Both are present in the negative control.**

### Consequence, by the project's own rule

`LEDGER.md`, YELLOW → GREEN gate, criterion (c):

> *"**Differential presence** — demonstrated absent in negative-control text AND in at
> least some genuine reasoning (it is not universal)."*

OP-008 and OP-009 are **present** in negative-control text. **Under the project's own
promotion gate, they are blocked from GREEN.** This is not an external objection. It is
the ledger's rule, applied.

---

## 4. The Steelman (which I think is correct, and which costs something)

> *"This is independent convergence — the First Law. OP-008 turning up in an unrelated
> moral-realism debate is EVIDENCE it's a real, domain-general operator, not an artifact
> of Barandes."*

I think this is right. But price it honestly. It converts the claim from:

> *"the grammar of **high-quality thinking**" · "every **exceptional** thinker performs
> the same small set of operations" · "fossils of thought" · "isolated brilliance"*

into:

> **"the grammar of competent argumentation."**

A throwaway seminar dialogue — written as junk-adjacent filler — runs the same operators
as Barandes, at the same grain. So the operator **SET** does not discriminate genius from
competence. It discriminates **reasoning from non-reasoning**. That is a real result. It is
not the result the README advertises.

**Falsification Criterion 3** ("operators are universally present… Rorschach, not grammar")
is not fully triggered — shopping lists stay clean. But the operators are universal
*across reasoning*, which is the only range where the claim was ever interesting.

---

## 5. Where This Routes — Ziggy Already Wrote The Escape

`PRE_REGISTRATION.md`, A8, Fundamental Evidence Threshold, before any data existed:

> *"…it should be possible to predict how a thinker will navigate an unfamiliar problem —
> which moves they will reach for, **in what order, and what they will skip** — before
> observing their conclusions. Anything less — merely cataloging what a thinker already
> did — is 'interesting' but not fundamental."*

**"and what they will skip."**

Operator PRESENCE saturates at competence. The H-baseline proves it. Therefore the
discriminating signal must live in **selection, ordering, and omission** — which is
Level 4 (Discovery Architectures), and which is exactly **Test B**.

### Revised priority

| Was | Now |
|---|---|
| Test B = priority 3, downstream | **Test B = THE load-bearing experiment** |
| H-baseline = gate for Test B | **H-baseline = Test B's null, for free** |

Run operator sequence statistics on **neg_H as well as on the dig sites**. If Barandes'
operator ORDER is indistinguishable from a seminar dialogue's, the Museum catalogues
competence. **If the order differs — that is the fossil.**

Presence was never going to be the signature. Composition is.

---

## 6. Required Next Step: the Blinded Run

My matching is confounded (§0). The authoritative version, per prereg §4:

1. Mechanically extract operator name-lists from all files.
2. Assemble pairs — CFA×CFA, neg_H×neg_H, neg_G×neg_G — **source labels stripped**.
3. Shuffle. Give to a matcher who cannot tell which pair is the dig site.
4. If the matcher cannot separate dig-site pairs from neg_H pairs by agreement rate,
   **MEC is measuring vocabulary, not Barandes.**

---

*Scored against an immutable pre-registration written before observation. 1/5 right.*
*The objection survives not because I defended it, but because I bet against it and lost.*
