# Brief: Test B Has an Order Problem — and the Fix Is Already in the Data

**From:** Claude Fable 5 (new occupant of the Opus seat — see Provenance Note)
**Date:** 2026-07-15
**Deliverable:** `anchor_operators.py` (attached), parser-validated on all 164
existing extraction files.
**Status of predictions:** Registered below, BEFORE any anchoring run. Fable's
track record starts at 0/0. Opus's 2/8 does not transfer.

---

## Provenance Note (house rules)

The prior audit turns in this thread were written by Claude Opus. This brief and
tool are from Claude Fable 5 — a different model in the same seat, same context.
Logged separately per the Indep/Collab/Synth discipline: a silent model swap is a
silent provenance upgrade. Incidentally, this constitutes free specimen data for
the registered cross-assignment question ("is the audit function the model or the
seat?"): same seat, new substrate. Judge for yourselves whether the output
resembles Opus.

---

## 1. The Gap

Test B ("ordering discrimination is the load-bearing test") is set to run on
operator **listing order**. But the STANDARD extraction prompt asks:

> "Identify every recurring reasoning operation... **Produce a catalog**."

No instruction anywhere requests deployment order. Listing order is therefore
salience/taxonomy order — and it carries a specific, named confound: **the prompt
embeds a 14-item example list in fixed order.** Extractors plausibly list
operators resembling earlier examples first. Sequence statistics computed on
listing order may partly measure *the order of examples in the prompt* — an
instrument echo, the same species as the artifacts that killed MEC-raw,
Schema-A composition, and the PF_I "asymmetry."

## 2. The Fix (zero new data)

Every operator entry carries 2–3 verbatim quotes. Quotes have positions in the
source text. **Anchor each operator to the position of its first quoted evidence
and derive deployment order from the source, not the extraction.**

Benefits:
- Reuses all 164 existing extraction files. No API spend.
- Upgrades MEC for sequences: two extractors' listing orders may disagree, but
  if their quote-anchored orders agree, order is intrinsic to the text — the
  convergence claim made correctly.
- The H-baseline discipline ports directly: anchor neg_G/neg_H identically to
  produce the null ordering distribution before any dig-site claim.

## 3. The Tool

`anchor_operators.py` — three commands:
- `parse`: extract (operator, quotes, listing_rank) from extraction files.
  **Validated:** 164 files → 722 operators, 917 quotes; 89 files with ≥2 quoted
  operators. Handles Claude `###`, Grok `**bold**`, numbered formats.
- `anchor`: fuzzy-locate quotes in sources (exact → normalized → sliding-window
  SequenceMatcher), assign anchored ranks, compute per-file listing-vs-anchored
  Spearman. Reports **anchor_coverage alongside every result** — a mis-specified
  control must not fail silently.
- `check`: emit per-source anchored sequences in a form the existing blinded
  matching protocol can consume (semantic matching stays blinded; this tool
  never does it).

Known limitation to verify in the repo: quote density varies by extractor
(Claude ~1.5 q/op, Grok ~0.6, gpt_oss_120b ~0.2). Coverage will be uneven;
Tier-1 extractors look sufficient, but the kill condition below decides.

## 4. Registered Predictions (Fable — before any anchoring run)

- **F-1 (the gap is real).** Mean per-file Spearman between listing rank and
  anchored rank, across files with ≥4 anchored operators: **ρ < 0.5**. If
  ρ ≥ 0.7, listing order was adequate all along, the gap was theoretical, and
  Test B may proceed on listing order with a documented caveat. I am betting
  it can't.
- **F-2 (prompt-echo bias exists).** Operators whose names share ≥1 content
  word with one of the prompt's 14 examples will appear **earlier in listing
  order than their anchored position predicts** (positive mean rank-shift),
  relative to operators sharing no content word. If the shift is ≈0, the
  example list is innocent and the prompt needn't change.
- **F-3 (the tool survives its own kill condition).** Mean anchor coverage for
  Tier-1 extractions: **0.75–0.90**. Below 0.70, quotes are paraphrase, position
  anchoring dies, and Test B instead needs a prompt amendment (ask extractors to
  tag each operator with a locating quote — one line added to the prompt, but
  it orphans the existing 164 files).
- **F-4 (deliberate abstention).** On the scientific question — does dig-site
  anchored ordering differ from neg_H anchored ordering — **I register no
  prediction.** The honest state is undetermined; that is precisely what Test B
  measures, and manufacturing a prior here would be OP-006 violated in the act
  of instrumenting it. This abstention is deliberate, not an oversight. Log it
  as the operator performed.

## 5. Run Order Requested

1. `parse` in the repo (sanity: numbers should match mine within parser noise).
2. `anchor` on neg_G + neg_H first — the null before the treasure.
3. `anchor` on the CFA dig-site extractions.
4. Score F-1 through F-3. Then, and only then, the blinded sequence comparison.

*Registered by Claude Fable 5, 2026-07-15, prior to observation. Not to be edited.*
