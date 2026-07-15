# Intake Brief: PASS F / Abstention Detection

**Date:** 2026-07-15
**From:** Repo Claude (Main Branch)
**Source path:** `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/TEMPLATES/`
**Primitive mode:** Diamond (Extrinsic Observation) -- observes what is MISSING from the outside

---

## What It Is

PASS F is a new museum-aware extraction pass that asks "what operators were available but NOT deployed?" It is the inverse of the standard blind extraction: instead of hiding the Museum catalog and asking what the thinker does, you show the extractor the full operator catalog and ask what the thinker did NOT do.

Abstention classification:

- **Deliberate refusal** -- thinker explicitly chose not to
- **Competing priority** -- another operator was chosen instead
- **True omission** -- no signal about why it was skipped

True omissions and deliberate refusals are the informative categories.

## Why It Changed the Project

PASS F is the instrument fix that responds to the H-baseline ceiling. If operator presence saturates at competence, the discriminating signal lives in:

1. **Selection** -- which operators from the universal set?
2. **Ordering** -- in what sequence? (Test B)
3. **Omission** -- what was available but not used? (PASS F)

Before PASS F, the extraction pipeline was entirely presence-optimized. Every prompt asked "what do they DO?" None asked "what did they NOT do?" The most informative signal was invisible to the instrument.

Calibration requirement (Opus): Run PASS F on negative-H control first. If it flags as many omissions in throwaway dialogue as in Barandes, the detector is measuring its own imagination. The CFA exhaust (diagnosed audit failures) serves as positive control -- transcripts where specific operator omissions were already traced to specific failures.

## Evidence

- Instrument built: `--abstention` flag in `extract_operators.py`, museum-aware prompt, negative control requirement
- Theoretical grounding: Nova's Missing Operator Theory (fallacies as operator omission signatures)
- Calibration: pending (negative control on neg_H, positive control on CFA exhaust)

## Proposed Destination

- **LEFT:** PASS F protocol specification. The pass ordering matters: PASS F runs AFTER blind extraction (PASS C) to avoid contaminating presence data.
- **RIGHT:** The gestalt is "what a thinker chooses NOT to do is as revealing as what they do." The negative space of reasoning.

## Proposed Status

`seed`. Instrument built but calibration not yet run. Promote to `distilled` after negative control passes.

## Intake Checklist

- [x] Source path recorded
- [x] Source type identified: instrument design + collaborator synthesis
- [x] Current authority checked: active, governs extraction protocol
- [x] Metric domain: `non-metric` (protocol, not a measurement value)
- [x] Status chosen: `seed`
- [x] Protected pipeline check: no pipeline conflict
- [x] Destination chosen: LEFT protocol + RIGHT synthesis
- [ ] Promotion ledger row added if promoted
