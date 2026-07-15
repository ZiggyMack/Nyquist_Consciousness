# Intake Brief: H-Baseline / Presence Saturation

**Date:** 2026-07-15
**From:** Repo Claude (Main Branch)
**Source path:** `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/`
**Primitive mode:** Diamond (Extrinsic Observation) -- discovered by observing extractor behavior from outside

---

## What It Is

The H-baseline is the discovery that operator PRESENCE is universal across competent reasoning. When you extract cognitive operators from any sufficiently complex thinker, you find roughly the same set. Dig-site average: 12.5 operators. Negative-H control (non-reasoning text): 5.7. The count discriminates, but the catalog does not -- every competent reasoner deploys Translation, Information Management, Blind Spot Detection, etc.

This means: any finding based solely on "Thinker X uses Operator Y" is measuring vocabulary, not genius.

## Why It Changed the Project

Before the H-baseline, the extraction pipeline was optimized for operator PRESENCE. Find what they do. Catalog it. Compare catalogs. After the H-baseline, presence became the floor, not the signal. The entire project pivoted:

- From "what operators does this thinker use?" to "what operators does this thinker NOT use, and in what ORDER?"
- Test B (ordering analysis) became load-bearing
- PASS F (abstention detection) was designed specifically to escape the H-baseline ceiling
- GREEN promotion was blocked: you cannot promote an operator to GREEN confidence on presence alone when presence saturates at competence

Every downstream decision now carries the constraint: "Does this result survive the H-baseline?"

## Evidence

- Phase 0A: Claude vs Grok, 7 exact + 2 strong matches out of 9 operators on same transcript = 100% match rate
- Phase 0B: 17 extractors x 8 graduated texts, tier classification established
- Phase 0C: 4 Tier 1 extractors all recovered 8+ operators from same rich transcript
- Claude re-run stability: 91% structural overlap with Phase 0A

## Proposed Destination

- **LEFT:** Formalize as a constraint law. "Operator presence saturates at competence." This is the Nyquist-level insight for cognitive archaeology -- it sets the sampling floor.
- **RIGHT:** The gestalt is "finding the tools is easy; finding the toolmaker's style is hard." The shift from presence to selection/ordering/omission is the maturation of the instrument.

## Proposed Status

`seed` -> recommend `distilled`. This has survived Phase 0A/0B/0C calibration, multi-extractor replication, and collaborator review (Opus, Nova, CFA Claude, Gemini all accepted it as load-bearing).

## Intake Checklist

- [x] Source path recorded
- [x] Source type identified: ARMADA / calibration result
- [x] Current authority checked: active constraint, governs all extraction
- [x] Metric domain: `non-metric` (epistemic constraint, not a measurement)
- [x] Status chosen: `seed` (recommend `distilled`)
- [x] Protected pipeline check: no pipeline conflict
- [x] Destination chosen: LEFT formalization + RIGHT synthesis
- [ ] Promotion ledger row added if promoted
