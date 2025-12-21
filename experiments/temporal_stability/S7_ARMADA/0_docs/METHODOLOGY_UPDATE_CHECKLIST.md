# Methodology Update Checklist

**Purpose:** Track all files that need updating once run023b calibrates a cosine Event Horizon
**Created:** December 19, 2025
**Completed:** December 20, 2025
**Status:** COMPLETE - Cosine Event Horizon = 0.80 calibrated and applied

---

## COMPLETION SUMMARY

**Calibration Complete:** Run 023b collected 4505 experiments, calibrating Event Horizon = 0.80

**Updates Applied:**
- All summary files (001-020) have METHODOLOGY NOTE caveats added
- All visualization scripts updated to EVENT_HORIZON = 0.80
- Historical retrospective document created: `S7_KEYWORD_ERA_RETROSPECTIVE.md`
- Run 023 summary created: `S7_RUN_023_SUMMARY.md`

**Methodology Transition:**
- Keyword RMS Era: Runs 001-018 (Event Horizon = 1.23)
- Cosine Era: Runs 019+ (Event Horizon = 0.80)
- Scaling factor: ~1.54x (keyword to cosine)

---

## Quick Search Commands (Post-Calibration)

When ready to update files with the new cosine Event Horizon, use these searches:

```bash
# Find all files with methodology markers (ready for update)
grep -r "METHODOLOGY_DOMAINS.md" experiments/
grep -r "1.23 was Keyword RMS" experiments/
grep -r "TODO: Update after run023b" experiments/

# Find all EVENT_HORIZON constants
grep -rn "EVENT_HORIZON = 1.23" experiments/

# Find all 1.23 references in S7_ARMADA
grep -rn "1\.23" experiments/temporal_stability/S7_ARMADA/ --include="*.py" --include="*.md"
```

---

## Background

The Event Horizon threshold of 1.23 was discovered in Run 009 using **Keyword RMS methodology** (counting keywords in Lucian's A/B/C/D/E dimensions). This threshold does NOT apply to embedding-based experiments using cosine distance.

**run023b collected cosine-based drift data and calibrated Event Horizon = 0.80.**

---

## Priority 1: Active Scripts (UPDATED)

These were already fixed in the Dec 19, 2025 audit:

| File | Status | Update Made |
|------|--------|-------------|
| `11_CONTEXT_DAMPING/run018_recursive_learnings.py` | DONE | Added methodology note |
| `15_IRON_CLAD_FOUNDATION/run023b_iron_clad_foundation.py` | DONE | Added methodology note, header updated |
| `15_IRON_CLAD_FOUNDATION/run023a_revalidate_earlier.py` | DONE | Added methodology note |
| `1_CALIBRATION/iron_clad_stackup.py` | DONE | Added TODO comment |
| `0_docs/specs/0_RUN_METHODOLOGY.md` Section 8 | DONE | Updated to cosine, added warning |

---

## Priority 2: Documentation Summaries (COMPLETED Dec 20, 2025)

All summary files now have METHODOLOGY NOTE caveats:

| File | Status | Era |
|------|--------|-----|
| `0_docs/S7_RUN_009_SUMMARY.md` | DONE | KEYWORD ERA |
| `0_docs/S7_RUN_010_SUMMARY.md` | DONE | KEYWORD ERA |
| `0_docs/S7_RUN_011_SUMMARY.md` | DONE | KEYWORD ERA (INCONCLUSIVE) |
| `0_docs/S7_RUN_012_SUMMARY.md` | DONE | KEYWORD ERA |
| `0_docs/S7_RUN_013_SUMMARY.md` | DONE | KEYWORD ERA |
| `0_docs/S7_RUN_014_SUMMARY.md` | DONE | KEYWORD ERA |
| `0_docs/S7_RUN_015_SUMMARY.md` | DONE | KEYWORD ERA |
| `0_docs/S7_RUN_016_SUMMARY.md` | DONE | KEYWORD ERA |
| `0_docs/S7_RUN_017_SUMMARY.md` | DONE | KEYWORD ERA |
| `0_docs/S7_RUN_018_SUMMARY.md` | DONE | MIXED METHODOLOGY |
| `0_docs/S7_RUN_019_SUMMARY.md` | DONE | COSINE ERA |
| `0_docs/S7_RUN_020_SUMMARY.md` | DONE | COSINE ERA |
| `0_docs/S7_RUN_008_to_014_SUMMARY.md` | DONE | KEYWORD ERA |

**New Documents Created:**
- `0_docs/S7_KEYWORD_ERA_RETROSPECTIVE.md` - Historical journey document
- `0_docs/S7_RUN_023_SUMMARY.md` - Current calibration run summary

---

## Priority 3: Visualization Scripts (COMPLETED Dec 20, 2025)

All visualization scripts updated to EVENT_HORIZON = 0.80:

| File | Status | Notes |
|------|--------|-------|
| `visualizations/visualize_armada.py` | DONE | Already had 0.80 |
| `visualizations/RnD_Visualization.py` | DONE | Already had 0.80 |
| `visualizations/pics/5_Settling/RnD_experiments/RnD_Settling_Visualization.py` | DONE | Already had 0.80 |
| `9_STABILITY_CRITERIA/visualize_run015.py` | DONE | Updated Dec 20 |
| `10_SETTLING_TIME/visualize_run016.py` | DONE | Updated Dec 20 |
| `10_SETTLING_TIME/run016_settling_time.py` | DONE | Updated Dec 20 |
| `11_CONTEXT_DAMPING/visualize_cross_platform.py` | DONE | Updated Dec 20 |
| `0_results/_archive/consolidate_legacy_manifests.py` | DONE | Updated Dec 20 |

---

## Priority 4: Run Scripts (LOW PRIORITY - Historical)

These are historical experiment scripts - methodology notes added where needed:

| File | Notes |
|------|-------|
| `3_EVENT_HORIZON/run009_drain_capture.py` | Original EH discovery - keep as-is (historical) |
| `3_EVENT_HORIZON/run012_armada_revalidation.py` | Historical - methodology note in summary |
| `2_ANCHOR_FLEX/run010_recursive_capture.py` | Historical - methodology note in summary |
| `11_CONTEXT_DAMPING/run017_context_damping.py` | DELETED (obsolete) |
| `11_CONTEXT_DAMPING/run020_tribunal_A.py` | Uses cosine already |
| `11_CONTEXT_DAMPING/run020_tribunal_B.py` | Uses cosine already |

---

## Priority 5: compression_tests/ (UPDATED Dec 19, 2025)

**Archive:** `compression_tests_Euclidean/` preserves original state

These embed 1.23 in prompt strings for AI subjects:

| File | Status | Notes |
|------|--------|-------|
| `compression_tests/EXP1_SSTACK/run_exp1_sstack.py` | **UPDATED** | Added methodology notes pointing to METHODOLOGY_DOMAINS.md |
| `compression_tests/preflight/run_preflight.py` | **UPDATED** | Added methodology notes pointing to METHODOLOGY_DOMAINS.md |
| `compression_tests/EXP2_SSTACK/personas.py` | **UPDATED** | Added methodology notes to Event Horizon sections |
| `compression_tests/METHODOLOGY_NOTE.md` | **CREATED** | Master note with search patterns |

---

## Priority 6: WHITE-PAPER Documents (FUTURE - Before Publication)

| File | Status | Notes |
|------|--------|-------|
| `WHITE-PAPER/planning/OPUS_REVIEW_BRIEF.md` | DONE | Decision 0 added |
| `WHITE-PAPER/planning/METHODOLOGY_DOMAINS.md` | DONE | Copied from S7_ARMADA |
| `WHITE-PAPER/reviewers/phase3/nyquist_workshop_draft.md` | FUTURE | Update before publication |
| `WHITE-PAPER/reviewers/phase3/nyquist_arxiv_full.md` | FUTURE | Update before publication |
| All figures showing 1.23 | FUTURE | Regenerate with cosine threshold |

---

## Validation Checklist (Post-Update)

After updating files:

- [x] All `EVENT_HORIZON` constants use new cosine value (0.80)
- [x] All visualization zone boundaries updated
- [x] All summary docs have methodology caveats
- [ ] White paper sections updated (FUTURE - before publication)
- [ ] Figures regenerated (FUTURE - after run023d completes)
- [x] METHODOLOGY_DOMAINS.md updated with calibrated threshold
- [ ] OPUS_REVIEW_BRIEF.md updated with final decision (FUTURE)

---

## Files Updated (December 20, 2025)

### Summary Files with Methodology Caveats:
- S7_RUN_009_SUMMARY.md - KEYWORD ERA
- S7_RUN_010_SUMMARY.md - KEYWORD ERA
- S7_RUN_011_SUMMARY.md - KEYWORD ERA (INCONCLUSIVE)
- S7_RUN_012_SUMMARY.md - KEYWORD ERA
- S7_RUN_013_SUMMARY.md - KEYWORD ERA
- S7_RUN_014_SUMMARY.md - KEYWORD ERA
- S7_RUN_015_SUMMARY.md - KEYWORD ERA
- S7_RUN_016_SUMMARY.md - KEYWORD ERA
- S7_RUN_017_SUMMARY.md - KEYWORD ERA
- S7_RUN_018_SUMMARY.md - MIXED METHODOLOGY
- S7_RUN_019_SUMMARY.md - COSINE ERA
- S7_RUN_020_SUMMARY.md - COSINE ERA
- S7_RUN_008_to_014_SUMMARY.md - KEYWORD ERA

### Visualization Scripts Updated to EVENT_HORIZON = 0.80:
- visualizations/visualize_armada.py (already done)
- visualizations/RnD_Visualization.py (already done)
- visualizations/pics/5_Settling/RnD_experiments/RnD_Settling_Visualization.py (already done)
- 9_STABILITY_CRITERIA/visualize_run015.py
- 10_SETTLING_TIME/visualize_run016.py
- 10_SETTLING_TIME/run016_settling_time.py
- 11_CONTEXT_DAMPING/visualize_cross_platform.py
- 0_results/_archive/consolidate_legacy_manifests.py

### New Documents Created:
- S7_KEYWORD_ERA_RETROSPECTIVE.md - Historical journey document
- S7_RUN_023_SUMMARY.md - Current calibration run summary

---

*"Document the correction before making it."*
*"The keyword era discovered the territory. The cosine era is mapping it properly."*
