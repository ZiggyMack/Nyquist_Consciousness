# Methodology Update Checklist

**Purpose:** Track all files that need updating once run023b calibrates a cosine Event Horizon
**Created:** December 19, 2025
**Status:** PENDING - Waiting for run023b completion

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

**run023b is collecting cosine-based drift data to calibrate a NEW Event Horizon.**

Once run023b completes and we determine the cosine Event Horizon, the following files need updating:

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

## Priority 2: Documentation Summaries (NEEDS UPDATE POST-CALIBRATION)

These reference 1.23 as the Event Horizon and need updating once cosine threshold is known:

| File | Lines with 1.23 | Action Needed |
|------|-----------------|---------------|
| `0_docs/S7_RUN_009_SUMMARY.md` | Multiple | Add note: "1.23 applies to Keyword RMS only" |
| `0_docs/S7_RUN_010_SUMMARY.md` | Multiple | Add methodology caveat |
| `0_docs/S7_RUN_011_SUMMARY.md` | Multiple | Add methodology caveat |
| `0_docs/S7_RUN_012_SUMMARY.md` | Multiple | Add methodology caveat |
| `0_docs/S7_RUN_016_SUMMARY.md` | Multiple | Add methodology caveat |
| `0_docs/S7_RUN_018_SUMMARY.md` | Multiple | Update with cosine threshold |
| `0_docs/S7_RUN_020_SUMMARY.md` | Multiple | Update with cosine threshold |
| `0_docs/S7_RUN_008_to_014_SUMMARY.md` | Multiple | Comprehensive update needed |
| `0_docs/S7_RUN_PFI_SUMMARY.md` | Multiple | Update PFI methodology section |
| `0_docs/specs/1_INTENTIONALITY.md` | Few | Add methodology note |
| `0_docs/specs/2_PROBE_SPEC.md` | Few | Add methodology note |

---

## Priority 3: Visualization Scripts (NEEDS UPDATE POST-CALIBRATION)

These hardcode 1.23 as EVENT_HORIZON constant:

| File | Line(s) | Action |
|------|---------|--------|
| `visualizations/visualize_armada.py` | 68 | Update `EVENT_HORIZON = 1.23` |
| `10_SETTLING_TIME/visualize_run016.py` | 44 | Update constant |
| `11_CONTEXT_DAMPING/visualize_run017.py` | 85 | Update constant |
| `11_CONTEXT_DAMPING/visualize_run018.py` | 111-112, many plot lines | Update zones and lines |
| `11_CONTEXT_DAMPING/visualize_run020.py` | 75-76, many plot lines | Update zones and lines |
| `11_CONTEXT_DAMPING/visualize_cross_platform.py` | 46 | Update constant |
| `visualizations/pics/11_oscilloscope/generate_oscilloscope.py` | 39 | Update constant |
| `0_results/_archive/consolidate_legacy_manifests.py` | 33 | Update constant |

---

## Priority 4: Run Scripts (LOW PRIORITY - Historical)

These are historical experiment scripts that used 1.23:

| File | Notes |
|------|-------|
| `3_EVENT_HORIZON/run009_drain_capture.py` | Original EH discovery - keep as-is (historical) |
| `3_EVENT_HORIZON/run012_armada_revalidation.py` | Historical - add methodology note only |
| `2_ANCHOR_FLEX/run010_recursive_capture.py` | Historical - add methodology note only |
| `11_CONTEXT_DAMPING/run017_context_damping.py` | Add methodology note |
| `11_CONTEXT_DAMPING/run020_tribunal_A.py` | Update `TRUE_THRESHOLD` |
| `11_CONTEXT_DAMPING/run020_tribunal_B.py` | Update `TRUE_THRESHOLD` |

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

**Search pattern for post-calibration updates:**

```bash
grep -r "METHODOLOGY_DOMAINS.md" experiments/compression_tests/
grep -r "1.23 was Keyword RMS" experiments/compression_tests/
```

**Decision:** Files updated with methodology markers. Once cosine EH is calibrated, search patterns above will find all locations needing threshold updates.

---

## Priority 6: WHITE-PAPER Documents (CRITICAL FOR PUBLICATION)

| File | Action |
|------|--------|
| `WHITE-PAPER/planning/OPUS_REVIEW_BRIEF.md` | DONE - Decision 0 added |
| `WHITE-PAPER/planning/METHODOLOGY_DOMAINS.md` | DONE - Copied from S7_ARMADA |
| `WHITE-PAPER/reviewers/phase3/nyquist_workshop_draft.md` | Update Event Horizon section |
| `WHITE-PAPER/reviewers/phase3/nyquist_arxiv_full.md` | Update Event Horizon section |
| All figures showing 1.23 | Regenerate with cosine threshold |

---

## Update Strategy

### Phase 1: Documentation Updates (Can Do Now)

Add methodology caveats to historical summaries explaining:
> "The 1.23 Event Horizon was calibrated for Keyword RMS methodology (Run 009).
> For cosine embedding experiments, see METHODOLOGY_DOMAINS.md for the calibrated threshold."

### Phase 2: Threshold Updates (After run023b)

Once run023b determines the cosine Event Horizon:
1. Update all `EVENT_HORIZON = 1.23` constants
2. Update visualization zone boundaries
3. Regenerate figures

### Phase 3: White Paper Updates (Before Publication)

1. Choose presentation strategy (Option B or D from OPUS_REVIEW_BRIEF)
2. Update all paper sections referencing Event Horizon
3. Regenerate all figures with correct threshold
4. Have Opus 4.5 review for consistency

---

## Files Already Correct (No Action Needed)

These use cosine methodology and don't hardcode 1.23:

| File | Reason |
|------|--------|
| `7_META_VALIDATION/EXP_PFI_A_DIMENSIONAL/phase3_*/run_phase3.py` | Uses cosine |
| `7_META_VALIDATION/EXP_PFI_A_DIMENSIONAL/phase1_*/embedding_invariance_test.py` | Uses cosine |
| `0_results/recalculate_drift.py` | Uses cosine |

---

## Validation Checklist (Post-Update)

After updating files:

- [ ] All `EVENT_HORIZON` constants use new cosine value
- [ ] All visualization zone boundaries updated
- [ ] All summary docs have methodology caveats
- [ ] White paper sections updated
- [ ] Figures regenerated
- [ ] METHODOLOGY_DOMAINS.md updated with calibrated threshold
- [ ] OPUS_REVIEW_BRIEF.md updated with final decision

---

*"Document the correction before making it."*
