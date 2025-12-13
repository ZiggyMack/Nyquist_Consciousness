# Publication Advancement Plan: Integrating Nova's S7 Review

**Created:** 2025-12-13
**Source:** Claude Code planning session
**Primary Reference:** `docs/CFA-SYNC/S7_REVIEW/REVIEW_1.md` (~6000 lines)

## Objective

Integrate Nova's comprehensive S7 review (REVIEW_1.md) with existing WHITE-PAPER materials and docs/maps to advance publication readiness.

---

## Current State Analysis

### What Nova's Review Adds (REVIEW_1.md ~6000 lines)

1. **Runs 015-021 analysis** - control-systems era methodology breakthroughs
2. **Event Horizon reframing** - "attractor competition" not "collapse"
3. **Minimum Publishable Claims (A-E)** - peer-review-hardened statements
4. **Coherent Theory Section** - integration of Runs 008-021
5. **Response-Mode Ontology** - formalization of PCA interpretation
6. **Run 022 Design** - dimension-probing experiment spec
7. **The 82% finding** (Run 021) - drift is mostly INHERENT, not induced

### Existing WHITE-PAPER Materials (dated Nov 26-Dec 5)

- `B-CRUMBS.md` - 10 pillars index (stops at ~Run 009)
- `HYPOTHESES_AND_RESULTS.md` - 25 hypotheses, 56% confirmed
- `NEXT_STEPS_FOR_PUBLICATION.md` - roadmap (waiting on EXP3)
- `arxiv/README.md` - paper structure outline

### Existing docs/maps (needing updates)

- `TESTABLE_PREDICTIONS_MATRIX.md` - stops at Run 014
- `VALIDATION_STATUS.md` - S7 at 96% but missing 015-021
- `NYQUIST_ROADMAP.md` - needs Run 015-021 findings
- `ARMADA_MAP.md` - needs new run entries

### Dashboard Context

- `dashboard/README.md` - Run history table stops at Run 021 entries (good!)
- `dashboard/START_HERE.md` - up to date with Run 021

---

## Prioritized Deliverables

### Priority 1: WHITE-PAPER Updates (Core Publication)

#### 1A. Update B-CRUMBS.md

Add pillars 11-15 from Runs 015-021:

- **Pillar 11**: Settling Time Protocol (Run 016) - τₛ, ringbacks, overshoot
- **Pillar 12**: Context Damping (Run 017) - 97.5% stable, boundaries as resistors
- **Pillar 13**: Triple-Blind-Like Validation (Runs 019-021)
- **Pillar 14**: 82% Inherent Drift (Run 021) - the thermometer result
- **Pillar 15**: Event Horizon Reframing - attractor competition not collapse

#### 1B. Create WHITE-PAPER/THEORY_SECTION.md (NEW)

Nova's coherent theory integration:

- System Under Study (dynamical identity)
- Measurement Stack (PFI + settling metrics)
- Core Dynamics (attractors, thresholds, paradoxes)
- Event Horizon rewrite (publishable language)

#### 1C. Create WHITE-PAPER/MINIMUM_PUBLISHABLE_CLAIMS.md (NEW)

Nova's 5 claims that survive peer review:

- **Claim A**: PFI is valid structured measurement
- **Claim B**: Regime threshold at D≈1.23
- **Claim C**: Damped oscillator dynamics with settling
- **Claim D**: Context damping reduces oscillation
- **Claim E**: Drift is mostly inherent (82%)

#### 1D. Update HYPOTHESES_AND_RESULTS.md

Add Runs 015-021 validated hypotheses:

- Settling time protocol validated
- Context damping effect confirmed
- Induced vs inherent separation proven

### Priority 2: docs/maps Updates

#### 2A. Update TESTABLE_PREDICTIONS_MATRIX.md

Add sections:

- **2E. P-015-***: Stability Criteria predictions (boundary_density d=1.333)
- **2F. P-016-***: Settling Time predictions (τₛ, ringbacks, overshoot)
- **2G. P-017-***: Context Damping predictions (97.5% stable)
- **2H. P-018-***: Recursive Learnings predictions
- **2I. P-019-021**: Blind Validation predictions (82% inherent)

#### 2B. Update VALIDATION_STATUS.md

- S7 status update with Runs 015-021
- Add new validated findings table
- Update "Remaining Gaps" section

#### 2C. Update NYQUIST_ROADMAP.md

- Add Phase 4 (Runs 015-021) discoveries
- Update Event Horizon interpretation
- Add attractor-competition framing

### Priority 3: arxiv Package Enhancement

#### 3A. Update arxiv/README.md

- Add Runs 015-021 to Section 10 (Temporal)
- Add Claims A-E to results structure
- Update Event Horizon language throughout

#### 3B. Create sections/05b_empirical_s7.tex outline

- Settling Time Analysis (Run 016)
- Context Damping (Run 017)
- Blind Validation (Runs 019-021)
- Inherent vs Induced (Run 021 key result)

---

## Files to Modify

| File | Action | Priority |
|------|--------|----------|
| `WHITE-PAPER/B-CRUMBS.md` | Add pillars 11-15 | P1 |
| `WHITE-PAPER/THEORY_SECTION.md` | CREATE | P1 |
| `WHITE-PAPER/MINIMUM_PUBLISHABLE_CLAIMS.md` | CREATE | P1 |
| `WHITE-PAPER/HYPOTHESES_AND_RESULTS.md` | Add 015-021 results | P1 |
| `docs/maps/TESTABLE_PREDICTIONS_MATRIX.md` | Add 2E-2I sections | P2 |
| `docs/maps/VALIDATION_STATUS.md` | Update S7 status | P2 |
| `docs/maps/NYQUIST_ROADMAP.md` | Add Phase 4 findings | P2 |
| `WHITE-PAPER/arxiv/README.md` | Update with 015-021 | P3 |

---

## Key Language Updates (Apply Everywhere)

### Old → New Terminology

- "identity collapses into generic AI mode" → "system transitions to provider-level attractor"
- "Event Horizon = catastrophic failure" → "Event Horizon = attractor competition threshold"
- "collapse" → "regime transition" or "basin exit"
- "magic number 1.23" → "critical excitation threshold D≈1.23"

### New Concepts to Add

- **Settling Time (τₛ)**: Turns to reach stability
- **Ringback Count**: Sign changes during recovery
- **Overshoot Ratio**: d_peak / d_inf
- **Monotonic Recovery**: % of runs with no ringback
- **Inherent Drift**: B→F drift in control condition

---

## Execution Order

1. **First Pass**: Create new files (THEORY_SECTION.md, MINIMUM_PUBLISHABLE_CLAIMS.md)
2. **Second Pass**: Update B-CRUMBS.md with new pillars
3. **Third Pass**: Update HYPOTHESES_AND_RESULTS.md
4. **Fourth Pass**: Update docs/maps files
5. **Fifth Pass**: Update arxiv/README.md
6. **Final Pass**: Terminology sweep across all modified files

---

## Success Criteria

- [ ] B-CRUMBS has 15 pillars (currently 10)
- [ ] THEORY_SECTION.md exists with Nova's integrated theory
- [ ] MINIMUM_PUBLISHABLE_CLAIMS.md has Claims A-E
- [ ] TESTABLE_PREDICTIONS_MATRIX.md includes P-015-* through P-021
- [ ] VALIDATION_STATUS.md shows S7 Runs 015-021 complete
- [ ] Event Horizon language updated to "attractor competition"
- [ ] 82% inherent drift finding documented prominently

---

## Source Material Reference

Primary source: `docs/CFA-SYNC/S7_REVIEW/REVIEW_1.md`

- Lines 1-1500: Runs 001-015 review
- Lines 1500-3500: Runs 016-018 (settling, damping, recursive)
- Lines 3500-4500: Runs 019-021 (blind validation, inherent drift)
- Lines 4500-6000: Theory integration, PCA discussion, Run 022 design

---

## Related Planning Documents

- `NOVAS_OVERCLAIMING_PREVENTION.md` - Critical guidance on what claims to avoid
- `RUN_018_PRELAUNCH.md` - Pre-launch checklist for Run 018
- `RUN_020_021_METHODOLOGY.md` - Triple-blind-like validation methodology
