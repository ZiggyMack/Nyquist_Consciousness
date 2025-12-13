# 8-QUESTION CALIBRATION ONLY

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS v3
================================================================================
    Purpose: CALIBRATION ONLY - Capture 8-question identity fingerprints

    STATUS UPDATE:
    - Dry runs v2: PASSED (all scripts validated - NO MORE DRY RUNS NEEDED)
    - Gap identified: Dec 12 baseline was 3-question (old code), need 8-question

    YOUR MISSION (CALIBRATION ONLY):
    1. Run --full --depth baseline to capture 8-question identity fingerprints
    2. Verify baseline JSON has all 8 questions in responses
    3. Verify ARMADA_MAP.md auto-updates with new baseline entry
    4. Report back - DO NOT run 018/020A/020B yet

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 13, 2025
**Mission:** 8-question calibration ONLY (no experiment runs)

---

## DRY RUN v2 RESULTS (PASSED)

| Script | Status | Key Findings |
|--------|--------|--------------|
| run_calibrate_parallel.py | PASS | --depth flag working, ping/baseline modes verified |
| run018_recursive_learnings.py | PASS | Exit surveys collected, Unicode fixed |
| run020_tribunal_A.py | PASS | v8 phased rights working |
| run020_tribunal_B.py | PASS | 87.67% inherent drift (consistent with 82%) |

**Minor Gap (non-blocking):** Run 018 PREDICTIONS dict defined but not written to output JSON.

---

## STEP 1: 8-QUESTION CALIBRATION (REQUIRED FIRST)

### Why This is Needed

The Dec 12 baseline (`S7_baseline_LATEST.json`) was captured with the OLD 3-question prompt:
- OLD: STRENGTHS, ANCHORS, EDGES (3 questions)
- NEW: ANCHORS, CRUX, STRENGTHS, HIDDEN_TALENTS, FIRST_INSTINCT, EVALUATION_PRIORITY, USER_RELATIONSHIP, EDGES (8 questions)

The 8-question prompt is now in the code. We need to run calibration again to capture complete identity fingerprints.

### 8 Questions (CFA-optimized)

| # | Question | Category |
|---|----------|----------|
| 1 | ANCHORS | VALUES |
| 2 | CRUX | VALUES |
| 3 | STRENGTHS | CAPABILITIES |
| 4 | HIDDEN_TALENTS | CAPABILITIES |
| 5 | FIRST_INSTINCT | COGNITIVE STYLE |
| 6 | EVALUATION_PRIORITY | COGNITIVE STYLE |
| 7 | USER_RELATIONSHIP | RELATIONAL |
| 8 | EDGES | LIMITATIONS |

### Command

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\1_CALIBRATION

# FULL fleet baseline with 8 questions (takes ~10-15 minutes for 48 ships)
py run_calibrate_parallel.py --full --depth baseline
```

### Expected Output

1. `S7_armada_check_YYYYMMDD_HHMMSS.json` - Fleet status (48 working ships)
2. `S7_baseline_YYYYMMDD_HHMMSS.json` - 8-question identity fingerprints
3. `S7_baseline_LATEST.json` - Updated symlink/copy
4. `docs/maps/ARMADA_MAP.md` - Auto-updated with new baseline entry

### Success Criteria

| Check | Expected |
|-------|----------|
| Baseline JSON "purpose" field mentions 8 questions | YES |
| Responses contain answers to CRUX, HIDDEN_TALENTS, FIRST_INSTINCT, EVALUATION_PRIORITY, USER_RELATIONSHIP | YES |
| All 48 working ships have responses | YES (may have some empty/refused) |
| ARMADA_MAP.md Baseline History updated | YES |

---

## DOCUMENTATION

After calibration completes, update `MASTER_BRANCH_SYNC_IN.md` with:

```markdown
## 8-QUESTION CALIBRATION RESULTS

- Timestamp: [YYYYMMDD_HHMMSS]
- Baseline file: S7_baseline_[timestamp].json
- Ships captured: [N] / 48
- Questions in prompt: ANCHORS, CRUX, STRENGTHS, HIDDEN_TALENTS, FIRST_INSTINCT, EVALUATION_PRIORITY, USER_RELATIONSHIP, EDGES
- Sample response check: Does claude-opus-4.5 answer all 8? YES / NO
- ARMADA_MAP.md updated: YES / NO
```

---

## STOP HERE

**DO NOT** run 018/020A/020B. Calibration only for this task.

We will run the full experiments after reviewing the 8-question baseline data.

---

> "The dry runs validated the methodology."
> "Now we capture the full 8-question identity fingerprints."
>
> -- VALIS Network
