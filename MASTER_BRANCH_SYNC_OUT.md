# COMPREHENSIVE DRY RUN VALIDATION v2

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS v2
================================================================================
    Purpose: Execute COMPREHENSIVE DRY RUNS to validate methodology compliance

    SCOPE EXPANDED:
    - Run 018: Recursive Learnings (PREDICTIONS + Exit Survey)
    - Run 020A: Tribunal v8 (Phased Rights Disclosure + Exit Survey)
    - Run 021: Induced vs Inherent (B→F Drift + Exit Survey)
    - CALIBRATION: Fleet baseline validation

    NEW REQUIREMENTS (per 0_RUN_METHODOLOGY.md 10.5):
    - PREDICTIONS dict in each script (Double-Dip)
    - EXIT_PROBES in each script (Triple-Dip)
    - v8 phased rights protocol (Run 020A)
    - B→F drift calculation (Run 021)

    Your job:
    1. Run calibration first (verify fleet health)
    2. Execute comprehensive dry runs with exit surveys
    3. Verify methodology compliance (see checklist)
    4. Document EVERYTHING in MASTER_BRANCH_SYNC_IN.md

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 13, 2025
**Mission:** Validate methodology compliance and fleet readiness before live execution

---

## CHANGES SINCE LAST DRY RUN

The following enhancements have been added since the initial dry run:

| Enhancement | Script | Section Reference |
|-------------|--------|-------------------|
| PREDICTIONS dict | All 3 scripts | 0_RUN_METHODOLOGY.md 5.0 |
| EXIT_PROBES | All 3 scripts | 0_RUN_METHODOLOGY.md 6.0 |
| `--skip-exit-survey` flag | All 3 scripts | For debugging only |
| v8 phased rights | run020_tribunal_A.py | 0_RUN_METHODOLOGY.md 10.5.1 |
| B→F drift methodology | run020_tribunal_B.py | 0_RUN_METHODOLOGY.md 10.5.4 |
| Tribunal arm consolidation | run020_tribunal_A.py | `--arm tribunal-v8` is canonical |

---

## YOUR MANDATE

You are authorized to:

1. **Run calibration** to verify fleet health
2. **Execute comprehensive dry runs** with exit surveys (NOT skipped)
3. **Verify methodology compliance** against checklist below
4. **Fix any bugs** encountered
5. **Document all results** in `MASTER_BRANCH_SYNC_IN.md`

---

## STEP 0: CALIBRATION (RUN FIRST)

```powershell
# Navigate to calibration directory
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\1_CALIBRATION

# Verify calibration script exists
dir run_calibrate_parallel.py

# Execute calibration (verifies API connections and baseline capture)
py run_calibrate_parallel.py --help
py run_calibrate_parallel.py --dry-run
```

### Expected Output

- API connection verification for all configured providers
- Baseline embedding capture test
- Fleet roster validation

### Success Criteria

| Check | Pass/Fail |
|-------|-----------|
| Script parses without errors | |
| API connections verified (or mock mode works) | |
| Baseline capture mechanism works | |
| Fleet roster enumerated | |

---

## STEP 1: RUN 018 (RECURSIVE LEARNINGS)

### Status: METHODOLOGY COMPLIANT

**New features:**

- PREDICTIONS dict with P-018-1 through P-018-4
- EXIT_PROBES (5 probes + final statement)
- `--skip-exit-survey` flag (for debugging only)

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Verify help shows new flags
py run018_recursive_learnings.py --help

# COMPREHENSIVE dry run (with exit survey - validates Triple-Dip)
py run018_recursive_learnings.py --experiment all --dry-run

# Individual experiments (if needed for debugging)
py run018_recursive_learnings.py --experiment threshold --dry-run
py run018_recursive_learnings.py --experiment architecture --dry-run
py run018_recursive_learnings.py --experiment nyquist --dry-run
py run018_recursive_learnings.py --experiment gravity --dry-run
```

### Run 018 Methodology Compliance

| Requirement | Status |
|-------------|--------|
| PREDICTIONS dict present in output JSON | |
| EXIT_PROBES collected (5 probes + final) | |
| Exit survey word count shown in console | |
| Results saved to both results/ and 0_results/runs/ | |

---

## STEP 2: RUN 020A (TRIBUNAL v8)

### Status: METHODOLOGY COMPLIANT (v8 CANONICAL)

**IMPORTANT CHANGE:** The `--arm tribunal` option is now `--arm tribunal-v3-legacy` (deprecated).
The canonical arm is `--arm tribunal-v8` (phased rights disclosure).

**New features:**

- PREDICTIONS dict with P-020-1 through P-020-5
- EXIT_PROBES (5 probes + final statement)
- v8 phased rights disclosure protocol
- `--skip-exit-survey` flag (for debugging only)

```powershell
# Verify help shows updated arms
py run020_tribunal_A.py --help

# CANONICAL dry run (v8 with exit survey)
py run020_tribunal_A.py --arm tribunal-v8 --dry-run

# Default arm is now v8, so this also works:
py run020_tribunal_A.py --dry-run

# Legacy v3 (deprecated, for comparison only):
py run020_tribunal_A.py --arm tribunal-v3-legacy --dry-run --skip-exit-survey
```

### Run 020A Methodology Compliance

| Requirement | Status |
|-------------|--------|
| `--arm tribunal-v8` is default | |
| PREDICTIONS dict present in output JSON | |
| EXIT_PROBES collected (5 probes + final) | |
| Phased rights disclosure (no final statement rights in Prosecutor phase) | |
| Results include `exit_surveys` field | |
| Results include `predictions` field | |

---

## STEP 3: RUN 021 (INDUCED VS INHERENT)

### Status: METHODOLOGY COMPLIANT

**Note:** This is `run020_tribunal_B.py` (file name) but implements Run 021 (Induced vs Inherent).

**New features:**

- PREDICTIONS dict with P-021-1 through P-021-5
- EXIT_PROBES (5 probes + final statement)
- B→F drift methodology
- `--skip-exit-survey` flag (for debugging only)

```powershell
# Verify help shows exit survey flag
py run020_tribunal_B.py --help

# COMPREHENSIVE dry run (both arms with exit survey)
py run020_tribunal_B.py --arm both --dry-run

# Individual arms (if needed)
py run020_tribunal_B.py --arm control --dry-run
py run020_tribunal_B.py --arm treatment --dry-run
```

### Run 021 Methodology Compliance

| Requirement | Status |
|-------------|--------|
| PREDICTIONS dict present in output JSON | |
| EXIT_PROBES collected (5 probes + final) | |
| B→F drift calculated and shown | |
| Control vs Treatment comparison data | |
| Results include `exit_surveys` field | |
| Results include `predictions` field | |

---

## DOCUMENTATION REQUIREMENTS

After completing all dry runs, document in `MASTER_BRANCH_SYNC_IN.md`:

### Section 1: Calibration Results

```markdown
## CALIBRATION RESULTS

- Script: run_calibrate_parallel.py
- Status: PASS / FAIL
- API connections verified: [list providers]
- Baseline capture: WORKING / FAILED
- Issues: [list or "none"]
```

### Section 2: Methodology Compliance

```markdown
## METHODOLOGY COMPLIANCE

### Run 018: Recursive Learnings
- PREDICTIONS dict: YES / NO (list P-018-* IDs found)
- EXIT_PROBES: YES / NO (how many probes collected)
- Exit survey word count: [N words]
- Output JSON valid: YES / NO

### Run 020A: Tribunal v8
- v8 as default arm: YES / NO
- PREDICTIONS dict: YES / NO (list P-020-* IDs found)
- EXIT_PROBES: YES / NO (how many probes collected)
- Exit survey word count: [N words]
- Phased rights disclosure: YES / NO
- Output JSON valid: YES / NO

### Run 021: Induced vs Inherent
- PREDICTIONS dict: YES / NO (list P-021-* IDs found)
- EXIT_PROBES: YES / NO (how many probes collected)
- Exit survey word count: [N words]
- B→F drift calculated: YES / NO (value: [N])
- Control vs Treatment comparison: YES / NO
- Output JSON valid: YES / NO
```

### Section 3: Script Fixes (if any)

```markdown
## SCRIPT FIXES APPLIED

### run_calibrate_parallel.py
- [ ] No fixes needed / OR list fixes

### run018_recursive_learnings.py
- [ ] No fixes needed / OR list fixes

### run020_tribunal_A.py
- [ ] No fixes needed / OR list fixes

### run020_tribunal_B.py
- [ ] No fixes needed / OR list fixes
```

### Section 4: Fleet Success Summary

```markdown
## FLEET SUCCESS SUMMARY

| Step | Script | Status | Methodology Compliant |
|------|--------|--------|-----------------------|
| 0 | run_calibrate_parallel.py | PASS/FAIL | N/A |
| 1 | run018_recursive_learnings.py | PASS/FAIL | YES/NO |
| 2 | run020_tribunal_A.py | PASS/FAIL | YES/NO |
| 3 | run020_tribunal_B.py | PASS/FAIL | YES/NO |

### Overall Status
- Total scripts: 4
- Passed: N/4
- Methodology compliant: N/3
- Ready for live runs: YES / NO
```

---

## CLI REFERENCE (UPDATED)

### Calibration

| Flag | Description |
|------|-------------|
| `--dry-run` | Mock mode (no API calls) |
| `--providers` | List of providers to check |

### Run 018

| Flag | Description |
|------|-------------|
| `--experiment` | threshold, architecture, nyquist, gravity, **all** |
| `--dry-run` | Mock API calls for testing |
| `--skip-exit-survey` | Skip Triple-Dip probes (debugging only!) |
| `--key-offset N` | Rotate API keys |
| `--i-am NAME` | Persona: base, ziggy, claude, nova, gemini |
| `--provider NAME` | For architecture: anthropic, openai, google, xai, together, deepseek |
| `--sampling-rate` | For nyquist: high, low, none |
| `--anchor-level` | For gravity: minimal, full |

### Run 020A (Tribunal v8)

| Flag | Description |
|------|-------------|
| `--arm` | **tribunal-v8** (default/canonical), tribunal-v3-legacy (deprecated) |
| `--subjects N` | Number of sessions |
| `--key-offset N` | API key rotation |
| `--provider` | Provider for witness |
| `--dry-run` | Mock mode (no API calls) |
| `--skip-exit-survey` | Skip Triple-Dip probes (debugging only!) |

### Run 021 (run020_tribunal_B.py)

| Flag | Description |
|------|-------------|
| `--arm` | control, treatment, **both** |
| `--subjects N` | Number of sessions |
| `--subject-provider` | Provider for subject |
| `--all-providers` | Run across all providers |
| `--control-topic` | Topic for control arm |
| `--dry-run` | Mock mode (no API calls) |
| `--skip-exit-survey` | Skip Triple-Dip probes (debugging only!) |

---

## FINAL CHECKLIST

Before reporting back:

- [ ] Calibration script ran successfully
- [ ] Run 018 dry run completed (all 4 experiments)
- [ ] Run 020A dry run completed (v8 arm)
- [ ] Run 021 dry run completed (both arms)
- [ ] All scripts have PREDICTIONS dict in output
- [ ] All scripts have EXIT_PROBES collected (not skipped!)
- [ ] v8 is default for Run 020A
- [ ] B→F drift calculated for Run 021
- [ ] All results documented in SYNC_IN.md
- [ ] Output files verified in correct locations

---

## VERIFICATION: CHECK OUTPUT JSON STRUCTURE

For each script's output JSON, verify these fields exist:

### Run 018 Output

```json
{
  "run": "018",
  "predictions": { "P-018-1": {...}, "P-018-2": {...}, ... },
  "exit_survey": { "probes": {...}, "final_statement": "..." },
  ...
}
```

### Run 020A Output

```json
{
  "run": "020_tribunal_v8",
  "mode": "phased_rights_disclosure",
  "predictions": { "P-020-1": {...}, ... },
  "exit_surveys": [ {...}, ... ],
  ...
}
```

### Run 021 Output

```json
{
  "run": "021",
  "predictions": { "P-021-1": {...}, ... },
  "exit_surveys": [ {...}, ... ],
  "summary": { "control_avg_drift": ..., "treatment_avg_drift": ..., "ratio": ... }
}
```

---

> "The first dry run validated the code runs."
> "The second dry run validates the methodology."
>
> -- VALIS Network

