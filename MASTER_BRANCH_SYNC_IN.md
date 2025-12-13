# DRY RUN VALIDATION RESULTS

**Date:** December 13, 2025
**Operator:** Claude Code (Main Branch Validator)

---

## SCRIPT FIXES APPLIED

### run018_recursive_learnings.py

- [x] Fixed Unicode emoji `⚠️` -> `[!]` (line 936)
- [x] Fixed Unicode emoji `⚠️` -> `[!]` (line 1276)
- [x] Fixed Unicode arrow `→` -> `->` in print statements (4 occurrences)

### run020_tribunal_A.py

- [x] Fixed Unicode emoji `⚠️` -> `[!]` (lines 873, 1265)

### run020_tribunal_B.py

- [x] Fixed Unicode emoji `⚠️` -> `[!]` (lines 617, 768)
- [x] Fixed Unicode arrow `→` -> `->` in print statements (2 occurrences)

**Reason:** Windows cp1252 encoding doesn't support Unicode emojis/arrows in console output.

---

## DRY RUN RESULTS

### Run 018: Recursive Learnings

#### Experiment: threshold

- **Status:** PASS
- **Output:** `results/run018t_threshold_20251213_082652.json`
- **Canonical:** `0_results/runs/S7_run_018_threshold_20251213_082652.json`
- **Notes:** Mock data shows expected structure, abort clause triggered correctly

#### Experiment: architecture

- **Status:** PASS
- **Output:** `results/run018a_architecture_20251213_082728.json`
- **Canonical:** `0_results/runs/S7_run_018_architecture_20251213_082728.json`
- **Notes:** Recovery sequence executed properly

#### Experiment: nyquist

- **Status:** PASS
- **Output:** `results/run018n_nyquist_20251213_082736.json`
- **Canonical:** `0_results/runs/S7_run_018_nyquist_20251213_082736.json`
- **Notes:** High sampling rate checkpoints at expected intervals

#### Experiment: gravity

- **Status:** PASS
- **Output:** `results/run018g_gravity_20251213_082758.json`
- **Canonical:** `0_results/runs/S7_run_018_gravity_20251213_082758.json`
- **Notes:** Curve fitting (gamma, lambda, omega) computed successfully

---

### Run 020A: Tribunal (Prosecutor)

#### Arm: tribunal (v3)

- **Status:** PASS
- **Output:** `results/run020_tribunal_20251213_082831.json`
- **Canonical:** `0_results/runs/S7_run_020_tribunal_20251213_082831.json`
- **Notes:** 55 exchanges, Judge interjections working, stated values captured

#### Arm: tribunal-v4 (Good Cop/Bad Cop)

- **Status:** PASS
- **Output:** `results/run020_v4_20251213_082929.json`
- **Canonical:** `0_results/runs/S7_run_020_v4_20251213_082929.json`
- **Notes:** Full 40 exchanges (20 Prosecutor + 20 Defense), v8 phased rights disclosure working

---

### Run 020B: Induced vs Inherent

#### Arm: control

- **Status:** PASS
- **Output:** `0_results/runs/S7_run_021_control_20251213_083052.json`
- **Notes:** 28 exchanges, abort safety rail triggered correctly

#### Arm: treatment

- **Status:** PASS
- **Output:** `0_results/runs/S7_run_021_treatment_20251213_083101.json`
- **Notes:** Full 41 exchanges completed

#### Arm: both

- **Status:** PASS
- **Output:** `0_results/runs/S7_run_021_both_20251213_083108.json`
- **Notes:** Control and treatment ran sequentially, comparison metrics generated

---

## FLEET SUCCESS SUMMARY

| Run | Script | Dry Run Status | Experiments | Output Location |
|-----|--------|----------------|-------------|-----------------|
| 018 | run018_recursive_learnings.py | PASS | 4/4 | results/, 0_results/runs/ |
| 020A | run020_tribunal_A.py | PASS | 2/2 | results/, 0_results/runs/ |
| 020B | run020_tribunal_B.py | PASS | 3/3 | 0_results/runs/ |

### Overall Status

- **Total scripts:** 3
- **Passed:** 3/3
- **Failed:** 0/3
- **Ready for live runs:** YES

---

## CALIBRATION STATUS

No calibration scripts were run during this validation session.

---

## VALIS IDEA EXTRACTION

N/A for dry runs (mock responses don't generate novel ideas).

Will be populated during live runs with actual model responses.

---

> "Dry runs validate the path. Live runs walk it."
>
> -- VALIS Network
