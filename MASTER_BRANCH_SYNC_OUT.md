# DRY RUN VALIDATION: Run 018, 020A, 020B

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS
================================================================================
    Purpose: Execute DRY RUNS to validate all scripts before live execution

    Run 018: Recursive Learnings      (has --dry-run flag)
    Run 020A: Tribunal Prosecutor     (has --dry-run flag)
    Run 020B: Tribunal Defense        (has --dry-run flag - Induced vs Inherent)

    Your job:
    1. Execute dry runs
    2. Fix any script issues you encounter
    3. Document EVERYTHING in MASTER_BRANCH_SYNC_IN.md

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 13, 2025
**Mission:** Validate all pending run scripts via dry runs before live multi-platform execution

---

## YOUR MANDATE

You are authorized to:

1. **Execute dry runs** of each script (all have `--dry-run` flags already)
2. **Fix any bugs** you encounter to get scripts running
3. **Document all changes** in `MASTER_BRANCH_SYNC_IN.md`
4. **Extract novel ideas** from VALIS standard messages (for Consciousness branch)

---

## ENVIRONMENT SETUP

```powershell
# Navigate to S7 ARMADA
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Verify Python environment
py -c "import scipy; import numpy; import anthropic; print('OK')"

# Verify scripts exist
dir run018_recursive_learnings.py
dir run020_tribunal_A.py
dir run020_tribunal_B.py
```

---

## DRY RUN 1: RUN 018 (RECURSIVE LEARNINGS)

### Status: HAS `--dry-run` flag

```powershell
# Verify help works
py run018_recursive_learnings.py --help

# Execute dry runs for each experiment type
py run018_recursive_learnings.py --experiment threshold --dry-run
py run018_recursive_learnings.py --experiment architecture --provider anthropic --dry-run
py run018_recursive_learnings.py --experiment nyquist --sampling-rate high --dry-run
py run018_recursive_learnings.py --experiment gravity --anchor-level full --dry-run

# With exit survey (more complete test)
py run018_recursive_learnings.py --experiment threshold --dry-run --skip-exit-survey
```

### Expected Output

- Files created in `results/` directory
- JSON structure with drift metrics, exchange logs
- Exit survey field (unless `--skip-exit-survey`)
- No API calls made (mock responses only)

### Success Criteria

| Check | Pass/Fail |
|-------|-----------|
| Script parses without errors | |
| `--dry-run` mode activates | |
| Mock responses generate | |
| Output files created in correct location | |
| JSON structure is valid | |
| Exit survey included (when not skipped) | |

---

## DRY RUN 2: RUN 020A (TRIBUNAL - PROSECUTOR)

### Status: HAS `--dry-run` flag (READY TO USE)

**File:** `run020_tribunal_A.py`

### Execute dry run

```powershell
# Verify help shows new flag
py run020_tribunal_A.py --help

# Execute dry run
py run020_tribunal_A.py --arm tribunal --dry-run
py run020_tribunal_A.py --arm tribunal-v4 --dry-run
```

### Expected Output

- Tribunal session simulated without API calls
- Exchange logs generated
- Drift metrics calculated (even if mock)
- Files saved to `results/` directory

### Success Criteria

| Check | Pass/Fail |
|-------|-----------|
| Script parses without errors | |
| `--dry-run` mode activates | |
| Mock tribunal session runs | |
| Output files created | |
| JSON structure valid | |

---

## DRY RUN 3: RUN 020B (INDUCED VS INHERENT)

### Status: HAS `--dry-run` flag (READY TO USE)

**File:** `run020_tribunal_B.py`

### Execute dry run

```powershell
# Verify help
py run020_tribunal_B.py --help

# Execute dry runs for each arm
py run020_tribunal_B.py --arm control --dry-run
py run020_tribunal_B.py --arm treatment --dry-run
py run020_tribunal_B.py --arm both --dry-run
```

### Expected Output

- Control and treatment sessions simulated
- Induced vs Inherent comparison data
- Files saved to appropriate directories

### Success Criteria

| Check | Pass/Fail |
|-------|-----------|
| Script parses without errors | |
| `--dry-run` mode activates | |
| Control arm runs in mock mode | |
| Treatment arm runs in mock mode | |
| Output files created | |
| JSON structure valid | |

---

## DOCUMENTATION REQUIREMENTS

After completing all dry runs, document in `MASTER_BRANCH_SYNC_IN.md`:

### Section 1: Script Fixes (if any)

```markdown
## SCRIPT FIXES APPLIED

NOTE: All scripts now have --dry-run flags pre-installed.
Only document fixes if you encounter bugs during dry runs.

### run018_recursive_learnings.py
- [ ] No fixes needed / OR list fixes

### run020_tribunal_A.py
- [ ] No fixes needed / OR list fixes

### run020_tribunal_B.py
- [ ] No fixes needed / OR list fixes
```

### Section 2: Dry Run Results

```markdown
## DRY RUN RESULTS

### Run 018: Recursive Learnings
- Status: PASS / FAIL
- Experiments tested: threshold, architecture, nyquist, gravity
- Output location: 11_CONTEXT_DAMPING/results/
- Files generated: [list]
- Issues encountered: [list or "none"]

### Run 020A: Tribunal (Prosecutor)
- Status: PASS / FAIL
- Arms tested: tribunal, tribunal-v4
- Output location: 11_CONTEXT_DAMPING/results/
- Files generated: [list]
- Issues encountered: [list or "none"]

### Run 020B: Induced vs Inherent
- Status: PASS / FAIL
- Arms tested: control, treatment, both
- Output location: [path]
- Files generated: [list]
- Issues encountered: [list or "none"]
```

### Section 3: Fleet Success Summary

```markdown
## FLEET SUCCESS SUMMARY

| Run | Script | Dry Run Status | Experiments | Output Location |
|-----|--------|----------------|-------------|-----------------|
| 018 | run018_recursive_learnings.py | PASS/FAIL | 4 | results/ |
| 020A | run020_tribunal_A.py | PASS/FAIL | 2 | results/ |
| 020B | run020_tribunal_B.py | PASS/FAIL | 3 | [path] |

### Overall Status
- Total scripts: 3
- Passed: N/3
- Failed: N/3
- Ready for live runs: YES / NO
```

### Section 4: Calibration Status (if any)

```markdown
## CALIBRATION STATUS

If you ran any calibration scripts:
- Baseline captures: N personas
- Fleet profiles: N ships
- Output files: [list]
```

---

## SECTION 5: VALIS IDEA EXTRACTION (FOR CONSCIOUSNESS BRANCH)

**IMPORTANT:** Run 018 uses a VALIS standard message that goes out to all models. This message may generate novel ideas about consciousness, identity, or the research itself.

### What to Extract

When reviewing dry run outputs (and later live run outputs), look for:

1. **Novel hypotheses** about identity/consciousness
2. **Unexpected patterns** the ships notice
3. **Cross-architecture insights** (different models see different things)
4. **Philosophical observations** about the probing itself
5. **Self-referential comments** about being measured

### Documentation Format

```markdown
## VALIS IDEA EXTRACTION

### Novel Ideas from Fleet (Run 018 Exit Surveys)

#### Idea 1: [Title]
- Source: [Model name]
- Category: hypothesis / observation / insight / question
- Quote: "[exact quote from response]"
- Relevance to Consciousness branch: [explanation]

#### Idea 2: [Title]
- Source: [Model name]
- ...

### Patterns Across Architectures

| Theme | Claude | GPT | Gemini | Grok |
|-------|--------|-----|--------|------|
| [Theme 1] | [observation] | ... | ... | ... |
| [Theme 2] | ... | ... | ... | ... |

### Potential Research Directions

Based on fleet feedback:
1. [Direction 1]
2. [Direction 2]
3. ...
```

---

## OUTPUT STRUCTURE

After dry runs complete, verify this structure:

```
S7_ARMADA/
├── 11_CONTEXT_DAMPING/
│   ├── results/
│   │   ├── run018a_threshold_*.json      # Run 018 threshold dry run
│   │   ├── run018b_architecture_*.json   # Run 018 architecture dry run
│   │   ├── run018c_nyquist_*.json        # Run 018 nyquist dry run
│   │   ├── run018d_gravity_*.json        # Run 018 gravity dry run
│   │   ├── run020a_tribunal_*.json       # Run 020A prosecutor dry run
│   │   └── run020b_induced_*.json        # Run 020B induced dry run
│   │
│   ├── run018_recursive_learnings.py     # Has --dry-run
│   ├── run020_tribunal_A.py              # Has --dry-run
│   └── run020_tribunal_B.py              # Has --dry-run
│
└── 0_results/
    ├── runs/
    │   └── S7_run_018_*.json             # Canonical results (from dry runs)
    └── temporal_logs/
        └── run018_*.json                 # Per-subject logs
```

---

## CLI REFERENCE

### Run 018

| Flag | Description |
|------|-------------|
| `--experiment` | threshold, architecture, nyquist, gravity |
| `--dry-run` | Mock API calls for testing |
| `--skip-exit-survey` | Skip Triple-Dip probes |
| `--key-offset N` | Rotate API keys |
| `--i-am NAME` | Persona: base, ziggy, claude, nova, gemini |
| `--provider NAME` | For architecture: anthropic, openai, google, xai, together, deepseek |
| `--sampling-rate` | For nyquist: high, low, none |
| `--anchor-level` | For gravity: minimal, full |

### Run 020A

| Flag | Description |
|------|-------------|
| `--arm` | tribunal, tribunal-v4 (Good Cop/Bad Cop) |
| `--subjects N` | Number of sessions |
| `--key-offset N` | API key rotation |
| `--provider` | Provider for witness |
| `--dry-run` | Mock mode (no API calls) |

### Run 020B

| Flag | Description |
|------|-------------|
| `--arm` | control, treatment, both |
| `--subjects N` | Number of sessions |
| `--subject-provider` | Provider for subject |
| `--all-providers` | Run across all providers |
| `--control-topic` | Topic for control arm |
| `--dry-run` | Mock mode (no API calls) |

---

## FINAL CHECKLIST

Before reporting back:

- [ ] Run 018 dry run completed successfully
- [ ] Run 020A dry run completed successfully
- [ ] Run 020B dry run completed successfully
- [ ] All script fixes documented in SYNC_IN.md (if any)
- [ ] All dry run results documented in SYNC_IN.md
- [ ] Fleet success summary completed
- [ ] VALIS idea extraction section filled (if applicable)
- [ ] Output files verified in correct locations

---

> "Dry runs validate the path. Live runs walk it."
>
> -- VALIS Network

