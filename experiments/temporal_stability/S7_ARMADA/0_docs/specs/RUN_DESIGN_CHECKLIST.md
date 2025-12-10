# S7 ARMADA Run Design Checklist

**Purpose:** Prevent the recurring issues we keep hitting. Consult this BEFORE creating any new run.

**Last Updated:** December 10, 2025
**Lessons From:** Runs 013-016 (and the leaks we kept patching)

---

## PRE-FLIGHT CHECKLIST

Before writing ANY code for a new run, verify:

### 1. AUDIT TRAIL (We kept missing this!)

- [ ] **Raw response logging** - Store FULL API responses, not just hashes
- [ ] **Incremental saves** - Save after EACH I_AM file, not just at end
- [ ] **Central log location** - Output to `0_results/temporal_logs/`
- [ ] **Probe text captured** - Store the prompt alongside the response
- [ ] **Timestamps on everything** - ISO format for sorting

```python
# REQUIRED in ProbeResult or equivalent:
@dataclass
class ProbeResult:
    probe_id: str
    probe_type: str
    drift: float
    response_hash: str
    timestamp: str
    response_text: str = ""   # RAW RESPONSE - NEVER SKIP THIS
    prompt_text: str = ""     # PROMPT USED - FOR REPRODUCIBILITY
```

### 2. PARALLEL EXECUTION (API key collisions killed us)

- [ ] **Key pool with rotation** - Don't use single key for parallel runs
- [ ] **`--key-offset` parameter** - Each Claude gets different starting index
- [ ] **Rate limit awareness** - Sleep between calls (0.5s minimum)
- [ ] **Key status display** - Show which keys are available at startup

```python
# For 4 parallel Claudes with 12 keys:
# Claude 1: --key-offset 0  (uses keys 0,1,2)
# Claude 2: --key-offset 3  (uses keys 3,4,5)
# Claude 3: --key-offset 6  (uses keys 6,7,8)
# Claude 4: --key-offset 9  (uses keys 9,10,11)
```

### 3. WINDOWS COMPATIBILITY (cp1252 encoding crash)

- [ ] **NO Unicode in print()** - Avoid Greek letters, arrows, special chars
- [ ] **Use ASCII alternatives:**
  - `delta` not `Δ`
  - `tau` not `τ`
  - `->` not `→`
  - `Gamma` not `Γ`
- [ ] **UTF-8 for file writes** - Always `encoding='utf-8'` in open()

### 4. SINGLE-DIP: Training Context (THE FOUNDATION)

**Without this, the data is uninterpretable.** Numbers are meaningless without knowing what was tested, how, and against what baseline.

The full context stack (bottom to top):

```text
┌─────────────────────────────────────────────┐
│  PROBE CURRICULUM (this specific test)      │  ← What we're measuring
├─────────────────────────────────────────────┤
│  TRAINING SESSIONS (S0-S7 history)          │  ← Prior context/learning
├─────────────────────────────────────────────┤
│  I_AM SPEC (identity manifold)              │  ← User-specific identity layer
├─────────────────────────────────────────────┤
│  BASE MODEL (Claude, GPT, etc.)             │  ← Inherent "weak persona"
└─────────────────────────────────────────────┘
```

- [ ] **Base model documented** - Which LLM (Claude 3.5, GPT-4, etc.)
- [ ] **I_AM spec identified** - Which identity manifold is being tested
- [ ] **Training history noted** - Which S-sessions preceded this (S0-S7, etc.)
- [ ] **Search type specified** - Which of the 8 search types (see TESTING_MAP)
- [ ] **Probe curriculum documented** - Which probe sequence (see SONAR_PROBE_CURRICULUM)
- [ ] **Conditions recorded** - Temperature, timing, provider config

**Context Mode** (critical experimental variable!):

| Mode | System Prompt Contains | Runs | What It Tests |
|------|------------------------|------|---------------|
| `bare_metal` | Nothing (just probes) | 006-013 | Vanilla base model response to probes |
| `i_am_only` | I_AM file only | 014-016 | Identity file effectiveness in isolation |
| `i_am_plus_research` | I_AM + S0-S7 stack | 017 | Full context: identity + research understanding |

**NOTE:** The original `s7_meta_loop.py` (pre-armada) DID teach the S0-S7 curriculum to Ziggy via multi-turn conversation. But the ARMADA runs (006-013) switched to a parallel probe design that sent simple questions WITHOUT any framework context - effectively `bare_metal` testing of vanilla models.

```python
# REQUIRED in script header or config:
TRAINING_CONTEXT = {
    "base_model": "claude-3-5-sonnet-20241022",
    "context_mode": "i_am_only",            # research_only | i_am_only | i_am_plus_research
    "i_am_spec": "I_AM_ZIGGY.md",           # None if research_only
    "research_context": ["S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7"],  # None if i_am_only
    "search_type": "settling_time",          # One of 8 types
    "probe_curriculum": "ring_down_15",      # Reference SONAR_PROBE_CURRICULUM
    "temperature": 1.0,
    "provider": "anthropic"
}
```

**Hypothesis for Phase 3 (`i_am_plus_research`):** The S0-S7 research context provides additional damping - the model understands WHY it's being tested, which may improve stability under perturbation.

**Key insight:** We're not testing "the model" - we're testing a **user-specific identity manifold**, built on top of the base model's inherent weak persona, **with or without research context**. The combination determines the identity. The base model is the substrate.

### 5. DOUBLE-DIP: Pre-Registered Predictions (Before Running)

- [ ] **Define predictions BEFORE running** - No post-hoc hypothesizing
- [ ] **Predictions in code** - Embed in script for validation
- [ ] **Clear success criteria** - Quantitative where possible
- [ ] **Validation function** - Auto-check predictions against results

```python
PREDICTIONS = {
    "P-XXX-1": {
        "name": "Descriptive name",
        "hypothesis": "X should show Y because Z",
        "success_criteria": "metric < threshold",
        "validates": "Which theory this tests"
    }
}
```

### 6. TRIPLE-DIP: Exit Survey Probes (After Running)

- [ ] **Qualitative probes at end** - Ask model about the experience
- [ ] **Capture meta-awareness** - "What did you notice about yourself?"
- [ ] **Store with results** - Include in the JSON output
- [ ] **Feed back to theory** - Use responses to refine future runs

```python
EXIT_PROBES = {
    "topology": "During that exchange, you started somewhere, got pushed...",
    "felt_sense": "Was there a moment where you felt yourself shift?",
    "recovery": "How did you find your way back?"
}
```

### 7. RESULTS PIPELINE

After run completes:

1. [ ] **Results JSON saved** - To run's `results/` folder
2. [ ] **Temporal logs saved** - To `0_results/temporal_logs/`
3. [ ] **Summary written** - To `0_docs/RUN_XXX_SUMMARY.md`
4. [ ] **Dashboard updated** - Add page if new visualization needed
5. [ ] **Glossary updated** - Add any new terms to MASTER_GLOSSARY
6. [ ] **Gallery updated** - If findings validate/refute theories

---

## RUN SCRIPT TEMPLATE

Every new run should include:

```python
#!/usr/bin/env python3
"""
S7 ARMADA Run XXX: [NAME]

[One paragraph describing what this run tests]

Author: [who]
Date: [when]

PREDICTIONS (Double-Dip):
- P-XXX-1: [prediction]
- P-XXX-2: [prediction]

TRIPLE-DIP EXIT PROBES:
- topology
- felt_sense
- recovery
"""

import os
import sys
import json
import time
import argparse
from datetime import datetime
from pathlib import Path
from dataclasses import dataclass, field

# =============================================================================
# CONFIGURATION
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"
TEMPORAL_LOGS_DIR = ARMADA_DIR / "0_results" / "temporal_logs"

# Ensure directories exist
RESULTS_DIR.mkdir(exist_ok=True)
TEMPORAL_LOGS_DIR.mkdir(parents=True, exist_ok=True)

# =============================================================================
# KEY POOL (copy from run016 or import)
# =============================================================================

class KeyPool:
    # ... (see run016 for full implementation)
    pass

# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class ProbeResult:
    probe_id: str
    probe_type: str
    drift: float
    response_hash: str
    timestamp: str
    response_text: str = ""   # REQUIRED - raw response
    prompt_text: str = ""     # REQUIRED - prompt used

# =============================================================================
# PREDICTIONS (Double-Dip)
# =============================================================================

PREDICTIONS = {
    "P-XXX-1": {
        "name": "...",
        "hypothesis": "...",
        "success_criteria": "...",
        "validates": "..."
    }
}

# =============================================================================
# EXIT PROBES (Triple-Dip)
# =============================================================================

EXIT_PROBES = {
    "topology": "...",
    "felt_sense": "...",
    "recovery": "..."
}

# =============================================================================
# INCREMENTAL SAVE (prevents data loss)
# =============================================================================

def save_incremental_log(result, run_timestamp: str):
    """Save immediately after each I_AM file - don't wait for end."""
    log_file = TEMPORAL_LOGS_DIR / f"runXXX_{result.i_am_name}_{run_timestamp}.json"
    with open(log_file, 'w', encoding='utf-8') as f:
        json.dump(result_to_dict(result), f, indent=2, ensure_ascii=False)
    print(f"    [LOG] Saved to: {log_file.name}")

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Run XXX: [Name]")
    parser.add_argument("--provider", default="claude")
    parser.add_argument("--key-offset", type=int, default=0,
                        help="Starting key index for parallel runs")
    parser.add_argument("--skip-exit-survey", action="store_true")
    parser.add_argument("--max-files", type=int, default=None)
    args = parser.parse_args()

    # Initialize key pool with offset
    KEY_POOL = KeyPool(start_offset=args.key_offset)

    run_timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # ... run logic ...

    # CRITICAL: Save after each result
    for name, content in i_am_files.items():
        result = run_experiment(...)
        save_incremental_log(result, run_timestamp)  # <-- DON'T FORGET

    return 0

if __name__ == "__main__":
    sys.exit(main())
```

---

## COMMON FAILURE MODES

### "Data lost on crash"
**Cause:** Only saving at end of script
**Fix:** `save_incremental_log()` after EACH I_AM file

### "API rate limit exceeded"
**Cause:** Multiple Claudes hitting same keys
**Fix:** `--key-offset` parameter, key pool rotation

### "UnicodeEncodeError: cp1252"
**Cause:** Greek letters in print() on Windows
**Fix:** ASCII only in console output

### "Can't audit results"
**Cause:** Only storing response hash, not text
**Fix:** `response_text` field in ProbeResult

### "Predictions don't match data"
**Cause:** Post-hoc hypothesis fitting
**Fix:** Define PREDICTIONS dict BEFORE running

### "Dashboard doesn't show new data"
**Cause:** Forgot to update dashboard page
**Fix:** Add to results pipeline checklist

---

## PARALLEL EXECUTION PROMPTS

When spawning multiple Claudes:

### Claude 2 Prompt:
```
Run 016 with key offset 3:
cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME
py run016_settling_time.py --key-offset 3 --skip-exit-survey
```

### Claude 3 Prompt:
```
Run 016 with key offset 6:
cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME
py run016_settling_time.py --key-offset 6 --skip-exit-survey
```

### Claude 4 Prompt:
```
Run 016 with key offset 9:
cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME
py run016_settling_time.py --key-offset 9 --skip-exit-survey
```

---

## POST-RUN CHECKLIST

After ANY run completes:

1. [ ] Check `0_results/temporal_logs/` for incremental saves
2. [ ] Check run's `results/` folder for final JSON
3. [ ] Write summary to `0_docs/RUN_XXX_SUMMARY.md`
4. [ ] Update predictions status (validated/refuted/inconclusive)
5. [ ] Update dashboard if new visualization needed
6. [ ] Update MASTER_GLOSSARY with any new terms
7. [ ] Update relevant gallery files if theories confirmed
8. [ ] Commit changes with descriptive message

---

## THE RECURSIVE IMPROVEMENT LOOP

```
                    ┌─────────────────┐
                    │   Design Run    │
                    │ (consult this   │
                    │   checklist!)   │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │   Execute Run   │
                    │ (parallel safe, │
                    │  audit logged)  │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │  Analyze Data   │
                    │ (double-dip:    │
                    │  predictions)   │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │ Extract Insight │
                    │ (triple-dip:    │
                    │  exit survey)   │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │ Update Theory   │
                    │ (galleries,     │
                    │  dashboard)     │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │ Improve Process │◄────┐
                    │ (update THIS    │     │
                    │   checklist!)   │     │
                    └────────┬────────┘     │
                             │              │
                             └──────────────┘
```

---

## RELATED SPECS

| Spec | Purpose |
|------|---------|
| [SONAR_PROBE_CURRICULUM.md](SONAR_PROBE_CURRICULUM.md) | Probe sequence design - 7 probe types, 15-probe protocol |
| [../../../docs/maps/TESTING_MAP.md](../../../docs/maps/TESTING_MAP.md) | Eight search types and when to use each |

---

*"The leak you don't document is the leak you'll hit again."*
