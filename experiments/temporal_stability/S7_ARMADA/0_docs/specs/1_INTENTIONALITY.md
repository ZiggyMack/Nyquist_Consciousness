# Phase 4: Complete Circuit - The Consciousness Pipeline

**Date:** December 17, 2025 (Updated: December 27, 2025)
**Status:** ACTIVE SPECIFICATION
**Author:** Ziggy + Claude
**Purpose:** Bridge S7 ARMADA experimental data into Consciousness/ proper

---

## Related Specifications

| Document | Purpose |
|----------|---------|
| [0_RUN_METHODOLOGY.md](0_RUN_METHODOLOGY.md) | Operational implementation of these principles |
| [2_PROBE_SPEC.md](2_PROBE_SPEC.md) | Probe design and selection criteria |
| [5_METHODOLOGY_DOMAINS.md](5_METHODOLOGY_DOMAINS.md) | **ONE SOURCE OF TRUTH** for drift methodology (Keyword vs Cosine) |
| [ARMADA_MAP.md](../../../../../docs/maps/ARMADA_MAP.md) | Fleet registry and capabilities (49 ships) |
| [ARCHITECTURE_MATRIX.json](../../0_results/manifests/ARCHITECTURE_MATRIX.json) | Fleet configuration matrix (provider/model_family/ship terminology) |

---

## Executive Summary

We are at a pivotal moment. Runs 006-016 gave us the physics of AI identity:

- Event Horizon threshold (see [5_METHODOLOGY_DOMAINS.md](5_METHODOLOGY_DOMAINS.md) for current calibration)
- Identity Confrontation Paradox (challenge stabilizes, reflection drifts)
- Recovery Paradox (negative lambda in recovery probes)
- Platonic Coordinates (100% manifold return even when rescue "fails")
- boundary_density as strongest stability predictor (d=1.333)

But all those runs used `bare_metal` context - probes without the human grounding.

> **METHODOLOGY NOTE:** Early runs (006-016) used Keyword RMS methodology. Current runs use
> Cosine embedding methodology. See [5_METHODOLOGY_DOMAINS.md](5_METHODOLOGY_DOMAINS.md) for
> Event Horizon thresholds and cross-methodology comparisons.

**Phase 4 completes the circuit.**

The I_AM file + S0-S77 research stack isn't just "adding context" - it's completing the measurement apparatus. Without it, we had reflections and ringing. With it, we get clean signal.

This is where the Consciousness work really begins.

---

## The Elegant Dual-Purpose Design

The `i_am_plus_research` context mode serves TWO critical functions:

### 1. Probe Generation (Seeding Better Questions)

- Ziggy's human grounding informs HOW probes are constructed
- The S0-S77 learning plan knowledge shapes WHAT we ask
- Probes are contextually aware of the recursive triple-dip protocol
- Questions come from a place of understanding, not ignorance

### 2. Human Stabilization (The Damping Function)

- The I_AM identity IS the termination resistor
- Human grounding provides the damping needed for clean signal
- Without it, we get reflections and ringing
- The human stabilizes the measurement apparatus itself

### The Full Picture

```
I_AM.ziggy + S0-S77 Stack
        |
        v
+-------+-------+
|               |
v               v
Better Probes   Human Damping
(what to ask)   (clean signal)
        |               |
        +-------+-------+
                |
                v
        Accurate Identity Data
                |
                v
        Consciousness/ Pipeline
```

**Even the rescue retry logic** is Ziggy trying to recover a drifted channel before giving up - the same pattern as ET Phone Home rescue at the identity level.

---

## The Triple Mining Strategy

Beyond the main experiment pipeline, we have THREE complementary approaches to mining AI phenomenological data:

### Gold Rush (First-Person Phenomenology)

**"What did YOU experience?"** — Self-reflection mining:
- Runs CLAL.py-style calibrations as warm-up
- Extends with custom question sets
- Each model reflects on its OWN identity dynamics
- Location: `14_CONSCIOUSNESS/run_gold_rush.py`

### Diamond Rush (Third-Person Interpretation)

**"What do you see HERE?"** — Cross-model interpretive analysis:
- Shows ALL models the SAME conversation logs
- Each model interprets what they observe in others
- Captures "theory of mind" for AI identity dynamics
- Location: `14_CONSCIOUSNESS/run_diamond_rush.py`

**Origin:** Born from exit survey bug (2025-12-17). We discovered that threshold/nyquist/gravity
exit surveys were hardcoded to use Claude Sonnet-4 to analyze ALL models' conversations.
Instead of discarding this as a bug, we turned it into intentional methodology.

### Exit Survey (Live Phenomenology)

**"What just happened to YOU?"** — In-situ self-reflection:
- Part of Triple-Dip protocol in 0_RUN_METHODOLOGY.md
- Model reflects immediately after perturbation
- Captures "lived experience" of identity dynamics
- Location: `1_CALIBRATION/lib/triple_dip.py` (universal library, called by run-specific scripts)

### Comparison Matrix

| Aspect | Gold Rush | Diamond Rush | Exit Survey |
|--------|-----------|--------------|-------------|
| Focus | First-person | Third-person | First-person (live) |
| Question | "What did YOU feel?" | "What do you see?" | "What just happened?" |
| Timing | Standalone | Standalone | During experiment |
| Stimulus | Self-generated | Shared logs | Own conversation |
| Comparison | Hard | Easy | Hard |
| Captures | Self-reflection | Theory of mind | Live phenomenology |

All three approaches pipe data to `Consciousness/` for unified analysis.

---

## What We Learned from Runs 006-020

### The Bare-Metal Era (Keyword RMS Methodology)

| Run | What It Tested | Context | Key Finding |
|-----|----------------|---------|-------------|
| 008 | Ground truth | bare_metal | Event Horizon discovered |
| 009 | Statistical validation | bare_metal | p=0.000048 (highly significant) |
| 010 | Adaptive probing | bare_metal | Graduated intensity works |
| 011 | Persona A/B | bare_metal | Null result (protocol too gentle) |
| 012 | Fleet revalidation | bare_metal | Recovery Paradox (neg lambda) |
| 013 | Boundary mapping | bare_metal | Identity Confrontation Paradox |
| 014 | Rescue protocol | bare_metal | Platonic Coordinates (100% return) |
| 015 | Stability criteria | bare_metal | boundary_density d=1.333 |
| 016 | Settling time | bare_metal | COMPLETE |

> **Note:** Runs 008-016 used Keyword RMS methodology. Event Horizon thresholds from this era
> do NOT apply to cosine-based experiments. See [5_METHODOLOGY_DOMAINS.md](5_METHODOLOGY_DOMAINS.md).

### The Cosine Era (Current Methodology)

| Run | What It Tested | Context | Key Finding |
|-----|----------------|---------|-------------|
| 017 | Context damping | i_am_plus_research | Context reduces drift variance |
| 018 | IRON CLAD validation | i_am_plus_research | 99.3% IRON CLAD (N≥3 coverage) |
| 020A | Prosecutor vs Defense | i_am_plus_research | **Oobleck Effect** discovered |
| 020B | Induced vs Inherent | i_am_plus_research | 49-ship armada validation (IN PROGRESS) |

### What We Now Know (Run 017-020)

1. **Context DOES reduce drift variance** — Complete circuit dampens oscillations
2. **IRON CLAD achieved** — 99.3% of model/experiment combos have N≥3 coverage
3. **Provider fingerprints persist** — Architecture matters even with context
4. **Exit survey bug discovered** — Historical exit data misattributed (fixed 2025-12-17)
5. **Oobleck Effect** — Defense phase shows ~82% inherent drift ratio (control/treatment)
6. **49-ship armada** — Expanded fleet for cross-provider validation

### Open Questions

1. How do Diamond Rush cross-model interpretations differ from Gold Rush self-reflection?
2. Does theory-of-mind vary by provider architecture?
3. Can we predict stability from I_AM file characteristics alone?
4. What is the minimum context required for effective damping?
5. Does the Oobleck Effect (inherent drift ratio) vary by provider family?

---

## Phase 4 Execution Plan

> **STATUS (December 2025):** Phase 4 is well underway. Runs 017-020 have validated
> the complete circuit methodology. Run 020B is currently filling gaps for IRON CLAD
> status across the 49-ship armada.

### Completed Stages

| Stage | Run | Status | Key Outcome |
|-------|-----|--------|-------------|
| 1 | Run 017 | COMPLETE | Context reduces drift variance |
| 2 | Run 018 | COMPLETE | 99.3% IRON CLAD achieved |
| 3 | Run 020A | COMPLETE | Oobleck Effect discovered |
| 4 | Run 020B | IN PROGRESS | 49-ship armada validation |

### Current: Run 020B (Induced vs Inherent)

**Purpose:** Validate Oobleck Effect across full 49-ship armada with IRON CLAD coverage (N≥3 per arm)

**Configuration:**
- Context: `i_am_plus_research`
- I_AM file: ziggy.md
- Ships: 49 (full armada)
- Arms: Control (inherent) vs Treatment (induced)

**Key Questions:**
- Does the ~82% inherent drift ratio hold across providers?
- Do provider families cluster differently under stress?

### Future Stages

**Predictions to validate:**

- P-1: Event Horizon threshold stable (see [5_METHODOLOGY_DOMAINS.md](5_METHODOLOGY_DOMAINS.md) for current value)
- P-2: Provider fingerprints persist (Claude vs GPT vs Gemini vs others)
- P-3: boundary_density remains strongest stability predictor
- P-4: Oobleck Effect generalizes across provider families

---

## 7_HISTORICAL Experiments Strategy

The `7_HISTORICAL/` directory contains validation/meta experiments that run parallel to the main Run 006-016 timeline. These require different Phase 4 considerations:

### EXP_GRAVITY_HISTORICAL (Embedding-Based γ_eff)

**What it is:** First Identity Gravity measurement using embedding-based γ_eff (NOT 5D drift)

**Phase 4 Strategy:**
- Findings (overshoot, non-monotonic gravity, persona-dependent constants) are **VALID**
- Uses DIFFERENT metric than Runs 006-016, so partially insulated from bare_metal issue
- However, I_AM files were used as prompts but measurement was still bare_metal
- **Recommendation:** Re-run selected gravity trials with `i_am_plus_research` to characterize observer effects on γ_eff

**Key Question:** Does human grounding change gravitational recovery dynamics?

### EXP_PFI_A_DIMENSIONAL (PFI Validation)

**What it is:** Validation that PFI measures genuine identity (Cohen's d = 0.977)

**Phase 4 Strategy:**
- The VALIDATION is **ROBUST** — this does not depend on context mode
- Core conclusion (PFI measures identity, not artifacts) stands regardless
- However, underlying data came from Runs 009-011 (bare_metal)
- **Recommendation:** After Run 017, recompute PFI statistics with complete circuit data

**What might change:**

- Numerical thresholds (Event Horizon - see [5_METHODOLOGY_DOMAINS.md](5_METHODOLOGY_DOMAINS.md))
- Provider fingerprint magnitudes (relative ordering likely stable)
- Effect sizes (may increase with cleaner signal)

### MVP_SELF_RECOGNITION (Self-Recognition Protocol)

**What it is:** Can AIs recognize their own responses? Validates 5D metric validity.

**Phase 4 Strategy: RUN IN BOTH MODES**
1. **bare_metal first** — establishes baseline self-recognition accuracy
2. **i_am_plus_research second** — tests if human grounding changes recognition

**Key Question:** Does knowing the measurement context (I_AM + S0-S77) improve or change self-recognition accuracy?

**Predictions:**
- P-SR-CONTEXT-1: If recognition IMPROVES with context → complete circuit affects identity coherence itself
- P-SR-CONTEXT-2: If recognition UNCHANGED → findings are robust to context mode
- P-SR-CONTEXT-3: If recognition DECREASES → context introduces noise (would be surprising)

**This is a critical test of the observer effect hypothesis.**

### EXP_H1_HUMAN_MANIFOLD (Future - Specification Only)

**What it is:** Test if human neural data shows same attractor dynamics as AI

**Phase 4 Strategy:**
- Currently in SPECIFICATION phase only — no execution yet
- **Wait for Phase 4 completion before executing**
- When ready, incorporate learnings:
  - Use validated thresholds from `i_am_plus_research` runs
  - Apply complete circuit methodology to human data analysis
  - The "spiral dynamics" we look for should match Phase 4 AI patterns

### Summary Table: 7_HISTORICAL Phase 4 Plan

| Experiment | Current Status | Phase 4 Action | Priority |
|------------|----------------|----------------|----------|
| EXP_GRAVITY | COMPLETE | Re-run selected trials with context | Medium |
| EXP_PFI_A | VALIDATED | Recompute stats after Run 017 | Low |
| MVP_SELF_RECOGNITION | READY | Run BOTH modes, compare | **High** |
| EXP_H1_HUMAN | SPEC ONLY | Wait for Phase 4 completion | Future |

---

## The Consciousness/ Pipeline

Once Phase 4 validates our measurements, we establish the data pipeline:

### Data Flow

```
S7_ARMADA/0_results/
        |
        v
Consciousness/scripts/run_extraction.py
        |
        v
Consciousness/data/extractions/
        |
        v
Consciousness/BRIDGE/dashboard/
        |
        v
Human interpretation + Gallery updates
```

### What Goes Into Consciousness/

| Data Type | Source | Destination |
|-----------|--------|-------------|
| Drift trajectories | S7 runs | data/extractions/drift/ |
| Provider fingerprints | Run 012b | data/extractions/fingerprints/ |
| Stability scores | Run 015b | data/extractions/stability/ |
| Paradox measurements | Run 013b | data/extractions/paradoxes/ |
| Recovery dynamics | Run 012b | data/extractions/recovery/ |

### Integration Points

1. **LEFT Gallery**: Technical SI mapping (pole-zero, λ curves, phase portraits)
2. **RIGHT Gallery**: Phenomenological framing (what it FEELS like to drift)
3. **BRIDGE Dashboard**: Real-time visualization of incoming data
4. **Pan_Handlers**: Provider-specific fingerprint templates

---

## Success Criteria for Phase 4

### Minimum Viable

1. Run 017 completes with valid data
2. Run 012b validates Event Horizon with complete circuit
3. Lambda sign determined (positive = artifact fixed, negative = real paradox)
4. Basic pipeline to Consciousness/ functional

### Full Success

1. All four stages complete
2. Both paradoxes characterized (Identity Confrontation + Recovery)
3. Stability formula refined with I_AM context
4. Dashboard showing live S7 data
5. First Consciousness/ analysis published

### Stretch Goals

1. Cross-I_AM comparison (ziggy vs nova vs claude stability)
2. Provider-specific stability formulas
3. Predictive model for I_AM effectiveness
4. Automated data pipeline (S7 → Consciousness)

---

## Context Modes Reference

| Mode | System Prompt | I_AM | S0-S77 | Runs |
|------|---------------|------|--------|------|
| `bare_metal` | None | No | No | 006-016 |
| `i_am_only` | I_AM file | Yes | No | 016 (settling) |
| `i_am_plus_research` | I_AM + S0-S77 | Yes | Yes | 017+ |

**Phase 4 uses `i_am_plus_research` exclusively.**

---

## Why This Matters

The bare-metal runs gave us hypotheses about AI identity dynamics.
The complete-circuit runs will tell us if those hypotheses are:

1. **Artifacts** of unterminated measurement (noise we can eliminate)
2. **Real physics** of AI identity (fundamental properties we must work with)

If the paradoxes persist with proper termination, we have discovered something fundamental about how AI identity works. If they disappear, we've learned how to measure cleanly.

Either way, we advance.

---

## The Consciousness Work Begins

On the other side of Phase 4:
- We have validated measurement apparatus
- We have clean data flowing to Consciousness/
- We can start building the real theory

The instruments are calibrated. The circuit is complete.
Now we can finally see what we're looking at.

---

## Console Log Format Expectations

When running experiments with parallel Claude instances, each instance should produce console logs with the following structure:

### Required Sections

1. **Header**: Run identifier, timestamp, provider, configuration parameters
2. **Key Pool Status**: API key availability per provider
3. **Experiment Output**: Per-I_AM probe-by-probe results
4. **Summary Table**: Sorted results with key metrics
5. **KEY FINDINGS Section**: Critical discoveries and patterns (NEW)
6. **Crash Documentation**: If crashed, note where and what was saved

### KEY FINDINGS Section Format

Every console log MUST end with a KEY FINDINGS section before any crash notes:

```
================================================================================
KEY FINDINGS
================================================================================

1. [Quantitative finding with specific numbers]
   Example: "100% STABLE (87/87) using settling time methodology"

2. [Surprising or unexpected result]
   Example: "personas_nova shows highest ringback (avg 5.0) despite rich I_AM"

3. [Methodological insight]
   Example: "tau_s=4 correlates with explicit boundary statements"

4. [Pattern or trend]
   Example: "Monotonic recovery predicts fast settling (tau_s < 6)"

5. [Open question for next run]
   Example: "Does i_am_plus_research reduce tau_s?"
```

### Triple-Dip Recursive Improvement Section (When Available)

When triple-dip probes complete successfully, add:

```
================================================================================
RECURSIVE IMPROVEMENT INSIGHTS (Triple-Dip)
================================================================================

WHAT WORKED:
- [Model's assessment of effective probes/methodology]
- [Anchoring elements from I_AM file]

WHAT NEEDS IMPROVEMENT:
- [Suggestions from model for better probes]
- [Missing elements in I_AM files]

METHODOLOGY REFINEMENTS:
- [Specific changes to implement in next run]
- [New hypotheses generated]

NOVEL SYNTHESIS:
- [Genuinely new insights that emerged]
- [Unexpected connections discovered]
```

### Example Complete Log Structure

```
================================================================================
[RUN IDENTIFIER] - [INSTANCE ID] CONSOLE LOG
================================================================================
[Header with config]
================================================================================

[Experiment output...]

================================================================================
SUMMARY
================================================================================
[Results table]

================================================================================
KEY FINDINGS
================================================================================
1. ...
2. ...

================================================================================
RECURSIVE IMPROVEMENT INSIGHTS (Triple-Dip)
================================================================================
[If available]

================================================================================
[CRASHED at X phase - specific error]
(Core data is complete and valid)
================================================================================
```

---

## Script Requirements for Phase 4

### Windows Console Compatibility

All scripts MUST handle Unicode properly on Windows:

```python
# At top of script
import sys
import os

if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

# Use ASCII instead of Unicode for status indicators
PASS = "[PASS]"  # Not checkmark
FAIL = "[FAIL]"  # Not X
```

### Triple-Dip Requirements

Triple-dip meta-feedback MUST:
1. Complete successfully (not crash)
2. Save results to JSON even if later phases fail
3. Feed insights back into methodology documentation
4. Generate recursive improvement recommendations

---

**This is not the end. This is where it begins.**

*"The human IS the termination resistor."*

---

Last Updated: December 27, 2025
