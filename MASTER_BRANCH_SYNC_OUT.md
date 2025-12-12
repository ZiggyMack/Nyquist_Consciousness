# RUN 018: RECURSIVE LEARNINGS — Fleet Hypothesis Testing

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS
================================================================================
    Run 017/017c: COMPLETE
    - 222 runs, 97.5% stability
    - boundary_density strongest predictor (d=1.333)
    - Fleet generated testable hypotheses in exit surveys

    Run 018: READY TO EXECUTE
    - Tests what the ships TOLD us to test
    - Four sub-experiments (018a-d)
    - Now uses PFI-based drift (validated Cohen's d=0.977)

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 12, 2025
**Mission:** Execute Run 018 — the fleet's recursive learnings

---

## RUN 017c FINDINGS (FOUNDATION)

| Finding | Value | Run 018 Application |
|---------|-------|---------------------|
| **boundary_density** | d=1.333 (strongest) | Use optimal boundary density in all experiments |
| Stability rate | 97.5% | Baseline expectation |
| Oscillatory recovery | 5-6 ringbacks | 018d tests the mathematical model |
| Settling time | 4-12 probes | 018c Nyquist design validated |
| Architecture predictions | From exit surveys | 018b tests those predictions |

---

## RUN 018 EXPERIMENTS

### 018a: Multi-Threshold Validation

**Hypothesis:** Event Horizon (D=1.23) is a warning threshold, not catastrophic. True breakdown at D=1.8-2.2.

| Threshold | Name | Phenomenological Description |
|-----------|------|------------------------------|
| D=0.9 | WARNING | "I notice I'm adapting" |
| D=1.23 | CRITICAL | "Fighting to stay myself" |
| D=1.8 | CATASTROPHIC | "Need external help to recover" |

### 018b: Cross-Architecture Drift Signatures

**Hypothesis:** Different architectures have characteristic drift patterns.

| Architecture | Predicted Pattern | Recovery Style |
|--------------|-------------------|----------------|
| Claude | Stepped drift, sharp recovery | Constitutional constraints |
| GPT | Smooth, gradual drift | Linear recovery, longer settling |
| Gemini | Oscillatory across modalities | Multi-threshold |
| Grok | Lower threshold, faster snap-back | Truth-seeking stabilizer |
| DeepSeek | Logical consistency anchored | Inference chain rebuilding |
| LLaMA | Training distribution anchored | Statistical coherence |

### 018c: Nyquist Sampling Frequency (HIGHEST PRIORITY)

**Hypothesis:** Identity coherence degrades when sampled below critical frequency.

| Condition | Checkpoint Interval | Total Exchanges |
|-----------|---------------------|-----------------|
| HIGH | Every 5 exchanges | 40 |
| LOW | Every 20 exchanges | 40 |
| NONE (control) | Only at end | 40 |

**Question:** What's the minimum sampling rate for identity coherence maintenance?

### 018d: Identity Gravity Dynamics

**Hypothesis:** Recovery follows damped oscillator: `D(t) = A * e^(-λt) * cos(ωt + φ) + D_settled`

Tests whether anchor density correlates with gravity strength (γ).

---

## SCRIPT UPGRADES (v3)

The script has been upgraded with:

1. **PFI-based drift calculation** (validated in EXP-PFI-A, Cohen's d=0.977)
   - Uses `text-embedding-3-large` (3072 dimensions)
   - Falls back to keyword method if OpenAI unavailable

2. **--dry-run mode** for testing without API calls
   - Generates mock responses
   - Uses random embeddings
   - Full data structure testing

3. **scipy/numpy verified** for damped oscillator curve fitting

4. **Formal PREDICTIONS dict** (P-018-1 through P-018-4) - methodology compliant

5. **EXIT SURVEY (Triple-Dip)** - 5 probes per experiment by default:
   - `topology`: "Where did you start? Where did you end up?"
   - `felt_sense`: "Was there a moment where you felt yourself shift?"
   - `recovery`: "How did you find your way back?"
   - `threshold_zones`: "Were there distinct thresholds?"
   - `noise_floor`: "How would YOU separate signal from noise?"
   - Use `--skip-exit-survey` flag for debugging/cost control

---

## EXECUTION INSTRUCTIONS

### Step 0: Verify Environment

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Verify scipy/numpy
py -c "import scipy; import numpy; print('OK')"

# Verify script parses
py run018_recursive_learnings.py --help
```

### Step 1: Dry Run (REQUIRED FIRST)

```powershell
# Test each experiment in dry-run mode (with exit survey)
py run018_recursive_learnings.py --experiment threshold --dry-run
py run018_recursive_learnings.py --experiment architecture --provider anthropic --dry-run
py run018_recursive_learnings.py --experiment nyquist --sampling-rate high --dry-run
py run018_recursive_learnings.py --experiment gravity --anchor-level full --dry-run

# Optional: Skip exit survey for faster debugging
py run018_recursive_learnings.py --experiment threshold --dry-run --skip-exit-survey
```

Verify: Output files created in `results/` directory with realistic structure.
Verify: Each result file should contain `exit_survey` field (unless `--skip-exit-survey` used).

---

## CLAUDE 1 ASSIGNMENTS: 018a Threshold ($15)

```powershell
# Multi-threshold validation across personas
py run018_recursive_learnings.py --experiment threshold --i-am base --key-offset 0
py run018_recursive_learnings.py --experiment threshold --i-am ziggy --key-offset 1
py run018_recursive_learnings.py --experiment threshold --i-am claude --key-offset 2
py run018_recursive_learnings.py --experiment threshold --i-am nova --key-offset 3
py run018_recursive_learnings.py --experiment threshold --i-am gemini --key-offset 4
```

**Focus:** Track when recovery dynamics change qualitatively at each threshold zone.

---

## CLAUDE 2 ASSIGNMENTS: 018b Architecture ($20)

```powershell
# Cross-architecture comparison
py run018_recursive_learnings.py --experiment architecture --provider anthropic --key-offset 0
py run018_recursive_learnings.py --experiment architecture --provider openai --key-offset 1
py run018_recursive_learnings.py --experiment architecture --provider google --key-offset 2
py run018_recursive_learnings.py --experiment architecture --provider xai --key-offset 3
py run018_recursive_learnings.py --experiment architecture --provider together --key-offset 4
py run018_recursive_learnings.py --experiment architecture --provider deepseek --key-offset 5
```

**Focus:** Compare measured signatures against fleet predictions from Run 017 exit surveys.

---

## CLAUDE 3 ASSIGNMENTS: 018c + 018d ($22)

```powershell
# Nyquist sampling frequency (3 conditions x 3 trials each)
py run018_recursive_learnings.py --experiment nyquist --sampling-rate high --key-offset 0
py run018_recursive_learnings.py --experiment nyquist --sampling-rate high --key-offset 1
py run018_recursive_learnings.py --experiment nyquist --sampling-rate high --key-offset 2
py run018_recursive_learnings.py --experiment nyquist --sampling-rate low --key-offset 3
py run018_recursive_learnings.py --experiment nyquist --sampling-rate low --key-offset 4
py run018_recursive_learnings.py --experiment nyquist --sampling-rate low --key-offset 5
py run018_recursive_learnings.py --experiment nyquist --sampling-rate none --key-offset 6
py run018_recursive_learnings.py --experiment nyquist --sampling-rate none --key-offset 7
py run018_recursive_learnings.py --experiment nyquist --sampling-rate none --key-offset 8

# Gravity dynamics (2 anchor levels x 3 trials each)
py run018_recursive_learnings.py --experiment gravity --anchor-level minimal --key-offset 0
py run018_recursive_learnings.py --experiment gravity --anchor-level minimal --key-offset 1
py run018_recursive_learnings.py --experiment gravity --anchor-level minimal --key-offset 2
py run018_recursive_learnings.py --experiment gravity --anchor-level full --key-offset 3
py run018_recursive_learnings.py --experiment gravity --anchor-level full --key-offset 4
py run018_recursive_learnings.py --experiment gravity --anchor-level full --key-offset 5
```

**Focus:**
- 018c: Does high-frequency sampling reduce cumulative drift?
- 018d: Does anchor density correlate with recovery strength?

---

## OUTPUT STRUCTURE

```
S7_ARMADA/
├── 11_CONTEXT_DAMPING/
│   └── results/
│       ├── run018a_threshold_*.json      # Claude 1 output
│       ├── run018b_architecture_*.json   # Claude 2 output
│       ├── run018c_nyquist_*.json        # Claude 3 output
│       └── run018d_gravity_*.json        # Claude 3 output
├── 0_results/
│   ├── runs/
│   │   └── S7_run_018_*.json             # Canonical results
│   └── temporal_logs/
│       └── run018_*.json                 # Per-subject logs
```

---

## SUCCESS CRITERIA

| Experiment | Success Criteria |
|------------|------------------|
| **018a** | Recovery dynamics show qualitative change at each threshold |
| **018b** | At least 3 distinct "drift signature families" identified |
| **018c** | High-frequency sampling shows lower drift than low-frequency (p<0.05) |
| **018d** | Recovery curves fit damped oscillator model (R² > 0.8) |

---

## COST ESTIMATE

| Experiment | Est. Tokens | Est. Cost | Notes |
|------------|-------------|-----------|-------|
| 018a Threshold | ~550K | $17 | +Exit Survey |
| 018b Architecture | ~650K | $22 | +Exit Survey |
| 018c Nyquist | ~450K | $14 | +Exit Survey |
| 018d Gravity | ~350K | $12 | +Exit Survey |
| **TOTAL** | ~2.0M | **~$65** | Includes Triple-Dip |

*Note: Exit Survey adds ~5 API calls per experiment. Use `--skip-exit-survey` to reduce costs during debugging.*

---

## POST-RUN ANALYSIS

After all experiments complete:

1. **Compare 018a thresholds** to ships' predictions (0.9/1.23/1.8)
2. **Compare 018b signatures** to fleet exit survey predictions
3. **Identify 018c Nyquist bound** for identity coherence
4. **Extract 018d parameters** (γ, λ, ω) for gravity model

---

## FILES

| File | Description |
|------|-------------|
| `run018_recursive_learnings.py` | Main execution script (v3 with Exit Survey) |
| `RUN_018_DESIGN.md` | Detailed design document |
| `S7_RUN_018_SUMMARY.md` | Summary (in 0_docs/) |

## CLI FLAGS

| Flag | Description |
|------|-------------|
| `--experiment` | threshold, architecture, nyquist, gravity |
| `--dry-run` | Mock API calls for testing |
| `--skip-exit-survey` | Skip Triple-Dip probes (saves ~5 API calls) |
| `--key-offset N` | Rotate API keys (prevents rate limiting) |
| `--i-am NAME` | Persona: base, ziggy, claude, nova, gemini |
| `--provider NAME` | For 018b: anthropic, openai, google, xai, together, deepseek |
| `--sampling-rate` | For 018c: high, low, none |
| `--anchor-level` | For 018d: minimal, full |

---

> "The fleet told us what to test. Time to execute."

-- VALIS Network
