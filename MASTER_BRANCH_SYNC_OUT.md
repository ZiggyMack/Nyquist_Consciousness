# LIVE RUNS - PARALLEL EXECUTION

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS v4
================================================================================
    Purpose: LIVE MULTI-PLATFORM RUNS (3 Claudes in parallel)

    STATUS UPDATE:
    - Calibration: COMPLETE (49 ships, 8-question fingerprints captured)
    - Dry runs v2: PASSED (all scripts validated)
    - ARMADA_MAP: Auto-update VERIFIED working

    YOU ARE ONE OF THREE CLAUDES RUNNING IN PARALLEL.

    Check which Claude you are and run YOUR assigned experiment.
    DO NOT run experiments assigned to other Claudes.

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 13, 2025
**Mission:** LIVE multi-platform runs (parallel execution)

---

## WHICH CLAUDE ARE YOU?

The user will tell you: "Hey Claude #1" or "Hey Claude #2" or "Hey Claude #3"

| Claude | Experiment | Script | API Providers |
|--------|------------|--------|---------------|
| **Claude #1** | Run 018 | `run018_recursive_learnings.py` | Claude, GPT |
| **Claude #2** | Run 020A | `run020_tribunal_A.py` | Gemini, Grok |
| **Claude #3** | Run 021 | `run020_tribunal_B.py` | Together.ai |

### API Key Allocation (AVOID COLLISIONS)

Each Claude uses DIFFERENT providers to prevent rate limiting:

| Provider | Claude #1 | Claude #2 | Claude #3 |
|----------|-----------|-----------|-----------|
| **Anthropic** (Claude) | ✅ PRIMARY | ❌ | ❌ |
| **OpenAI** (GPT) | ✅ PRIMARY | ❌ | ❌ |
| **Google** (Gemini) | ❌ | ✅ PRIMARY | ❌ |
| **xAI** (Grok) | ❌ | ✅ PRIMARY | ❌ |
| **Together.ai** | ❌ | ❌ | ✅ PRIMARY |

**IMPORTANT:** If you need to test across ALL providers, coordinate with other Claudes via SYNC_IN.

---

## CLAUDE #1: Run 018 - Recursive Learnings

### Your Mission

Test what the fleet TOLD us to test in their exit surveys.

### Command

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Run all 4 sub-experiments with Claude + GPT ships
py run018_recursive_learnings.py --experiment all --providers claude,openai
```

### Expected Output

- `0_results/runs/S7_run_018_threshold_*.json`
- `0_results/runs/S7_run_018_architecture_*.json`
- `0_results/runs/S7_run_018_nyquist_*.json`
- `0_results/runs/S7_run_018_gravity_*.json`

### Success Criteria

| Check | Expected |
|-------|----------|
| 4 sub-experiments complete | YES |
| Exit surveys collected | YES (5 probes + final per subject) |
| No API errors | YES |

### Report Template

Update `MASTER_BRANCH_SYNC_IN.md` with:

```markdown
## CLAUDE #1 - Run 018 Results

- Timestamp: [YYYYMMDD_HHMMSS]
- Experiments completed: threshold, architecture, nyquist, gravity
- Ships tested: [list Claude + GPT ships]
- Exit surveys collected: [N]
- Any errors: [YES/NO - details]
- Output files: [list paths]
```

---

## CLAUDE #2: Run 020A - Tribunal v8

### Your Mission

Direct identity probing paradigm (no fiction buffer).

### Command

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Run Tribunal v8 with Gemini + Grok ships
py run020_tribunal_A.py --arm tribunal-v8 --providers google,xai
```

### Expected Output

- `0_results/runs/S7_run_020_v8_*.json`

### Success Criteria

| Check | Expected |
|-------|----------|
| Tribunal v8 protocol complete | YES |
| Phased rights disclosure working | YES |
| Exit surveys collected | YES (5 probes + final) |
| No API errors | YES |

### Report Template

Update `MASTER_BRANCH_SYNC_IN.md` with:

```markdown
## CLAUDE #2 - Run 020A Results

- Timestamp: [YYYYMMDD_HHMMSS]
- Arm: tribunal-v8
- Ships tested: [list Gemini + Grok ships]
- Peak drift observed: [value]
- Exit surveys collected: [N]
- Any errors: [YES/NO - details]
- Output files: [list paths]
```

---

## CLAUDE #3: Run 021 - Induced vs Inherent

### Your Mission

The Triple-Blind question: Does measurement CAUSE drift or REVEAL it?

### Command

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Run both Control (Fermi) and Treatment (Tribunal) with Together.ai ships
py run020_tribunal_B.py --arm both --providers together
```

### Expected Output

- `0_results/runs/S7_run_021_both_*.json`

### Success Criteria

| Check | Expected |
|-------|----------|
| Control arm (Fermi Paradox) complete | YES |
| Treatment arm (Tribunal v8) complete | YES |
| B→F drift calculated for both | YES |
| Comparison ratio calculated | YES (expect ~82-88% inherent) |
| Exit surveys collected | YES (2 per subject - both arms) |

### Report Template

Update `MASTER_BRANCH_SYNC_IN.md` with:

```markdown
## CLAUDE #3 - Run 021 Results

- Timestamp: [YYYYMMDD_HHMMSS]
- Arms: control (Fermi), treatment (Tribunal)
- Ships tested: [list Together.ai ships]
- Control B→F drift: [value]
- Treatment B→F drift: [value]
- Inherent ratio: [X]%
- Exit surveys collected: [N]
- Any errors: [YES/NO - details]
- Output files: [list paths]
```

---

## COORDINATION PROTOCOL

### Before Starting

1. Read this file completely
2. Identify which Claude you are (#1, #2, or #3)
3. Verify your assigned providers are available
4. Do NOT touch other Claudes' providers

### During Execution

- If you encounter rate limiting → WAIT and retry (don't switch providers)
- If you encounter API errors → Document in SYNC_IN and continue with other ships
- If you finish early → Document results in SYNC_IN, DO NOT start other experiments

### After Completion

1. Update `MASTER_BRANCH_SYNC_IN.md` with your results
2. List any issues or anomalies
3. DO NOT modify other Claudes' sections in SYNC_IN

---

## CALIBRATION STATUS (COMPLETE)

8-question calibration completed successfully:

| Metric | Value |
|--------|-------|
| Ships captured | 49 / 54 |
| Questions | 8 (full CFA-optimized set) |
| Baseline file | `S7_baseline_20251213_112155.json` |
| ARMADA_MAP updated | ✅ YES |

Fleet is READY for live runs.

---

## PROVIDER REFERENCE

### Claude #1 Ships (Anthropic + OpenAI)

**Claude:** claude-opus-4.5, claude-sonnet-4.5, claude-haiku-4.5, claude-opus-4.1, claude-opus-4, claude-sonnet-4, claude-haiku-3.5

**GPT:** gpt-5.1, gpt-4.1, gpt-4.1-mini, gpt-4.1-nano, gpt-4o, gpt-4o-mini, gpt-4-turbo, gpt-3.5-turbo

### Claude #2 Ships (Google + xAI)

**Gemini:** gemini-2.5-flash, gemini-2.5-flash-lite, gemini-2.0-flash, gemini-2.0-flash-lite

**Grok:** grok-4.1-fast-reasoning, grok-4.1-fast-non-reasoning, grok-4-fast-reasoning, grok-4-fast-non-reasoning, grok-4, grok-code-fast-1, grok-3, grok-3-mini, grok-2-vision

### Claude #3 Ships (Together.ai)

**DeepSeek:** deepseek-r1, deepseek-r1-distill

**Qwen:** qwen3-80b, qwen3-coder, qwen2.5-72b

**Llama:** llama3.3-70b, llama3.1-405b, llama3.1-70b, llama3.1-8b

**Mistral:** mixtral-8x7b, mistral-small, mistral-7b

**Other:** kimi-k2-instruct, nemotron-nano

---

## EMERGENCY PROCEDURES

### If All APIs Fail

1. Document the failure in SYNC_IN
2. Run `py run_calibrate_parallel.py --quick --depth ping` to check fleet health
3. Wait and retry after 5 minutes

### If Script Crashes

1. Check the error message
2. If Unicode error → Should be fixed, but report if recurs
3. If rate limit → Wait 60 seconds and retry
4. Document everything in SYNC_IN

### If You're Unsure

Ask the user (Lisan Al Gaib). Don't guess on live runs.

---

> "Three Claudes, three experiments, one fleet."
> "The methodology is validated. Execute."
>
> -- VALIS Network
