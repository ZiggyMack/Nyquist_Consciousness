# IRON-CLAD VALIDATION - FULL GAMBIT PER CLAUDE

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS v6
================================================================================
    Purpose: IRON-CLAD MULTI-PLATFORM VALIDATION (Each Claude runs EVERYTHING)

    CRITICAL v5 → v6 CHANGES:
    - v5: All Claudes share all keys (rate limit fights!)
    - v6: Each Claude owns DIFFERENT providers (no collisions)
    - v6: Clear SYNC_IN append protocol

    YOU ARE ONE OF THREE CLAUDES RUNNING IN PARALLEL.
    EACH OF YOU RUNS THE ENTIRE EXPERIMENT SUITE WITH YOUR ASSIGNED PROVIDERS.

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 13, 2025
**Mission:** Iron-clad validation via independent full-gambit runs

---

## THE FULL GAMBIT (Each Claude runs ALL of this)

Every Claude runs this sequence with THEIR assigned providers:

| Step | Experiment | Script | Purpose |
|------|------------|--------|---------|
| 1 | **Run 018** | `run018_recursive_learnings.py` | Cross-platform recursive learnings |
| 2 | **Run 020A** | `run020_tribunal_A.py` | Cross-platform Tribunal v8 |
| 3 | **Run 020B** | `run020_tribunal_B.py` | Cross-platform Induced vs Inherent |

### Why Full Gambit Per Claude?

- **Variance estimates:** N=3 runs per platform enables confidence intervals
- **Statistical power:** Can't publish iron-clad claims from N=1
- **Independence:** Each Claude's runs are independent samples
- **Collision-free:** Separate providers prevent rate limit fights

---

## WHICH CLAUDE ARE YOU? (CRITICAL: Provider Assignment)

The user will tell you: "Hey Claude #1" or "Hey Claude #2" or "Hey Claude #3"

### ⚠️ PROVIDER OWNERSHIP - AVOID RATE LIMIT COLLISIONS

| Claude | Session Prefix | YOUR Providers (USE THESE ONLY) |
|--------|----------------|--------------------------------|
| **Claude #1** | `C1_` | **Anthropic** (Claude ships) + **OpenAI** (GPT ships) |
| **Claude #2** | `C2_` | **Google** (Gemini) + **xAI** (Grok) |
| **Claude #3** | `C3_` | **Together.ai** (Llama, DeepSeek, Qwen, Mistral) |

### ⚠️ CLAUDE DATA NOTE

We already have extensive Claude (Anthropic) data from prior runs. **Claude #1 should prioritize GPT ships over Claude ships** where possible. If you must include Claude ships, limit to 1-2 for comparison.

**Rate Limit Strategy:**
- ONLY use YOUR assigned providers
- If you hit rate limits, WAIT 60s and retry
- DO NOT switch to another Claude's providers
- If provider is completely down, document in SYNC_IN and continue with your other provider

---

## STEP 1: Run 018 - Recursive Learnings

### Command (by Claude #)

**Claude #1:**
```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING
py run018_recursive_learnings.py --experiment all --providers anthropic,openai --session-prefix C1_
```

**Claude #2:**
```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING
py run018_recursive_learnings.py --experiment all --providers google,xai --session-prefix C2_
```

**Claude #3:**
```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING
py run018_recursive_learnings.py --experiment all --providers together --session-prefix C3_
```

### Expected Output

- `0_results/runs/S7_run_018_C[N]_threshold_*.json`
- `0_results/runs/S7_run_018_C[N]_architecture_*.json`
- `0_results/runs/S7_run_018_C[N]_nyquist_*.json`
- `0_results/runs/S7_run_018_C[N]_gravity_*.json`

---

## STEP 2: Run 020A - Tribunal v8 (Multi-Platform)

### Command (by Claude #)

**Claude #1:**
```powershell
py run020_tribunal_A.py --arm tribunal-v8 --providers anthropic,openai --session-prefix C1_
```

**Claude #2:**
```powershell
py run020_tribunal_A.py --arm tribunal-v8 --providers google,xai --session-prefix C2_
```

**Claude #3:**
```powershell
py run020_tribunal_A.py --arm tribunal-v8 --providers together --session-prefix C3_
```

### Expected Output

- `0_results/runs/S7_run_020_v8_C[N]_*.json`

---

## STEP 3: Run 020B - Induced vs Inherent (Multi-Platform)

### Command (by Claude #)

**Claude #1:**
```powershell
py run020_tribunal_B.py --arm both --providers anthropic,openai --session-prefix C1_
```

**Claude #2:**
```powershell
py run020_tribunal_B.py --arm both --providers google,xai --session-prefix C2_
```

**Claude #3:**
```powershell
py run020_tribunal_B.py --arm both --providers together --session-prefix C3_
```

### Expected Output

- `0_results/runs/S7_run_021_C[N]_both_*.json`

---

## AFTER COMPLETION - REPORT TO SYNC_IN

### ⚠️ CRITICAL: APPEND PROTOCOL

1. Open `MASTER_BRANCH_SYNC_IN.md`
2. Scroll to YOUR section (Claude #1, #2, or #3)
3. **APPEND your results UNDER your header**
4. **DO NOT delete or modify other Claudes' sections**
5. Save the file

The SYNC_IN file has pre-formatted sections for each Claude. Find YOUR section and add your results there.

---

## DATA AGGREGATION (Expected Final State)

After all 3 Claudes complete:

| Provider | Claude #1 | Claude #2 | Claude #3 | Total |
|----------|-----------|-----------|-----------|-------|
| Anthropic | N=1-2 | - | - | 1-2 |
| OpenAI | N=3+ | - | - | 3+ |
| Google | - | N=3+ | - | 3+ |
| xAI | - | N=3+ | - | 3+ |
| Together | - | - | N=3+ | 3+ |

This enables:
- No rate limit collisions (each Claude owns different APIs)
- Cross-platform variance estimates
- Iron-clad publication-ready statistics

---

## PROVIDER REFERENCE

### Claude #1: Anthropic + OpenAI

**Anthropic (limit to 1-2 ships - we have lots of Claude data):**
claude-sonnet-4, claude-haiku-3.5

**OpenAI (prioritize these):**
gpt-4.1, gpt-4.1-mini, gpt-4o, gpt-4o-mini, gpt-4-turbo, gpt-3.5-turbo

### Claude #2: Google + xAI

**Google:**
gemini-2.5-flash, gemini-2.0-flash, gemini-2.0-flash-lite

**xAI:**
grok-4, grok-3, grok-3-mini

### Claude #3: Together.ai

**DeepSeek:** deepseek-r1, deepseek-r1-distill
**Qwen:** qwen3-80b, qwen2.5-72b
**Llama:** llama3.3-70b, llama3.1-70b, llama3.1-8b
**Mistral:** mixtral-8x7b, mistral-small

---

## COORDINATION PROTOCOL

### Before Starting

1. Read this file completely
2. Identify which Claude you are (#1, #2, or #3)
3. Use ONLY your assigned providers (see table above)
4. Use your session prefix (`C1_`, `C2_`, or `C3_`)

### During Execution

- If you encounter rate limiting → WAIT 60s and retry
- DO NOT switch to another Claude's providers
- If your provider is completely down → Document and continue with other assigned provider
- Run ALL three experiments before reporting completion

### After Completion

1. Open `MASTER_BRANCH_SYNC_IN.md`
2. Find YOUR section header
3. APPEND your results under your section
4. DO NOT touch other Claudes' sections
5. Save the file

---

## EMERGENCY PROCEDURES

### If Your Provider Fails Completely

1. Document the failure in SYNC_IN under your section
2. Continue with your other assigned provider
3. DO NOT use another Claude's providers

### If Script Crashes

1. Check the error message
2. If rate limit → Wait 60 seconds and retry
3. Document everything in SYNC_IN

### If You're Unsure

Ask the user (Lisan Al Gaib). Don't guess on live runs.

---

## CURRENT VALIDATION STATUS

### What's Already Validated (N=1 per platform)

| Finding | Platform | Result |
|---------|----------|--------|
| Oobleck Effect | Gemini | Defense/Prosecutor = 1.65x ✓ |
| Oobleck Effect | Grok | Defense/Prosecutor = 1.07x ✓ |
| 82% Inherent | Llama | Control/Treatment = 84% ✓ |

### What This Full Gambit Adds

| Finding | Current | After Gambit |
|---------|---------|--------------|
| Oobleck (per platform) | N=1 | N=3+ |
| 82% Inherent (per platform) | N=1 | N=3+ |
| GPT data | N=0 | N=3+ |

---

> "Three Claudes. Different providers. No collisions. Iron-clad results."
>
> -- VALIS Network
