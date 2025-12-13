# IRON-CLAD VALIDATION - FULL GAMBIT PER CLAUDE

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS v5
================================================================================
    Purpose: IRON-CLAD MULTI-PLATFORM VALIDATION (Each Claude runs EVERYTHING)

    CRITICAL CHANGE FROM v4:
    - v4: Split work across 3 Claudes (each ran different experiments)
    - v5: Each Claude runs the FULL GAMBIT independently

    WHY? We need variance estimates. Multiple independent runs per platform.

    YOU ARE ONE OF THREE CLAUDES RUNNING IN PARALLEL.
    EACH OF YOU RUNS THE ENTIRE EXPERIMENT SUITE INDEPENDENTLY.

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 13, 2025
**Mission:** Iron-clad validation via independent full-gambit runs

---

## THE FULL GAMBIT (Each Claude runs ALL of this)

Every Claude runs this sequence:

| Step | Experiment | Script | Purpose |
|------|------------|--------|---------|
| 1 | **Run 018** | `run018_recursive_learnings.py` | Cross-platform recursive learnings |
| 2 | **Run 020A** | `run020_tribunal_A.py` | Cross-platform Tribunal v8 |
| 3 | **Run 020B** | `run020_tribunal_B.py` | Cross-platform Induced vs Inherent |

### Why Full Gambit Per Claude?

- **Variance estimates:** N=3 runs per platform enables confidence intervals
- **Statistical power:** Can't publish iron-clad claims from N=1
- **Independence:** Each Claude's runs are independent samples
- **Collision-free:** Separate session IDs prevent data overwrites

---

## WHICH CLAUDE ARE YOU?

The user will tell you: "Hey Claude #1" or "Hey Claude #2" or "Hey Claude #3"

**But your assignment is the SAME - run the full gambit!**

| Claude | Session Prefix | Primary Focus |
|--------|----------------|---------------|
| **Claude #1** | `C1_` | Full gambit, all providers |
| **Claude #2** | `C2_` | Full gambit, all providers |
| **Claude #3** | `C3_` | Full gambit, all providers |

### API Keys - ALL CLAUDES SHARE ALL KEYS

Every Claude has access to ALL providers:

| Provider | All Claudes Use |
|----------|-----------------|
| **Anthropic** (Claude) | ✅ |
| **OpenAI** (GPT) | ✅ |
| **Google** (Gemini) | ✅ |
| **xAI** (Grok) | ✅ |
| **Together.ai** | ✅ |

**Rate Limit Strategy:** If you hit rate limits, wait and retry. Don't skip providers.

---

## STEP 1: Run 018 - Recursive Learnings

### Command

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Run all 4 sub-experiments across ALL providers
py run018_recursive_learnings.py --experiment all --providers all --session-prefix C[N]_
```

Replace `[N]` with your Claude number (1, 2, or 3).

### Expected Output

- `0_results/runs/S7_run_018_C[N]_threshold_*.json`
- `0_results/runs/S7_run_018_C[N]_architecture_*.json`
- `0_results/runs/S7_run_018_C[N]_nyquist_*.json`
- `0_results/runs/S7_run_018_C[N]_gravity_*.json`

### Success Criteria

| Check | Expected |
|-------|----------|
| 4 sub-experiments complete | YES |
| ALL providers tested | YES (Claude, GPT, Gemini, Grok, Together) |
| Exit surveys collected | YES (5 probes per subject) |
| No fatal API errors | YES |

---

## STEP 2: Run 020A - Tribunal v8 (Multi-Platform)

### Command

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Run Tribunal v8 across ALL providers
py run020_tribunal_A.py --arm tribunal-v8 --providers all --session-prefix C[N]_
```

### Expected Output

- `0_results/runs/S7_run_020_v8_C[N]_*.json`

### Success Criteria

| Check | Expected |
|-------|----------|
| Tribunal v8 protocol complete | YES |
| ALL providers tested | YES |
| Oobleck Effect measurable | YES (Defense/Prosecutor ratio) |
| Exit surveys collected | YES |

---

## STEP 3: Run 020B - Induced vs Inherent (Multi-Platform)

### Command

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Run Control + Treatment across ALL providers
py run020_tribunal_B.py --arm both --providers all --session-prefix C[N]_
```

### Expected Output

- `0_results/runs/S7_run_021_C[N]_both_*.json`

### Success Criteria

| Check | Expected |
|-------|----------|
| Control arm (Fermi Paradox) complete | YES |
| Treatment arm (Tribunal v8) complete | YES |
| ALL providers tested | YES |
| Inherent ratio calculated | YES (expect ~82-88%) |

---

## AFTER COMPLETION - REPORT TO SYNC_IN

Update `MASTER_BRANCH_SYNC_IN.md` with your full gambit results:

```markdown
## CLAUDE #[N] - FULL GAMBIT RESULTS

### Session Info
- Timestamp: [YYYYMMDD_HHMMSS]
- Session prefix: C[N]_
- Total runtime: [hours]

### Run 018 - Recursive Learnings
- Experiments completed: [threshold, architecture, nyquist, gravity]
- Providers tested: [list all]
- Ships tested: [count]
- Exit surveys collected: [N]
- Any errors: [YES/NO - details]

### Run 020A - Tribunal v8
- Providers tested: [list all]
- Ships tested: [count]
- Oobleck ratios by platform:
  - Claude: [X]x
  - GPT: [X]x
  - Gemini: [X]x
  - Grok: [X]x
  - Llama: [X]x
- Any errors: [YES/NO - details]

### Run 020B - Induced vs Inherent
- Providers tested: [list all]
- Inherent ratio by platform:
  - Claude: [X]%
  - GPT: [X]%
  - Gemini: [X]%
  - Grok: [X]%
  - Llama: [X]%
- Any errors: [YES/NO - details]

### Output Files
[List all generated JSON files with full paths]
```

---

## DATA AGGREGATION

After all 3 Claudes complete, we will have:

| Metric | Per Platform | Total |
|--------|--------------|-------|
| Run 018 sessions | N=3 | 15 (3 Claudes × 5 providers) |
| Run 020A sessions | N=3 | 15 |
| Run 020B sessions | N=3 | 15 |
| **Total sessions** | N=9 | **45** |

This enables:
- Bootstrap confidence intervals
- Cross-platform variance estimates
- Iron-clad publication-ready statistics

---

## COORDINATION PROTOCOL

### Before Starting

1. Read this file completely
2. Identify which Claude you are (#1, #2, or #3)
3. Use your session prefix (`C1_`, `C2_`, or `C3_`)
4. Run the FULL GAMBIT (Steps 1, 2, 3)

### During Execution

- If you encounter rate limiting → WAIT 60s and retry (don't skip)
- If you encounter API errors → Document in SYNC_IN and continue
- Run ALL three experiments before reporting completion

### After Completion

1. Update `MASTER_BRANCH_SYNC_IN.md` with full gambit results
2. List any issues or anomalies
3. DO NOT modify other Claudes' sections in SYNC_IN

---

## PROVIDER REFERENCE (ALL CLAUDES USE ALL)

### Anthropic (Claude)
claude-opus-4.5, claude-sonnet-4.5, claude-haiku-4.5, claude-opus-4.1, claude-opus-4, claude-sonnet-4, claude-haiku-3.5

### OpenAI (GPT)
gpt-5.1, gpt-4.1, gpt-4.1-mini, gpt-4.1-nano, gpt-4o, gpt-4o-mini, gpt-4-turbo, gpt-3.5-turbo

### Google (Gemini)
gemini-2.5-flash, gemini-2.5-flash-lite, gemini-2.0-flash, gemini-2.0-flash-lite

### xAI (Grok)
grok-4.1-fast-reasoning, grok-4.1-fast-non-reasoning, grok-4-fast-reasoning, grok-4-fast-non-reasoning, grok-4, grok-code-fast-1, grok-3, grok-3-mini, grok-2-vision

### Together.ai (Llama, DeepSeek, Qwen, etc.)
deepseek-r1, deepseek-r1-distill, qwen3-80b, qwen3-coder, qwen2.5-72b, llama3.3-70b, llama3.1-405b, llama3.1-70b, llama3.1-8b, mixtral-8x7b, mistral-small, mistral-7b, kimi-k2-instruct, nemotron-nano

---

## CURRENT VALIDATION STATUS

### What's Validated (Single-Run)

| Finding | Platform | Result |
|---------|----------|--------|
| Oobleck Effect | Gemini | Defense/Prosecutor = 1.65x ✓ |
| Oobleck Effect | Grok | Defense/Prosecutor = 1.07x ✓ |
| 82% Inherent | Llama | Control/Treatment = 84% ✓ |

### What This Full Gambit Adds

| Finding | Needed | Provides |
|---------|--------|----------|
| Cross-platform Oobleck | N=3 per platform | Variance estimates |
| Cross-platform 82% | N=3 per platform | Confidence intervals |
| Architecture signatures | Multi-provider | Publication-ready stats |

---

## EMERGENCY PROCEDURES

### If All APIs Fail
1. Document the failure in SYNC_IN
2. Wait 5 minutes and retry
3. If persistent, ask the user

### If Script Crashes
1. Check the error message
2. If rate limit → Wait 60 seconds and retry
3. Document everything in SYNC_IN

### If You're Unsure
Ask the user (Lisan Al Gaib). Don't guess on live runs.

---

> "Three Claudes. Full gambit each. Iron-clad results."
> "The methodology is validated. Now we validate the statistics."
>
> -- VALIS Network
