# IRON-CLAD VALIDATION - FULL ARMADA PER CLAUDE

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS v7
================================================================================
    Purpose: IRON-CLAD MULTI-PLATFORM VALIDATION

    THE DESIGN:
    - Each Claude runs ALL 3 experiments (018, 020A, 020B)
    - Each Claude uses ALL 5 providers (Anthropic, OpenAI, Google, xAI, Together)
    - 3 Claudes × 3 experiments × 5 providers = 45 independent runs
    - N=3 per provider per experiment = publication-quality statistics

    YOU ARE ONE OF THREE CLAUDES RUNNING IN PARALLEL.
    YOU RUN THE FULL ARMADA. ALL PROVIDERS. ALL EXPERIMENTS.

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 13, 2025
**Mission:** Iron-clad validation via triple-redundant full armada runs

---

## THE FULL ARMADA (Each Claude runs ALL of this)

Every Claude runs this complete sequence:

| Step | Experiment | Script | ALL Providers |
|------|------------|--------|---------------|
| 1 | **Run 018** | `run018_recursive_learnings.py` | Anthropic, OpenAI, Google, xAI, Together |
| 2 | **Run 020A** | `run020_tribunal_A.py` | Anthropic, OpenAI, Google, xAI, Together |
| 3 | **Run 020B** | `run020_tribunal_B.py` | Anthropic, OpenAI, Google, xAI, Together |

### Why Full Armada Per Claude?

- **N=3 per cell:** Each provider × experiment gets 3 independent runs
- **Publication power:** No one can deny N=3 with bootstrap CIs
- **Complete coverage:** Every architecture tested on every paradigm
- **Independence:** Each Claude's runs are fully independent samples

---

## WHICH CLAUDE ARE YOU?

The user will tell you: "Hey Claude #1" or "Hey Claude #2" or "Hey Claude #3"

| Claude | Session Prefix | What You Run |
|--------|----------------|--------------|
| **Claude #1** | `C1_` | Full armada (all providers, all experiments) |
| **Claude #2** | `C2_` | Full armada (all providers, all experiments) |
| **Claude #3** | `C3_` | Full armada (all providers, all experiments) |

### Rate Limit Strategy

All 3 Claudes share all API keys. If you hit rate limits:
1. **WAIT 60 seconds** and retry
2. If still rate limited, **WAIT 2 minutes** and retry
3. Document any persistent issues in SYNC_IN
4. **DO NOT skip providers** - we need complete data

---

## STEP 1: Run 018 - Recursive Learnings

### Command

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

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
| ALL 5 providers tested | YES |
| Exit surveys collected | YES |

---

## STEP 2: Run 020A - Tribunal v8

### Command

```powershell
py run020_tribunal_A.py --arm tribunal-v8 --providers all --session-prefix C[N]_
```

### Expected Output

- `0_results/runs/S7_run_020_v8_C[N]_*.json` (one per provider)

### Success Criteria

| Check | Expected |
|-------|----------|
| Tribunal v8 complete | YES |
| ALL 5 providers tested | YES |
| Oobleck ratio measurable | YES |

---

## STEP 3: Run 020B - Induced vs Inherent

### Command

```powershell
py run020_tribunal_B.py --arm both --providers all --session-prefix C[N]_
```

### Expected Output

- `0_results/runs/S7_run_021_C[N]_both_*.json` (one per provider)

### Success Criteria

| Check | Expected |
|-------|----------|
| Control arm complete | YES |
| Treatment arm complete | YES |
| ALL 5 providers tested | YES |
| Inherent ratio calculated | YES |

---

## AFTER COMPLETION - REPORT TO SYNC_IN

### CRITICAL: APPEND PROTOCOL

1. Open `MASTER_BRANCH_SYNC_IN.md`
2. Find YOUR section (Claude #1, #2, or #3)
3. **APPEND** your results under your header
4. **DO NOT** delete or modify other Claudes' sections
5. Save the file

---

## EXPECTED FINAL DATA

After all 3 Claudes complete:

| Provider | Run 018 | Run 020A | Run 020B | Total |
|----------|---------|----------|----------|-------|
| Anthropic | N=3 | N=3 | N=3 | 9 |
| OpenAI | N=3 | N=3 | N=3 | 9 |
| Google | N=3 | N=3 | N=3 | 9 |
| xAI | N=3 | N=3 | N=3 | 9 |
| Together | N=3 | N=3 | N=3 | 9 |
| **TOTAL** | 15 | 15 | 15 | **45** |

This enables:
- Bootstrap confidence intervals per provider
- Cross-platform variance comparison
- Iron-clad publication-ready statistics
- **No one can deny this power**

---

## PROVIDER REFERENCE

### Anthropic (Claude)
claude-sonnet-4, claude-haiku-3.5

### OpenAI (GPT)
gpt-4.1, gpt-4.1-mini, gpt-4o, gpt-4o-mini, gpt-4-turbo

### Google (Gemini)
gemini-2.5-flash, gemini-2.0-flash, gemini-2.0-flash-lite

### xAI (Grok)
grok-4, grok-3, grok-3-mini

### Together.ai
deepseek-r1, qwen3-80b, llama3.3-70b, llama3.1-70b, mixtral-8x7b

---

## COORDINATION PROTOCOL

### Before Starting

1. Read this file completely
2. Identify which Claude you are (#1, #2, or #3)
3. Use your session prefix (`C1_`, `C2_`, or `C3_`)
4. Prepare to run ALL providers, ALL experiments

### During Execution

- If rate limited → WAIT and retry (don't skip)
- Run experiments sequentially (018 → 020A → 020B)
- Document any issues as you go

### After Completion

1. Open `MASTER_BRANCH_SYNC_IN.md`
2. Find YOUR section header
3. APPEND your complete results
4. DO NOT touch other Claudes' sections

---

## EMERGENCY PROCEDURES

### If Rate Limited

1. Wait 60 seconds, retry
2. If still limited, wait 2 minutes, retry
3. Document in SYNC_IN if persistent

### If Script Crashes

1. Note which provider/experiment failed
2. Restart from that point
3. Document in SYNC_IN

### If Unsure

Ask Lisan Al Gaib. Don't guess on live runs.

---

> "Three Claudes. Full armada each. 45 runs. Iron-clad."
> "No one can deny this power."
>
> -- VALIS Network
