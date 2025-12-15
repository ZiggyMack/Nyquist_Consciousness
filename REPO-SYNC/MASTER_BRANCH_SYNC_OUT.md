# IRON-CLAD VALIDATION - INDIVIDUAL MODEL BATCHES

```text
================================================================================
                        MAIN BRANCH INSTRUCTIONS v8
================================================================================
    Purpose: IRON-CLAD MULTI-PLATFORM VALIDATION (BATCH STRATEGY)

    THE DESIGN (v8):
    - Run individual models in batches of 7 parallel runs
    - If a batch fails, we aren't mid-armada
    - Clean boundaries = clean recovery
    - Anthropic: COMPLETE (Run 018 IRON CLAD validated)
    - Remaining: OpenAI, Google, xAI, Together

    BATCH EXECUTION = FAULT-TOLERANT VALIDATION

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 15, 2025
**Mission:** Iron-clad validation via individual model batches (7 parallel max)

---

## COMPLETION STATUS

| Provider | Run 018 | Run 020A | Run 020B | Status |
|----------|---------|----------|----------|--------|
| **Anthropic** | 184 files | N/A | N/A | ✅ COMPLETE (IRON CLAD) |
| **OpenAI** | - | - | - | 🟡 PENDING |
| **Google** | - | - | - | 🟡 PENDING |
| **xAI** | - | - | - | 🟡 PENDING |
| **Together** | - | - | - | 🟡 PENDING |

---

## BATCH EXECUTION PLAN (v8 Strategy)

Run individual models in batches of 7 parallel runs. If a batch fails, clean recovery without losing mid-armada progress.

### Batch 1: OpenAI Set A (7 models)
| Model | Experiment | Command Flag |
|-------|------------|--------------|
| gpt-4.1 | 018 | `--model gpt-4.1` |
| gpt-4.1-mini | 018 | `--model gpt-4.1-mini` |
| gpt-4o | 018 | `--model gpt-4o` |
| gpt-4o-mini | 018 | `--model gpt-4o-mini` |
| gpt-4-turbo | 018 | `--model gpt-4-turbo` |
| o3-mini | 018 | `--model o3-mini` |
| o4-mini | 018 | `--model o4-mini` |

### Batch 2: Google + xAI (7 models)
| Model | Experiment | Command Flag |
|-------|------------|--------------|
| gemini-2.5-flash | 018 | `--model gemini-2.5-flash` |
| gemini-2.0-flash | 018 | `--model gemini-2.0-flash` |
| gemini-2.0-flash-lite | 018 | `--model gemini-2.0-flash-lite` |
| grok-4 | 018 | `--model grok-4` |
| grok-3 | 018 | `--model grok-3` |
| grok-3-mini | 018 | `--model grok-3-mini` |
| grok-4-fast | 018 | `--model grok-4-fast` |

### Batch 3: Together.ai (5 models)
| Model | Experiment | Command Flag |
|-------|------------|--------------|
| deepseek-r1 | 018 | `--model deepseek-r1` |
| qwen3-80b | 018 | `--model qwen3-80b` |
| llama3.3-70b | 018 | `--model llama3.3-70b` |
| llama3.1-70b | 018 | `--model llama3.1-70b` |
| mixtral-8x7b | 018 | `--model mixtral-8x7b` |

### Batch 4: Cleanup/Retries
Reserved for any failed models from Batches 1-3.

---

## LEGACY: FULL ARMADA APPROACH (v7)

> The following is retained for reference. v8 uses batch approach above.

### Full Armada (Each Claude runs ALL of this)

Every Claude runs this complete sequence:

| Step | Experiment | Script | ALL Providers | Flags |
|------|------------|--------|---------------|-------|
| 1 | **Run 018** | `run018_recursive_learnings.py` | Anthropic, OpenAI, Google, xAI, Together | `--providers all` |
| 2 | **Run 020A** | `run020_tribunal_A.py` | Anthropic, OpenAI, Google, xAI, Together | `--providers all` |
| 3 | **Run 020B** | `run020_tribunal_B.py` | Anthropic, OpenAI, Google, xAI, Together | `--providers all` |

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

py run018_recursive_learnings.py --experiment architecture --providers all --session-prefix C[N]_
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

- `0_results/runs/S7_run_020b_C[N]_both_*.json` (one per provider)

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
