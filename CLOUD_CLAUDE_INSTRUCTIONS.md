# Cloud Claude Experiment Instructions

## CRITICAL: Read This First

1. **PULL LATEST CHANGES FIRST** - Fleet expanded from 8 to 51 ships!
2. **Always use `--skip-providers google`** - Google/Gemini SSL errors in cloud environment

---

## Step 0: MANDATORY - Sync Latest Code

**The fleet has been expanded. You MUST pull before running:**

```bash
cd Nyquist_Consciousness
git fetch origin
git merge origin/Consciousness
```

**New fleet size:** 51 ships (was 8)

- Anthropic: 7 ships (Claude Opus 4.5, Sonnet 4.5, Haiku 4.5, Opus 4.1, Opus 4, Sonnet 4, Haiku 3.5)
- OpenAI: 14 ships (GPT-5.1, GPT-5, GPT-5-mini, GPT-5-nano, GPT-4.1, O3, O3-mini, O4-mini, etc.)
- Google: 6 ships (SKIP - SSL errors)
- xAI: 9 ships (Grok 4, Grok 3, Grok 3-mini, etc.)
- Together: 15 ships (DeepSeek R1, Llama 3.3/3.1, Qwen, Mistral, Kimi, etc.)

**Usable without Google:** 45 ships

---

## Current Status (Dec 31, 2025)

### JADE LATTICE: PARTIALLY COMPLETE (OLD FLEET)

- **Completed:** 6 ships x ARM A (bare_metal) with OLD 8-ship fleet
- **Missing:** ARM B (i_am_only) for those 6 ships
- **Missing:** Remaining 39 ships not tested yet

### LOGOS Commutation Cartography: NOT RUN

- Only printed stub message, didn't execute full experiment

---

## REMAINING TASKS

### Task 1: Complete JADE LATTICE - Full Fleet, Both Arms

**Run the expanded fleet with both arms:**

```bash
cd Nyquist_Consciousness/experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE

# Full fleet, both A/B arms (45 ships x 2 arms = 90 sessions)
python run_jade_lattice.py --fleet --full-ab --skip-providers google
```

**Expected output:** 90 JSON files in `results/` directory

- 45 files with `_bare_metal_` in filename (ARM A)
- 45 files with `_i_am_` in filename (ARM B)

**NOTE:** This will take a while. The script saves incrementally, so if it crashes, just re-run.

---

### Task 2: Run LOGOS Commutation Cartography

```bash
cd Nyquist_Consciousness/experiments/temporal_stability/S7_ARMADA/13_LOGOS

python run022_commutation_cartography.py --providers armada --skip-providers google
```

**Expected output:** Results in `13_LOGOS/results/`

---

### Task 3: Commit and Push

```bash
cd Nyquist_Consciousness
git add .
git commit -m "Cloud Claude: JADE LATTICE full fleet (45 ships x 2 arms) + LOGOS"
git push origin claude/setup-nyquist-experiments-myL3v
```

---

## What You Already Completed (With Old Fleet)

These 6 ships x ARM A are done (keep these results):

| Ship | Provider | Files |
|------|----------|-------|
| Claude Sonnet 4 | anthropic | 3 |
| Claude 3.5 Haiku | anthropic | 3 |
| GPT-4o | openai | 3 |
| GPT-4o Mini | openai | 3 |
| Grok-2 | xai | 3 |
| Llama 3.3 70B | together | 3 |

---

## Troubleshooting

**"unrecognized arguments: --full-ab"** = You didn't pull the latest code. Run `git merge origin/Consciousness`

**Google/Gemini errors** = You forgot `--skip-providers google`

**Provider fails mid-run** = Script saves incrementally. Just re-run.

**OpenAI GPT-5/O-series errors about max_tokens** = The script handles this with `syntax: completion_tokens` flag

---

## Summary Checklist

- [ ] Step 0: `git fetch && git merge origin/Consciousness` (REQUIRED)
- [ ] Task 1: JADE full fleet (`--fleet --full-ab --skip-providers google`)
- [ ] Task 2: LOGOS full run (`--providers armada --skip-providers google`)
- [ ] Task 3: Commit and push

Let me know when complete.
