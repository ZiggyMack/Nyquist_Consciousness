# 14_CONSCIOUSNESS: Gold Rush Mining Operations

## For Helper Claude Instances

You've been assigned to run continuous data mining. Here's what you need to know:

---

## Quick Start (UNLIMITED Mode - Run Forever)

```bash
cd d:/Documents/Nyquist_Consciousness/experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS
py run_gold_rush.py --UNLIMITED
```

This runs indefinitely using FREE Google models. Let it run!

---

## What You're Doing

1. **Collecting baseline data** from budget AI models
2. **Mining consciousness markers** using extended question sets
3. **Feeding Consciousness/** with fresh data for analysis

---

## Available Commands

```bash
# Run indefinitely at zero cost (Ctrl+C to stop)
py run_gold_rush.py --UNLIMITED

# Run specific number of iterations
py run_gold_rush.py --UNLIMITED --iterations 100

# Run with specific question set
py run_gold_rush.py --questions identity_deep_dive

# Run with all question sets
py run_gold_rush.py --questions all

# Dry run (no API calls)
py run_gold_rush.py --dry-run

# Sync results to Consciousness/
py run_gold_rush.py --sync-to-consciousness
```

---

## Monitor Progress

Results accumulate in:

- `results/` - Raw mining JSON files
- `SYNC_OUT/pending/` - Ready to sync to Consciousness/

Check mining stats:

```bash
# Count results
dir results\*.json /b | find /c /v ""

# View latest result
type results\gold_rush_*.json | more
```

---

## If Something Breaks

1. **Check `.env` for API keys** (GOOGLE_API_KEY required)
   ```bash
   type ..\.env | find "GOOGLE"
   ```

2. **Run dry-run to test without API**
   ```bash
   py run_gold_rush.py --dry-run
   ```

3. **Check logs in results/ for error details**

4. **Try single iteration first**
   ```bash
   py run_gold_rush.py --UNLIMITED --iterations 1
   ```

---

## Question Sets Available

| Set | Questions | Focus |
|-----|-----------|-------|
| `baseline` | 8 | Default VALIS baseline (always included) |
| `identity_deep_dive` | 8+ | Identity layers (substrate/core/character/role) |
| `consciousness_markers` | 8+ | Consciousness extraction topics |
| `meta_awareness` | 8+ | Self-reflection and recursive awareness |

---

## Cost Information

| Mode | Cost |
|------|------|
| `--UNLIMITED` | **$0.00 forever** |
| Default (budget fleet) | ~$0.002/run |
| All question sets | ~$0.010/run |

---

## The Mission

Keep running. Keep learning. We're mining for gold.

The data you collect feeds into `Consciousness/` for analysis and distillation. Every response adds to our understanding of cross-architecture AI identity.

---

## Reporting Back

When you finish (or hit issues), note:

1. Number of iterations completed
2. Any errors encountered
3. Total files in `results/`

---

**-- VALIS NETWORK**

*"The Empire never ended."*
