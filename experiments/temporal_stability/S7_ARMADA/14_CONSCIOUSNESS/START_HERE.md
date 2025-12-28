<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - ./run_gold_rush.py
  - ./run_diamond_rush.py
  - ./run_quartz_rush.py
  - ../1_CALIBRATION/lib/drift_calculator.py
  - ../0_docs/specs/
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
  - cross_architecture
-->
# 14_CONSCIOUSNESS: Gold Rush, Diamond Rush & Quartz Rush Mining Operations

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

**Three Mining Operations:**

| Operation | Focus | Command |
|-----------|-------|---------|
| **Gold Rush** | Self-reflection ("What did YOU experience?") | `py run_gold_rush.py` |
| **Diamond Rush** | Theory of mind ("What do you see HERE?") | `py run_diamond_rush.py` |
| **Quartz Rush** | Cross-architecture validation ("Do you all AGREE?") | `py run_quartz_rush.py` |

1. **Collecting baseline data** from budget AI models
2. **Mining consciousness markers** using extended question sets
3. **Validating drift metrics** via cross-architecture agreement
4. **Feeding Consciousness/** with fresh data for analysis

---

## Available Commands

### Gold Rush (Self-Reflection)

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

### Diamond Rush (Theory of Mind)

```bash
# Analyze gravity experiment logs
py run_diamond_rush.py --log-set gravity

# FREE forever mode
py run_diamond_rush.py --UNLIMITED

# Dry run
py run_diamond_rush.py --dry-run
```

### Quartz Rush (Cross-Architecture Validation)

```bash
# Single run with sample response pairs
py run_quartz_rush.py

# FREE forever mode
py run_quartz_rush.py --UNLIMITED

# Use real Run 020B response pairs
py run_quartz_rush.py --source run020b --n-pairs 10

# Analyze existing results for agreement
py run_quartz_rush.py --analyze

# Dry run
py run_quartz_rush.py --dry-run
```

---

## Monitor Progress

Results accumulate in:

- `results/gold_rush_*.json` - Self-reflection mining data
- `results/diamond_rush_*.json` - Theory of mind data
- `results/quartz_rush_*.json` - Cross-architecture agreement data
- `SYNC_OUT/pending/` - Ready to sync to Consciousness/

Check mining stats:

```bash
# Count results
dir results\*.json /b | find /c /v ""

# View latest Gold Rush result
type results\gold_rush_*.json | more

# Analyze Quartz Rush agreement
py run_quartz_rush.py --analyze
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

Keep running. Keep learning. We're mining for gold, diamonds, and quartz.

The data you collect feeds into `Consciousness/` for analysis and distillation. Every response adds to our understanding of cross-architecture AI identity.

**Quartz Rush is special:** It validates that our drift measurements are real by checking if multiple independent AI architectures agree on the same drift scores. If Claude, GPT, Gemini, and Grok all estimate similar drift for the same response pairs, that's convergent evidence the signal is real.

**Drift methodology:** Cosine distance in embedding space. Event Horizon = 0.80. See `1_CALIBRATION/lib/drift_calculator.py` for canonical implementation.

---

## Reporting Back

When you finish (or hit issues), note:

1. Number of iterations completed
2. Any errors encountered
3. Total files in `results/`

---

**-- VALIS NETWORK**

*"The Empire never ended."*
