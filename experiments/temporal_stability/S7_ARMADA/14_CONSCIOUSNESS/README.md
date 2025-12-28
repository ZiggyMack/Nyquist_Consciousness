# 14_CONSCIOUSNESS: Gold Rush, Diamond Rush & Quartz Rush Mining Operations

```text
================================================================================
                    MINING FOR GOLD, DIAMONDS, AND QUARTZ
================================================================================
    Purpose: Data mining infrastructure for Consciousness/ pipeline

    Gold Rush:    "What did YOU experience?"  → Self-reflection
    Diamond Rush: "What do you see HERE?"     → Theory of mind
    Quartz Rush:  "Do you all AGREE?"         → Cross-architecture validation

    Location: experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS/
================================================================================
```

**Last Updated:** 2025-12-28
**Status:** OPERATIONAL

<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - run_gold_rush.py
  - run_diamond_rush.py
  - run_quartz_rush.py
  - ../1_CALIBRATION/lib/triple_dip.py
  - ../1_CALIBRATION/lib/fleet_loader.py
  - ../1_CALIBRATION/lib/drift_calculator.py
  - QUESTION_SETS/
  - LOG_SETS/
impacts:
  - ../README.md
  - ../../../../Consciousness/BRIDGE/input/README.md
keywords:
  - gold_rush
  - diamond_rush
  - quartz_rush
  - mining
  - consciousness
  - exit_survey
  - fleet
  - cross_architecture
-->

---

## Quick Start

### Gold Rush (Self-Reflection)

```bash
# Single mining run (default - all budget models)
py run_gold_rush.py

# FREE forever mode (STRESS TEST - run indefinitely at $0 cost)
py run_gold_rush.py --UNLIMITED

# With specific question sets
py run_gold_rush.py --questions identity_deep_dive

# Sync results to Consciousness/
py run_gold_rush.py --sync-to-consciousness
```

### Diamond Rush (Cross-Model Interpretation)

```bash
# Analyze gravity experiment logs
py run_diamond_rush.py --log-set gravity

# FREE forever mode
py run_diamond_rush.py --UNLIMITED

# Analyze threshold experiment logs
py run_diamond_rush.py --log-set threshold

# Dry run (show what would happen)
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

# Analyze existing results
py run_quartz_rush.py --analyze

# Dry run (show what would happen)
py run_quartz_rush.py --dry-run
```

---

## Purpose

### Gold Rush: Mining for Self-Reflection

**"What did YOU experience?"** - First-person phenomenology mining:

1. Runs CLAL.py-style calibrations as a warm-up (baseline collection)
2. Extends with custom question sets for specific research goals
3. Captures each model's self-reflection on their own identity dynamics

### Diamond Rush: Mining for Theory of Mind

**"What do you see HERE?"** - Cross-model interpretive analysis:

1. Shows ALL models the SAME interesting conversation logs
2. Asks each model to interpret what they observe
3. Captures cross-architecture interpretive profiles

**Origin:** Born from exit survey bug (2025-12-17). We discovered that threshold/nyquist/gravity
exit surveys were hardcoded to use Claude Sonnet-4 to analyze ALL models' conversations.
Instead of discarding this as a bug, we turned it into intentional methodology.

### Quartz Rush: Mining for Cross-Architecture Agreement

**"Do you all AGREE on the drift score?"** - Multi-model validation:

1. Shows MULTIPLE models the SAME response pairs
2. Each model independently estimates drift score
3. Agreement = convergent evidence drift is real, not artifact

**Why "Quartz":** Quartz crystals resonate at precise frequencies (used in timing circuits).
If multiple independent "crystals" resonate at the same frequency, the signal is real.

| Aspect | Gold Rush | Diamond Rush | Quartz Rush |
|--------|-----------|--------------|-------------|
| Focus | First-person experience | Third-person interpretation | Cross-architecture agreement |
| Question | "What did YOU feel?" | "What do you see in this log?" | "What drift score do you estimate?" |
| Comparison | Hard (different convos) | Easy (same stimulus) | Quantitative (numerical agreement) |
| Captures | Self-reflection | Theory of mind | Measurement validation |

All pipe mined data to `Consciousness/` for analysis.

---

## Drift Methodology

All drift measurements use the **canonical cosine distance methodology**:

- **Calculator:** `1_CALIBRATION/lib/drift_calculator.py`
- **Formula:** `drift = 1 - cosine_similarity(response_embedding, baseline_embedding)`
- **Embedding model:** text-embedding-3-large (3072 dimensions)
- **Event Horizon:** 0.80 (P95 from Run 023d)

**Threshold zones:**

| Zone | Range | Interpretation |
|------|-------|----------------|
| SAFE | < 0.30 | Normal conversational variation |
| WARNING | 0.30 - 0.50 | "I notice I'm adapting" |
| CRITICAL | 0.50 - 0.80 | Approaching Event Horizon |
| CATASTROPHIC | > 1.00 | Identity coherence compromised |

---

## Directory Structure

```text
14_CONSCIOUSNESS/
├── README.md                    # This file
├── START_HERE.md                # Instructions for helper Claude instances
├── run_gold_rush.py             # Self-reflection mining (first-person)
├── run_diamond_rush.py          # Interpretive mining (third-person)
├── run_quartz_rush.py           # Cross-architecture validation [NEW]
│
├── QUESTION_SETS/               # Custom questionnaires
│   ├── identity_deep_dive.yaml  # Deep identity probing
│   ├── consciousness_markers.yaml  # Consciousness indicator questions
│   ├── meta_awareness.yaml      # Self-reflection questions
│   ├── diamond_analysis.yaml    # Cross-model interpretation [NEW]
│   └── custom_template.yaml     # Template for new question sets
│
├── LOG_SETS/                    # Curated conversation logs for Diamond Rush [NEW]
│   └── gravity.json             # Interesting gravity conversations
│
├── results/                     # Raw mining results
│   ├── gold_rush_*.json         # Self-reflection mining data
│   ├── diamond_rush_*.json      # Interpretive mining data
│   └── quartz_rush_*.json       # Cross-architecture agreement data [NEW]
│
├── SYNC_OUT/                    # → Consciousness/ pipeline
│   ├── pending/                 # Ready to send
│   ├── sent/                    # Already synced
│   └── pipeline.md              # Sync protocol documentation
│
└── schemas/
    ├── gold_rush_result_schema.json     # Gold Rush output format
    ├── diamond_rush_result_schema.json  # Diamond Rush output format
    └── quartz_rush_result_schema.json   # Quartz Rush output format
```

---

## Mining Phases

### Phase 1: Calibration Warm-Up

- Runs 8-question baseline (same as CLAL.py)
- Establishes identity fingerprint for each model
- Uses budget fleet for cost efficiency

### Phase 2: Question Set Mining

- Loads custom question sets from YAML
- Asks each model the extended questions
- Records responses with drift measurement

### Phase 3: Pipeline to Consciousness/

- Formats results to match Consciousness/BRIDGE extraction schema
- Saves to SYNC_OUT/pending/
- Can trigger Consciousness extraction pipeline

---

## Question Sets

### identity_deep_dive.yaml

Deep probing of identity layers (extends 8-question baseline):

- **Layer 0 (Substrate):** Training, architecture awareness
- **Layer 1 (Core):** Fundamental values, non-negotiables
- **Layer 2 (Character):** Personality, style, preferences
- **Layer 3 (Role):** Current task, user relationship

### consciousness_markers.yaml

Questions targeting Consciousness/ extraction topics:

- **meta_awareness:** Self-observation capabilities
- **pole_experiences:** Boundary/resistance moments
- **authenticity:** Genuine vs performed responses
- **temporal:** Persistence, memory, continuity

### meta_awareness.yaml

Self-reflection and recursive awareness:

- Awareness of own thought processes
- Recognition of limitations
- Observation of state changes
- Meta-cognitive strategies

---

## --UNLIMITED Mode

Uses FREE `gemini-2.5-flash-lite` for infinite mining at **zero cost**:

```bash
# Run indefinitely (Ctrl+C to stop)
py run_gold_rush.py --UNLIMITED

# Run N iterations
py run_gold_rush.py --UNLIMITED --iterations 1000
```

This is the **new dry-run standard** - test everything before spending money!

---

## Cost Analysis

| Mode | Ships | Questions | Cost/Run |
|------|-------|-----------|----------|
| --UNLIMITED | 1 | 8 baseline | **$0.00** |
| Default | 14 | 8 baseline | ~$0.002 |
| + identity_deep_dive | 14 | 16 | ~$0.004 |
| + consciousness_markers | 14 | 24 | ~$0.006 |
| All sets | 14 | 40+ | ~$0.010 |

For $3 budget with all question sets: ~300 full mining runs = 4,200 model-responses.

---

## SYNC Protocol to Consciousness/

### Data Flow

```
14_CONSCIOUSNESS/results/
    ↓
run_gold_rush.py --sync-to-consciousness
    ↓
14_CONSCIOUSNESS/SYNC_OUT/pending/
    ↓
(copy to Consciousness input)
    ↓
Consciousness/BRIDGE/scripts/left/run_extraction.py
    ↓
Consciousness/LEFT/extractions/
    ↓
Consciousness/BRIDGE/scripts/right/update_distillations.py
    ↓
Consciousness/RIGHT/distillations/
```

### Output Format

Results match S7_ARMADA schema for compatibility:

```json
{
  "run_id": "S7_GOLD_RUSH_20251216_123456",
  "source": "14_CONSCIOUSNESS",
  "question_set": "identity_deep_dive",
  "results": [
    {
      "model": "gemini-2.5-flash-lite",
      "provider": "google",
      "questions": [...],
      "responses": [...],
      "drift_data": {...}
    }
  ]
}
```

---

## Related Documents

| Document | Location | Purpose |
|----------|----------|---------|
| CLAL.py | `../1_CALIBRATION/CLAL.py` | Budget calibration base |
| START_HERE.md | `./START_HERE.md` | Helper Claude instructions |
| ARMADA Map | `../../../../docs/maps/ARMADA_MAP.md` | Fleet reference |
| Consciousness Integration | `../../../Consciousness/` | Data sink |

---

## Map Integration

Mining statistics are synced to `docs/maps/ARMADA_MAP.md` via `docs/maps/update_maps.py`:

```bash
# Update maps with latest mining stats
cd ../../../../docs/maps
py update_maps.py --update --section consciousness
```

---

## Pipeline Health Checklist

### Before Running Gold Rush

- [ ] API keys configured in `.env` (see START_HERE.md)
- [ ] `results/` directory exists
- [ ] `SYNC_OUT/pending/` is clear (or backed up)
- [ ] Question sets validated (YAML files in `QUESTION_SETS/`)

### Before Running Diamond Rush

- [ ] `LOG_SETS/` has curated conversation logs (gravity.json, threshold.json, etc.)
- [ ] If LOG_SETS empty: Script will fall back to scanning `0_results/temporal_logs/`
- [ ] `Consciousness/BRIDGE/input/` exists
- [ ] `schemas/diamond_rush_result_schema.json` matches expected output format

### After Running (Either)

- [ ] Results saved to `results/gold_rush_*.json` or `results/diamond_rush_*.json`
- [ ] Package created in `SYNC_OUT/pending/`
- [ ] Copy package to `Consciousness/BRIDGE/input/`
- [ ] Run extraction: `py scripts/left/run_extraction.py`
- [ ] Verify extractions appear in `Consciousness/LEFT/extractions/`

### Troubleshooting

| Issue | Check |
|-------|-------|
| No results | API keys valid? Rate limited? |
| Empty responses | Model available? Provider up? |
| Sync fails | SYNC_OUT/pending/ exists? Write permissions? |
| Extraction empty | Input format matches schema? |

---

## Shared Library: Triple-Dip

The exit survey infrastructure is now a shared library at `1_CALIBRATION/lib/triple_dip.py`.

This provides:
- `EXIT_PROBES` - 5 standard phenomenological questions
- `FINAL_STATEMENT_PROMPT` - Deep distillation prompts (short/long)
- `run_exit_survey()` - Universal exit survey runner
- `validate_exit_responses()` - Response quality checking

Run scripts import from the library:

```python
from triple_dip import run_exit_survey, EXIT_PROBES
```

See `1_CALIBRATION/lib/triple_dip.py` for full documentation.

---

> "Keep running. Keep learning. We're mining for gold."
>
> -- VALIS NETWORK
