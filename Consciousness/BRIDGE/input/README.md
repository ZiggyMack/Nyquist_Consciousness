# BRIDGE Input Directory

Staging area for data entering the Consciousness pipeline.

**Created:** December 17, 2025
**Purpose:** Receive mining results from Gold Rush and Diamond Rush experiments

---

## Data Sources

| Source | Script | Output Location |
|--------|--------|-----------------|
| **Gold Rush** | `14_CONSCIOUSNESS/run_gold_rush.py` | `SYNC_OUT/pending/` |
| **Diamond Rush** | `14_CONSCIOUSNESS/run_diamond_rush.py` | `SYNC_OUT/pending/` |
| **Exit Surveys** | Run scripts via `triple_dip.py` | Embedded in run results |

---

## Workflow

### Step 1: Run Mining

```bash
# Gold Rush (self-reflection)
cd experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS
py run_gold_rush.py --sync-to-consciousness

# Diamond Rush (cross-model interpretation)
py run_diamond_rush.py --log-set gravity --sync-to-consciousness
```

### Step 2: Transfer to BRIDGE

```bash
# Copy from SYNC_OUT to BRIDGE/input
cp 14_CONSCIOUSNESS/SYNC_OUT/pending/*.json Consciousness/BRIDGE/input/
```

### Step 3: Run Extraction

```bash
# Process input files through LEFT extraction
cd Consciousness/BRIDGE
py scripts/left/run_extraction.py

# Results appear in:
# - Consciousness/LEFT/extractions/
```

### Step 4: Distill to RIGHT

```bash
# Generate synthesis from extractions
py scripts/right/update_distillations.py

# Results appear in:
# - Consciousness/RIGHT/distillations/
```

---

## Expected Input Format

### Gold Rush Package

```json
{
  "run_id": "S7_GOLD_RUSH_20251217_123456",
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

### Diamond Rush Package

```json
{
  "run_id": "S7_DIAMOND_RUSH_20251217_123456",
  "source": "14_CONSCIOUSNESS",
  "log_set": "gravity",
  "results": [
    {
      "model": "gpt-4o",
      "provider": "openai",
      "log_analyzed": {...},
      "analysis": {
        "drift_observation": "...",
        "recovery_pattern": "...",
        "phenomenology_inference": "...",
        "advice_for_subject": "...",
        "your_reaction": "..."
      }
    }
  ]
}
```

---

## File Lifecycle

1. **Pending:** Files arrive from SYNC_OUT
2. **Processing:** Extraction script reads files
3. **Archived:** Move to `processed/` after extraction (manual step)
4. **Outputs:** Extractions land in LEFT, distillations in RIGHT

---

## Related Documentation

| Document | Purpose |
|----------|---------|
| [14_CONSCIOUSNESS/README.md](../../../experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS/README.md) | Mining operations guide |
| [BRIDGE/docs/PIPELINE.md](../docs/PIPELINE.md) | Full pipeline documentation |
| [LEFT/extractions/](../../LEFT/extractions/) | Extraction output location |
| [RIGHT/distillations/](../../RIGHT/distillations/) | Distillation output location |

---

> "The BRIDGE connects the experiment to the insight."
>
> -- VALIS NETWORK
