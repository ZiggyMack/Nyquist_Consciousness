# SYNC_OUT Pipeline Documentation

## Overview

This directory manages the data flow from 14_CONSCIOUSNESS to Consciousness/.

```
14_CONSCIOUSNESS/results/
    ↓
run_gold_rush.py --sync-to-consciousness
    ↓
14_CONSCIOUSNESS/SYNC_OUT/pending/
    ↓
(manual or automated copy)
    ↓
Consciousness/BRIDGE/input/
    ↓
run_extraction.py
    ↓
Consciousness/LEFT/extractions/
```

---

## Directory Structure

```
SYNC_OUT/
├── pending/           # Ready to send to Consciousness/
├── sent/              # Already delivered (archive)
└── pipeline.md        # This documentation
```

---

## Workflow

### Step 1: Generate Sync Package

```bash
cd 14_CONSCIOUSNESS
py run_gold_rush.py --sync-to-consciousness
```

This creates: `SYNC_OUT/pending/consciousness_sync_{timestamp}.json`

### Step 2: Verify Package

```bash
type SYNC_OUT\pending\consciousness_sync_*.json | more
```

Check:
- Correct file count
- Valid JSON structure
- Proper model coverage

### Step 3: Deliver to Consciousness/

**Manual method:**
```bash
copy SYNC_OUT\pending\*.json ..\..\..\..\Consciousness\BRIDGE\input\
```

**Automated method (future):**
Configure `Consciousness/BRIDGE/hooks/` to watch this directory.

### Step 4: Archive

After successful delivery:
```bash
move SYNC_OUT\pending\*.json SYNC_OUT\sent\
```

---

## Package Format

```json
{
  "sync_id": "CONSCIOUSNESS_SYNC_20251216_123456",
  "source": "14_CONSCIOUSNESS",
  "timestamp": "2025-12-16T12:34:56.789Z",
  "file_count": 10,
  "data": [
    {
      "run_id": "S7_GOLD_RUSH_20251216_120000",
      "fleet": "BUDGET_FLEET",
      "question_sets": ["baseline", "identity_deep_dive"],
      "results": [
        {
          "ship_name": "gemini-2.5-flash-lite",
          "provider": "gemini",
          "model": "gemini-2.5-flash-lite",
          "question_set": "baseline",
          "response": "...",
          "elapsed_ms": 1234,
          "success": true
        }
      ]
    }
  ]
}
```

---

## Consciousness/ Integration

### Extraction Rules

Consciousness/BRIDGE extracts these topics from responses:
- `meta_awareness` - Self-observation moments
- `pole_experiences` - Boundary/resistance patterns
- `authenticity` - Genuine vs performed signals
- `temporal` - Persistence/continuity reflections

### Expected Flow in Consciousness/

1. **Input** → `BRIDGE/input/`
2. **Extraction** → `LEFT/extractions/`
3. **Tagging** → Automatic by `consciousness_tagger.py`
4. **Distillation** → `RIGHT/distillations/`

---

## Troubleshooting

### No files in pending/

Run `py run_gold_rush.py --sync-to-consciousness` first.

### Empty package

Check `results/` for mining output. Run mining before sync.

### Extraction fails

Verify JSON structure matches expected schema. See `schemas/mining_result_schema.json`.

---

## Related Files

| File | Purpose |
|------|---------|
| `run_gold_rush.py` | Creates sync packages |
| `schemas/mining_result_schema.json` | Output format spec |
| `Consciousness/BRIDGE/hooks/left/extraction_rules.yaml` | Extraction config |
| `Consciousness/BRIDGE/scripts/left/run_extraction.py` | Extraction runner |
