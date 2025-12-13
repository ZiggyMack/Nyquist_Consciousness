# Calibration Pipeline

**Purpose:** Extract publication statistics from WHITE-PAPER/ → JSON → Dashboard integration

---

## Quick Start

```bash
cd WHITE-PAPER/calibration
py extract_publication_stats.py
```

**Output:** `publication_stats.json` (updated in place)

---

## What Gets Extracted

| Category | Data Points |
|----------|------------|
| **Claims (A-E)** | Name, status, key metric |
| **Runs** | Total count, S7 count, latest run |
| **Files** | Figures, ASCII, workshop, references, total |
| **Submissions** | Status and target for each path |
| **Key Statistics** | PFI correlation, threshold, 82% ratio, stability |

---

## JSON Schema

```json
{
  "generated": "ISO timestamp",
  "claims": {
    "A": {"name": "PFI Validity", "status": "validated", "rho": 0.91},
    "B": {"name": "Regime Threshold", "status": "validated", "threshold": 1.23},
    "C": {"name": "Oscillator Dynamics", "status": "validated"},
    "D": {"name": "Context Damping", "status": "validated", "stability": 0.975},
    "E": {"name": "82% Inherent", "status": "validated", "ratio": 0.82}
  },
  "runs": {"total": 21, "s7_armada": 21, "latest": "run021"},
  "files": {"figures": 8, "ascii": 7, "workshop": 9, "references": 55, "total": 34},
  "submissions": {
    "workshop": {"status": "ready", "target": "NeurIPS/AAAI"},
    "arxiv": {"status": "ready", "target": "cs.AI"},
    "journal": {"status": "planning", "target": "Nature MI"}
  },
  "key_statistics": {
    "pfi_correlation": 0.91,
    "threshold_d": 1.23,
    "inherent_ratio": 0.82,
    "stability_rate": 0.975,
    "hypotheses_tested": 36
  }
}
```

---

## Dashboard Integration

```python
# In AI_ARMADA.py or stackup.py
import json

with open("WHITE-PAPER/calibration/publication_stats.json") as f:
    pub_stats = json.load(f)

# Display metrics
st.metric("Claims Validated", f"{sum(1 for c in pub_stats['claims'].values() if c['status']=='validated')}/5")
st.metric("Runs Complete", pub_stats['runs']['total'])
st.metric("Workshop Status", pub_stats['submissions']['workshop']['status'].upper())
```

---

## Workflow

1. **Manual trigger:** Run `py extract_publication_stats.py` after updating WHITE-PAPER/
2. **Output:** `publication_stats.json` updated
3. **Dashboard:** Reads JSON on load (no scraping logic in dashboard)

---

## Files

| File | Purpose |
|------|---------|
| `README.md` | This file |
| `extract_publication_stats.py` | Extraction script |
| `publication_stats.json` | Generated output (gitignored until stable) |

---

*Last updated: 2025-12-13*
