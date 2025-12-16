# Calibration Pipeline

**Purpose:** Extract publication statistics, create review packages, and generate PDFs from WHITE-PAPER/
**Last Updated:** 2025-12-16

---

## Scripts

### 1. generate_pdfs.py (NEW)

Generate publication-ready PDFs for all 8 paths:

```bash
cd WHITE-PAPER/calibration
py generate_pdfs.py
```

**Output:** `WHITE-PAPER/reviewers/packages/pdf/`

Generated PDFs:

| PDF | Size | Target |
|-----|------|--------|
| Nyquist_Workshop_Paper.pdf | ~150 KB | NeurIPS/AAAI |
| Nyquist_arXiv_Paper.pdf | ~300 KB | cs.AI |
| Nyquist_Journal_Paper.pdf | ~200 KB | Nature MI |
| Nyquist_Popular_Science.pdf | ~100 KB | Atlantic/Wired |
| Nyquist_Education_Quiz.pdf | ~150 KB | OER/Coursera |
| Nyquist_Policy_Briefing.pdf | ~100 KB | Think tanks |
| Nyquist_Funding_Proposal.pdf | ~150 KB | NSF/DARPA |
| Nyquist_Media_Press.pdf | ~80 KB | Press/TED |

### 2. extract_publication_stats.py

Extract statistics for dashboard integration:

```bash
cd WHITE-PAPER/calibration
py extract_publication_stats.py
```

**Output:** `publication_stats.json`

### 3. extract_review_package.py

Extract path-specific review packages for AI reviewers:

```bash
# Show available paths and estimated sizes
py extract_review_package.py --status

# Extract single path
py extract_review_package.py workshop

# Extract multiple paths
py extract_review_package.py workshop arxiv

# Extract ALL paths
py extract_review_package.py --all

# Include figures (increases size)
py extract_review_package.py arxiv --include-figures

# Preview without extracting
py extract_review_package.py workshop --dry-run

# Custom output location
py extract_review_package.py workshop --output ./FOR_OPUS
```

**Output:** `WHITE-PAPER/reviewers/packages/{path}/`

**Available Paths:** workshop, arxiv, journal, popular_science, education, policy, funding, media

**Expected Sizes (text-only):**

| Path | Size | Files |
|------|------|-------|
| workshop | ~90 KB | ~13 |
| arxiv | ~360 KB | ~17 |
| journal | ~530 KB | ~29 |
| popular_science | ~30 KB | ~4 |
| education | ~40 KB | ~4 |
| policy | ~30 KB | ~3 |
| funding | ~70 KB | ~6 |
| media | ~35 KB | ~5 |

---

## What Gets Extracted (extract_publication_stats.py)

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
| `generate_pdfs.py` | PDF generation for all 8 paths |
| `extract_publication_stats.py` | Statistics extraction script |
| `extract_review_package.py` | Review package extraction script |
| `publication_stats.json` | Generated statistics output |

---

*Last updated: 2025-12-16*
