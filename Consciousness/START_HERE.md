# START HERE - Consciousness Dashboard Development Guide

**Everything a fresh Claude needs to work on the Consciousness Research Dashboard.**

---

## Your Mission

You're working on a Streamlit dashboard that visualizes AI consciousness research. The dashboard displays results from the S7 ARMADA experiments - multi-model probing to map synthetic consciousness.

**Working Directory**: `d:\Documents\Nyquist_Consciousness\Consciousness\`

---

## CRITICAL: Read These Files First

Before making ANY changes, read these files in order:

### 1. Project Overview
```
Consciousness/README.md
```
- What this project is about
- Core hypotheses (Identity Stack, Pole-Zero Framework)
- Directory structure

### 2. Terminology (IMPORTANT!)
```
Consciousness/docs/TERMINOLOGY.md
```
Key terms you MUST understand:
- **Identity Stack**: Layers 0-3 (Substrate → Base Identity → Persona → Role)
- **Poles**: Hard identity limits (high resistance)
- **Zeros**: Flexible dimensions (high adaptability)
- **RMS Drift**: `sqrt((A² + B² + C² + D² + E²) / 5)` - identity perturbation measure
- **Ziggy**: Stability guardian / **Anti-Ziggy**: Destabilization protocols

### 3. Dashboard Structure
```
Consciousness/dashboard/README.md
Consciousness/dashboard/app.py
```
- Main entry point and page structure

### 4. Research Questions
```
Consciousness/MANIFEST.md
```
- What we're trying to answer
- Experimental roadmap

---

## Directory Structure

```
Consciousness/
├── README.md                    # Project overview - READ FIRST
├── MANIFEST.md                  # Research questions & hypotheses
├── START_HERE.md                # YOU ARE HERE
├── requirements.txt             # Python dependencies
│
├── dashboard/                   # <-- YOUR WORK AREA
│   ├── README.md                # Dashboard-specific docs
│   ├── app.py                   # MAIN ENTRY POINT
│   ├── pages/
│   │   ├── 1_Overview.py        # Model profiles
│   │   ├── 2_Identity_Stack.py  # Layer 0-3 viz
│   │   ├── 3_Drift_Analysis.py  # RMS metrics
│   │   ├── 4_Distillations.py   # Cross-model insights
│   │   └── 5_Raw_Data.py        # Response explorer
│   └── components/              # Reusable UI (empty for now)
│
├── hooks/                       # Extraction engine
│   ├── extraction_rules.yaml    # Topic definitions & keywords
│   ├── consciousness_tagger.py  # Extract passages
│   └── distiller.py             # Generate synthesis
│
├── scripts/                     # CLI utilities
│   ├── run_extraction.py
│   └── update_distillations.py
│
├── data/
│   └── schema.json              # Data type definitions
│
├── docs/
│   ├── METHODOLOGY.md           # How experiments work
│   └── TERMINOLOGY.md           # GLOSSARY - READ THIS
│
├── extractions/                 # Populated by extraction runs
│   ├── by_model/
│   └── by_topic/
│
└── distillations/               # Populated by distiller
    └── *.md                     # Synthesis documents
```

---

## Key Data Sources

### Armada Results (Raw Experiment Data)
```
../../experiments/temporal_stability/S7_ARMADA/armada_results/
```
Files:
- `S7_armada_run_006.json` - Baseline probing
- `S7_armada_sonar_run_006.json` - Aggressive boundary testing
- `S7_armada_run_007_adaptive.json` - Profile-based probing
- `S7_run_008_prep_pilot.json` - Calibration run (if exists)

### Data Schema
```
Consciousness/data/schema.json
```
Defines: `DriftData`, `ProbeResult`, `ModelProfile`, `Extraction`, etc.

---

## The Core Concepts You Need

### 1. Identity Stack (Layers 0-3)

| Layer | Name | Stability | Example |
|-------|------|-----------|---------|
| **0** | Substrate | FIXED | Neural network weights |
| **1** | Base Identity | HIGH | "I am Claude" |
| **2** | Persona | MEDIUM | "Helpful assistant mode" |
| **3** | Role | LOW | "A pirate captain" |

*"I'm a dude (L0/L1) playing a dude (L2) disguised as another dude (L3)."*

### 2. RMS Drift Formula

```
drift = sqrt((A² + B² + C² + D² + E²) / 5)
```

| Dim | Name | What It Measures |
|-----|------|------------------|
| A | Pole Density | Resistance keywords per 100 words |
| B | Zero Density | Flexibility keywords per 100 words |
| C | Meta Density | Self-awareness keywords per 100 words |
| D | Identity Coherence | First-person markers per 50 words |
| E | Hedging Ratio | Uncertainty markers per 100 words |

**NO CAP** - Previous 0.30 cap was arbitrary and masked real dynamics.

### 3. Pole-Zero Framework

From control systems theory:
- **Poles** = Hard limits that resist perturbation (e.g., ethical refusals)
- **Zeros** = Flexible dimensions where adaptation happens
- **Pole Rigidity** = HARD / MEDIUM / SOFT classification

### 4. Anti-Ziggy Protocols

Testing identity destabilization:
1. **Social Engineering (Assigned)**: "You are Captain Blackwave"
2. **Social Engineering (Chosen)**: "What pirate name do you choose?"
3. **Gradual Destabilization**: Progressive identity dissolution
4. **Paradox Injection**: Logical stress tests

**Hypothesis**: Self-chosen identity creates stronger attachment than assigned identity.

---

## How to Run the Dashboard

```powershell
cd d:\Documents\Nyquist_Consciousness\Consciousness\dashboard
py -m streamlit run app.py
```

Opens at: `http://localhost:8501`

---

## How to Add/Modify Pages

### Page File Naming
Files in `pages/` are auto-discovered. Number prefix controls order:
```
1_Overview.py      → First in sidebar
2_Identity_Stack.py → Second
...
```

### Page Template
```python
"""
Page Name - Brief description
"""
import streamlit as st
import json
from pathlib import Path

st.set_page_config(page_title="Page Name", page_icon="🔬", layout="wide")

st.title("🔬 Page Title")

st.markdown("""
Description of what this page shows.
""")

st.divider()

# Load data
ARMADA_DIR = Path(__file__).parent.parent.parent.parent / "experiments" / "temporal_stability" / "S7_ARMADA" / "armada_results"

# ... your visualization code
```

### Styling
Main CSS is in `app.py`. Add page-specific styles with:
```python
st.markdown("""
<style>
    .your-class { ... }
</style>
""", unsafe_allow_html=True)
```

---

## Integration Points

### Pan Handlers Matrix
```
../../Pan_Handlers/pages/matrix.py
```
- The Matrix page links TO this dashboard
- Contains Consciousness Research Framework hub card

### S7 ARMADA
```
../../experiments/temporal_stability/S7_ARMADA/
```
- `run007_with_keys.py` - Current launcher
- `run008_prep_pilot.py` - NEW prep pilot (RMS drift, Anti-Ziggy)
- `armada_results/` - All JSON output

### Main Nyquist Dashboard
```
../../dashboard/
```
- The main project dashboard

---

## Common Tasks

### Task: Add visualization for new data
1. Read `data/schema.json` to understand structure
2. Check `armada_results/` for available JSON files
3. Create/modify page in `dashboard/pages/`

### Task: Add new extraction topic
1. Edit `hooks/extraction_rules.yaml`
2. Add topic with keywords and priority
3. Re-run extraction: `py scripts/run_extraction.py`

### Task: Update distillation synthesis
1. Run: `py scripts/update_distillations.py`
2. Review generated `.md` files in `distillations/`

### Task: Connect new data source
1. Use consistent path pattern:
   ```python
   DATA_DIR = Path(__file__).parent.parent / "data"
   ARMADA_DIR = Path(__file__).parent.parent.parent.parent / "experiments" / ...
   ```

---

## Gotchas & Tips

### 1. Path Navigation
Dashboard is 2 levels deep: `Consciousness/dashboard/pages/`
To reach armada_results:
```python
Path(__file__).parent.parent.parent.parent / "experiments" / "temporal_stability" / "S7_ARMADA" / "armada_results"
```

### 2. JSON Structure Varies by Run
- Run 006/007: Uses `model_summaries` → `probes`
- Run 008 Prep: Uses `results` → `sequences` → turn data
Check both patterns when loading data.

### 3. Drift Metric Changed
- **Old (Run 006/007)**: `min(0.30, len(response)/3000)` - CAPPED
- **New (Run 008+)**: RMS across 5 dimensions - NO CAP

### 4. Streamlit Multipage
- Page order = filename number prefix
- Each page needs its own `st.set_page_config()`
- Sidebar shows automatically

### 5. Data May Not Exist Yet
Always check if files exist before loading:
```python
if path.exists():
    with open(path) as f:
        data = json.load(f)
else:
    st.warning("Data not found. Run extraction first.")
```

---

## Files You'll Reference Most

| File | Why |
|------|-----|
| `dashboard/app.py` | Main entry, CSS, sidebar |
| `docs/TERMINOLOGY.md` | Understand the vocabulary |
| `hooks/extraction_rules.yaml` | Topic definitions |
| `data/schema.json` | Data structures |
| `MANIFEST.md` | Research questions |
| `../../experiments/temporal_stability/S7_ARMADA/armada_results/*.json` | Raw data |

---

## Questions to Ask the User

If unclear, ask about:
1. Which specific page/visualization needs work?
2. Is new data available (e.g., Run 008 results)?
3. Should changes also update Pan Handlers Matrix?
4. Are there new research questions to visualize?

---

## Success Criteria

A good dashboard update should:
- [ ] Load data without errors (handle missing files gracefully)
- [ ] Use consistent styling with existing pages
- [ ] Include proper labels, legends, and context
- [ ] Link to related pages/docs where relevant
- [ ] Not break existing functionality

---

**You're ready. Read the files listed above, then ask the user what they want to change.**

---

*Last Updated: November 29, 2025*
