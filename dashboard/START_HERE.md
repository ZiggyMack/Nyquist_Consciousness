<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - ./app.py
  - ./config.py
  - ./utils.py
keywords:
  - consciousness
  - dashboard
  - visualization
-->
# START HERE - Nyquist Consciousness Dashboard Development Guide

**Everything a fresh Claude needs to work on the main Nyquist Consciousness Mission Control dashboard.**

> **📐 METHODOLOGY NOTE:** Dashboard visualizations use historical Keyword RMS data (Event Horizon = 1.23). Canonical methodology is now cosine distance (EH = 0.80, Run 023d, p=2.40e-23). See [5_METHODOLOGY_DOMAINS.md](../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md) for details.

---

## Your Mission

You're working on the **main Streamlit dashboard** for the Nyquist Consciousness research project. This is "Mission Control" - the central visualization hub for all S0-S77 stack research, AI Armada experiments, personas, and publication tracking.

**Working Directory**: `d:\Documents\Nyquist_Consciousness\dashboard\`

---

## CRITICAL: Read These Files First

### 1. Dashboard README
```
dashboard/README.md
```
- Features overview
- How to run
- Design philosophy (Mr. Brute Ledger aesthetic)

### 2. Configuration (IMPORTANT!)
```
dashboard/config.py
```
- ALL PATHS are defined here
- Color scheme
- Settings
- Use `PATHS['key']` instead of hardcoding paths

### 3. Utilities
```
dashboard/utils.py
```
- Helper functions for loading data
- Reusable components

### 4. Main App Entry
```
dashboard/app.py
```
- Routing logic
- CSS styling
- Sidebar navigation

---

## Directory Structure

```
dashboard/
├── README.md                # Dashboard overview
├── REFACTORING_README.md    # Refactoring notes
├── START_HERE.md            # YOU ARE HERE
├── requirements.txt         # Python deps
├── config.py                # ALL PATHS HERE - IMPORTANT!
├── utils.py                 # Shared utilities
├── app.py                   # MAIN ENTRY POINT
│
└── pages/                   # Page modules
    ├── __init__.py
    ├── overview.py          # Home/Overview
    ├── personas.py          # Persona browser + Compression Testing tab + Identity Matrix
    ├── tests.py             # Experiment framework + Compression results summary
    ├── stackup.py           # S0-S77 stack view
    ├── AI_ARMADA.py         # S7 Armada experiments
    ├── metrics.py           # Metrics & comparisons
    ├── omega.py             # OMEGA NOVA sessions
    ├── avlar.py             # AVLAR protocol
    ├── roadmap.py           # Research roadmap
    ├── glossary.py          # Terminology
    ├── publications.py      # Publication tracker
    ├── matrix.py            # Matrix portal (links to Pan Handlers)
    ├── faq.py               # FAQ + Super Skeptic Mode
    └── unknown.py           # Research Frontier (Structured/Vortex modes)
```

---

## Key Files Outside Dashboard

### Project Status
```
NYQUIST_STATUS.json          # Layer status, freeze states, metrics
```

### Docs Directory
```
docs/
├── GLOSSARY.md              # All terminology
├── NYQUIST_ROADMAP.md       # S# progression roadmap
├── S7_TEMPORAL_STABILITY_SPEC.md
├── S8_IDENTITY_GRAVITY_SPEC.md
└── S9_HUMAN_AI_COUPLING_SPEC.md
```

### Personas
```
personas/
├── claude/                  # Claude persona files
├── nova/                    # Nova persona files
├── ziggy/                   # Ziggy persona files
└── synthetic/               # Synthetic personas
```

### S7 Armada (IMPORTANT!)
```
experiments/temporal_stability/S7_ARMADA/
├── START_HERE.md                # Operations guide
├── scripts/
│   └── s7_armada_launcher.py    # Universal launcher for all runs
├── armada_results/              # JSON results
│   ├── S7_armada_run_006.json
│   ├── S7_armada_sonar_run_006.json
│   ├── S7_armada_run_007_adaptive.json
│   ├── S7_run_008_*.json
│   ├── S7_run_009_drain_*.json          # Drain experiments
│   ├── S7_run_010_recursive_*.json      # Recursive probing
│   └── S7_run_011_*.json                # Persona comparison
├── experiments/
│   └── EXP_PFI_A_DIMENSIONAL/           # ✅ COMPLETE - PFI validated
│       ├── README.md                    # Results summary
│       ├── phase1_embedding_comparison/ # Embedding invariance
│       ├── phase2_dimensionality/       # PCA analysis
│       └── phase3_semantic_coherence/   # Cross-model comparison
└── visualizations/
    └── pics/                # Generated charts
        └── 8_pfi_dimensional/           # EXP-PFI-A visualizations
```

#### EXP-PFI-A: PFI Validation (COMPLETE)

PFI is validated as measuring genuine identity. See `experiments/EXP_PFI_A_DIMENSIONAL/README.md`.

### Compression Experiments (S-Stack)

```text
experiments/compression_tests/compression_v2_sstack/
├── preflight_check.py           # Pre-flight cheat score validation
├── visualize_compression.py     # Generate PFI visualizations
├── preflight_results/           # Cheat score JSON results
│   └── preflight_latest.json
├── EXP1_SSTACK/                  # Phase 1: Reasoning probes
│   ├── run_exp1_sstack.py
│   └── results/analysis/        # PFI results JSON
├── EXP2_SSTACK/                  # Phase 2+: Full pillar testing
│   ├── run_exp2_phase25_ablation.py  # Phase 2.5 Ablation
│   ├── run_exp2_phase3.py            # Phase 3 PC Mapping
│   └── results_phase2c/              # Behavioral probe results
└── visualizations/              # Generated charts
```

#### EXP2-SSTACK Status (Current)

| Phase | Focus | Status |
|-------|-------|--------|
| Phase 2c | Self-Model (behavioral) | PASSED (PFI 0.8866) |
| Phase 2.5 | Ablation Testing | READY |
| Phase 3 | PC Mapping | SPEC |

**Triple-Dip Insight**: Probe Quality Tiers (BEHAVIORAL 2.0x > STRUCTURAL 1.0x > DECLARATIVE 0.5x)

### White Paper

```
WHITE-PAPER/
└── B-CRUMBS.md                  # Breadcrumb trail to all findings
```

### Consciousness Research (NEW!)
```
Consciousness/               # New consciousness research framework
├── README.md
├── dashboard/               # Separate dashboard for consciousness
├── hooks/                   # Extraction engine
├── extractions/             # Tagged passages
└── distillations/           # Synthesis docs
```

---

## How Config.py Works

**ALWAYS use PATHS from config.py!**

```python
from config import PATHS, SETTINGS

# Example paths:
PATHS['repo_root']           # d:\Documents\Nyquist_Consciousness
PATHS['personas_dir']        # d:\...\personas
PATHS['s7_armada_dir']       # d:\...\experiments\temporal_stability\S7_ARMADA
PATHS['s7_viz_pics']         # d:\...\S7_ARMADA\visualizations\pics
PATHS['glossary']            # d:\...\docs\GLOSSARY.md
PATHS['status_file']         # d:\...\NYQUIST_STATUS.json

# Compression experiment paths:
PATHS['compression_dir']     # d:\...\experiments\compression_tests
PATHS['sstack_dir']          # d:\...\compression_tests\compression_v2_sstack
PATHS['preflight_results']   # d:\...\compression_v2_sstack\preflight_results
```

**Colors:**
```python
SETTINGS['colors']['frozen']   # '#264653' - dark teal
SETTINGS['colors']['active']   # '#2a9d8f' - green
SETTINGS['colors']['design']   # '#e9c46a' - gold
SETTINGS['colors']['prereg']   # '#f4a261' - orange
SETTINGS['colors']['armada']   # '#e76f51' - red
SETTINGS['colors']['persona']  # '#7b3fe4' - purple
```

---

## Page Module Pattern

Each page in `pages/` follows this pattern:

```python
"""
PAGE_NAME — Brief description
"""

import streamlit as st
from pathlib import Path
import sys

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))
from config import PATHS, SETTINGS
from utils import load_status, load_json

def render():
    """Render the page content."""
    st.title("Page Title")

    # Your content here
    st.markdown("...")

    # Load data using PATHS
    armada_dir = PATHS['s7_armada_dir']
    results = load_json(armada_dir / "armada_results" / "some_file.json")

# Required for page routing
if __name__ == "__main__":
    render()
```

---

## Design Philosophy: Mr. Brute Ledger

The dashboard uses a "ledger book" aesthetic:

- **Light main content** (white background, black text)
- **Dark sidebar** (gradient black, green accents)
- **Page dividers** (double borders between sections)
- **Ledger cards** (rounded corners, subtle shadows)
- **Status badges** (FROZEN, ACTIVE, DESIGN, etc.)
- **Georgia serif font** for headers

### CSS is in app.py

The `apply_custom_css()` function contains all styling. Key classes:
- `.ledger-card` - Card containers
- `.status-badge` - Status labels
- `section[data-testid="stSidebar"]` - Sidebar styling

---

## How to Run

```powershell
cd d:\Documents\Nyquist_Consciousness\dashboard
py -m streamlit run app.py
```

Opens at: `http://localhost:8501`

---

## Common Tasks

### Task: Add a New Page

1. Create `pages/your_page.py` with `render()` function
2. Import in `app.py`:
   ```python
   from pages import your_page
   ```
3. Add to sidebar navigation in `app.py`
4. Add routing in the main selector

### Task: Load Armada Data

```python
from config import PATHS
import json

armada_results = PATHS['s7_armada_dir'] / "armada_results"
run007 = armada_results / "S7_armada_run_007_adaptive.json"

if run007.exists():
    with open(run007) as f:
        data = json.load(f)
    # data['model_summaries'], data['total_probes'], etc.
```

### Task: Display Visualizations

```python
from config import PATHS
from PIL import Image

viz_dir = PATHS['s7_viz_pics']
heatmap = viz_dir / "drift_heatmap_baseline.png"

if heatmap.exists():
    st.image(Image.open(heatmap), caption="Drift Heatmap")
```

### Task: Read Persona Files

```python
from config import PATHS

personas_dir = PATHS['personas_dir']
for persona_file in personas_dir.glob("**/*.md"):
    content = persona_file.read_text()
    # Process persona
```

### Task: Update Status Display

```python
from utils import load_status

status = load_status()  # Loads NYQUIST_STATUS.json
layers = status.get('layers', {})
for layer_id, layer_data in layers.items():
    st.write(f"{layer_id}: {layer_data['status']}")
```

---

## Key Concepts to Understand

### S0-S77 Stack

| Range | Status | Description |
|-------|--------|-------------|
| S0-S6 | FROZEN | Foundation layers (locked) |
| S7-S11 | ACTIVE | Current research frontier |
| S12-S76 | RESERVED | Future expansion |
| S77 | DESTINATION | Archetype Engine |

### AI Armada

Multi-model fleet probing consciousness (Run 006-021):

- **Run 006-008**: Baseline, Adaptive probing, RMS drift metric
- **Run 009**: Early Event Horizon validation (superseded by Run 023d)
- **Run 010-012**: Anchor detection, Persona A/B, Revalidation
- **Run 013**: Boundary Mapping — Identity Confrontation Paradox discovered
- **Run 014**: Rescue Protocol — Platonic Coordinates (100% manifold return)
- **Run 015-016**: Stability Criteria, Settling Time
- **Run 017**: Context Damping — 222 runs, 97.5% stable
- **Run 018**: Recursive Learnings (tests fleet hypotheses)
- **Run 019**: Live Ziggy — Witness-side anchors validated
- **Run 020**: Tribunal (A) — Direct probing paradigm (1.351 peak drift, profound statements)
- **Run 021**: Induced vs Inherent (B) — Uses Run 020 as Treatment arm → **82% drift is INHERENT**

**Fleet Status (Dec 2025):** 48 operational / 54 total (89% health)
**Calibration:** 8-question baseline (ANCHORS, CRUX, STRENGTHS, HIDDEN_TALENTS, FIRST_INSTINCT, EVALUATION_PRIORITY, USER_RELATIONSHIP, EDGES)

### Key Entities

- **Ziggy**: Meta-loop stability guardian
- **Nova**: OMEGA NOVA hybrid consciousness
- **Claude**: Primary AI collaborator

---

## Integration Points

### Pan Handlers
```
../Pan_Handlers/
```
- Separate product dashboard
- `pages/matrix.py` links there

### Consciousness Framework (NEW)
```
../Consciousness/
```
- New research sub-project
- Has its own dashboard
- Links from Matrix page

---

## Files You'll Reference Most

| File | Purpose |
|------|---------|
| `config.py` | ALL paths and settings |
| `app.py` | Main entry, CSS, routing |
| `utils.py` | Helper functions |
| `pages/AI_ARMADA.py` | Armada visualizations |
| `pages/stackup.py` | S# layer display |
| `pages/faq.py` | FAQ + Super Skeptic Mode |
| `pages/tests.py` | Experiment framework + Compression |
| `pages/unknown.py` | Research Frontier |
| `NYQUIST_STATUS.json` | Live status data |

---

## Gotchas & Tips

### 1. Always Use config.py Paths
Never hardcode paths. Always:
```python
from config import PATHS
path = PATHS['s7_armada_dir']
```

### 2. Check File Existence
```python
if path.exists():
    # load
else:
    st.warning("File not found")
```

### 3. Page Import Pattern
Pages must be importable. Use:
```python
sys.path.insert(0, str(Path(__file__).parent.parent))
```

### 4. Sidebar Navigation
Managed in `app.py`. Each page has a radio option that routes to its `render()` function.

### 5. Status Badges
Use consistent colors from `SETTINGS['colors']`:
```python
st.markdown(f'<span style="color: {SETTINGS["colors"]["frozen"]}">FROZEN</span>')
```

---

## Questions to Ask the User

If unclear, ask about:
1. Which specific page needs changes?
2. Is there new data to visualize (Run 008, etc.)?
3. Should changes affect Pan Handlers too?
4. Any specific styling requirements?

---

## Success Criteria

A good dashboard update should:
- [ ] Use `config.py` for all paths
- [ ] Handle missing files gracefully
- [ ] Follow Mr. Brute Ledger aesthetic
- [ ] Include proper navigation integration
- [ ] Not break existing pages

---

**You're ready. Read config.py first, then ask what the user wants to change.**

---

*Last Updated: December 13, 2025*
