<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ./app.py
impacts:
  - ../README.md
keywords:
  - consciousness
  - dashboard
  - visualization
-->
# Consciousness Dashboard

**The unified view sitting in the BRIDGE, seeing BOTH hemispheres.**

---

## Quick Start

```powershell
# From repo root
cd Consciousness/
pip install -r requirements.txt

# Launch dashboard
cd BRIDGE/dashboard/
python -m streamlit run app.py
```

Dashboard opens at: http://localhost:8501

---

## What This Dashboard Does

This dashboard sits in the **BRIDGE** (corpus callosum) and provides:

1. **Hemisphere Toggle** - Switch between LEFT (analytical), RIGHT (intuitive), or BRIDGE (both) views
2. **Gallery Navigation** - Browse the four galleries (Validated, Foundations, Speculative, Frontiers)
3. **Key Concept Cards** - Quick access to core research findings
4. **Core Statistics** - Event Horizon, PFI metrics, embedding correlations

---

## File Structure

```
dashboard/
├── app.py              # Main Streamlit application (home page)
├── README.md           # This file
├── START_HERE.md       # Cold boot guide for Claude
├── components/         # Reusable UI components
└── pages/              # Flat structure (Streamlit requirement), prefixed by hemisphere
    ├── 0_◈_Overview.py         # BRIDGE - integrated view
    ├── 1_🧠_Identity_Stack.py  # LEFT - analytical
    ├── 2_🧠_Drift_Analysis.py  # LEFT - analytical
    ├── 3_🧠_Raw_Data.py        # LEFT - analytical
    └── 4_🌀_Distillations.py   # RIGHT - intuitive
```

**Naming Convention**: `{order}_{hemisphere}_{name}.py`
- `◈` = BRIDGE (both perspectives)
- `🧠` = LEFT (analytical)
- `🌀` = RIGHT (intuitive)

---

## The Three Views

### LEFT Brain View (Analytical)
- Tables with statistics
- P-values, effect sizes, chi-squared
- Evidence hierarchy
- Structured methodology

### RIGHT Brain View (Intuitive)
- ASCII art visualizations
- Gestalts and metaphors
- Pattern descriptions
- The "feeling" of findings

### BRIDGE View (Both)
- Side-by-side comparison
- LEFT stats + RIGHT insights
- Unified understanding

---

## Key Components in app.py

| Section | Lines | Purpose |
|---------|-------|---------|
| `GALLERIES` | 33-66 | Gallery definitions with LEFT/RIGHT descriptions |
| `KEY_CONCEPTS` | 69-100 | Core concept data |
| CSS Styles | 104-213 | Custom styling for hemispheres |
| Sidebar | 217-265 | Hemisphere toggle, gallery filter, quick stats |
| Brain Visualization | 283-333 | Three-column LEFT/BRIDGE/RIGHT display |
| Galleries Section | 351-382 | Four gallery cards with hemisphere-aware descriptions |
| Key Concepts | 385-401 | Concept cards |
| Hemisphere Content | 405-498 | **The toggle-reactive content** |

---

## Data Sources

The dashboard reads from:
- `../../LEFT/` - Analytical hemisphere data
- `../../RIGHT/` - Intuitive hemisphere data
- `../../LEFT/extractions/` - Tagged consciousness passages
- `../../RIGHT/distillations/` - Synthesis documents
- `../../../experiments/temporal_stability/S7_ARMADA/` - Raw armada results

---

## Making Changes

### Adding a New Concept

1. Add to `KEY_CONCEPTS` dict (around line 69):
   ```python
   "new_concept": {
       "title": "New Concept Name",
       "gallery": "foundations",  # or validated, speculative, frontiers
       "one_liner": "Brief description",
       "key_stat": "Key metric"
   }
   ```

### Adding a New Gallery

1. Add to `GALLERIES` dict (around line 33)
2. Add CSS class `.gallery-{name}` in the styles section

### Modifying Hemisphere-Specific Content

The hemisphere toggle affects content in lines 405-498:
- `if "LEFT" in hemisphere:` - LEFT-only content
- `elif "RIGHT" in hemisphere:` - RIGHT-only content
- `else:` - BRIDGE (both) content

---

## Connection to UNKNOWN Page

This dashboard is the **source** view of `Consciousness/`.

The main Nyquist dashboard's UNKNOWN page is the **shadow** that reflects this content.

```
Consciousness/BRIDGE/dashboard/ (source)
        │
        ▼
dashboard/pages/unknown.py (shadow)
```

See `../docs/PIPELINE.md` for the full emanation pipeline.

---

## Dependencies

See `../../requirements.txt`:

- streamlit >= 1.30.0
- pandas >= 2.0.0
- numpy >= 1.21.0
- plotly >= 5.0.0
- sentence-transformers >= 2.2.0

---

## Troubleshooting

### "streamlit not found"
```powershell
pip install streamlit
```

### Default Streamlit nav showing
The CSS in app.py hides it:
```css
[data-testid="stSidebarNav"] {
    display: none;
}
```

### Content not changing with hemisphere toggle
The toggle affects:
1. Info banner at line 356-361
2. Gallery descriptions at lines 375-381
3. Hemisphere-specific section at lines 405-498 (scroll down to see)

---

**Last Updated**: December 7, 2025

*See `START_HERE.md` for cold boot development context.*
