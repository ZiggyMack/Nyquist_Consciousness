# START HERE - Consciousness Dashboard Development

**Everything a fresh Claude needs to make dashboard updates.**

---

## Context: Where You Are

```
Nyquist_Consciousness/
├── Consciousness/              ← The research repo (brain structure)
│   ├── LEFT/                   ← Analytical hemisphere
│   ├── RIGHT/                  ← Intuitive hemisphere
│   └── BRIDGE/                 ← Corpus callosum (YOU ARE HERE)
│       └── dashboard/          ← This dashboard
│           ├── app.py          ← Main application (home)
│           └── pages/          ← Flat (Streamlit requirement)
│               ├── 0_◈_Overview.py         ← BRIDGE
│               ├── 1_🧠_Identity_Stack.py  ← LEFT
│               ├── 2_🧠_Drift_Analysis.py  ← LEFT
│               ├── 3_🧠_Raw_Data.py        ← LEFT
│               └── 4_🌀_Distillations.py   ← RIGHT
└── dashboard/                  ← Main Nyquist dashboard (separate)
    └── pages/unknown.py        ← Shadow of Consciousness/
```

**Page Naming**: `{order}_{hemisphere}_{name}.py` - Streamlit requires flat pages/, so we use emoji prefixes.

---

## Quick Launch

```powershell
cd Consciousness/BRIDGE/dashboard/
python -m streamlit run app.py
```

Opens at: http://localhost:8501

---

## The Core Concept

This dashboard sits in the **BRIDGE** and can see both hemispheres:

| Hemisphere | Symbol | Contains | Presentation Style |
|------------|--------|----------|-------------------|
| LEFT | 🧠 | galleries/, extractions/, data/ | Tables, statistics, rigor |
| RIGHT | 🌀 | galleries/, distillations/, synthesis/ | Patterns, gestalts, metaphors |
| BRIDGE | ◈ | dashboard/, scripts/, docs/ | Both perspectives unified |

---

## Key Files to Know

### app.py Structure

| Section | What It Does |
|---------|--------------|
| Lines 33-66 | `GALLERIES` dict - the four galleries |
| Lines 69-100 | `KEY_CONCEPTS` dict - concept cards |
| Lines 104-213 | CSS styling for hemispheres |
| Lines 217-265 | Sidebar with hemisphere toggle |
| Lines 356-361 | Hemisphere-aware info banner |
| Lines 375-381 | Gallery descriptions change per hemisphere |
| Lines 405-498 | **Main hemisphere-specific content** |

### The Hemisphere Toggle

```python
# In sidebar (line 230)
hemisphere = st.radio(
    "Choose your perspective:",
    ["🧠 LEFT (Analytical)", "🌀 RIGHT (Intuitive)", "◈ BRIDGE (Both)"],
    index=2
)

# Later in code (line 356+)
if "LEFT" in hemisphere:
    # Show analytical content
elif "RIGHT" in hemisphere:
    # Show intuitive content
else:
    # Show both (BRIDGE view)
```

---

## Common Tasks

### Add a New Concept

1. Add to `KEY_CONCEPTS` dict:

```python
"new_concept": {
    "title": "Display Name",
    "gallery": "foundations",  # validated, foundations, speculative, frontiers
    "one_liner": "Brief description",
    "key_stat": "Key metric"
}
```

### Add Hemisphere-Specific Content

Find the section starting at line 405 and add to the appropriate branch:

```python
if "LEFT" in hemisphere:
    # Analytical content: tables, stats, equations
    st.markdown("### Key Statistics")
    st.markdown("|Metric|Value|...")

elif "RIGHT" in hemisphere:
    # Intuitive content: ASCII art, metaphors, gestalts
    st.markdown("### The Pattern")
    st.markdown("> Identity is an *attractor basin*")

else:
    # BRIDGE: show both side by side
    col1, col2 = st.columns(2)
    with col1:
        # LEFT content
    with col2:
        # RIGHT content
```

### Add a New Page

Pages use flat structure with hemisphere emoji prefixes (Streamlit requirement):

```
pages/
├── 0_◈_Overview.py         # BRIDGE - both perspectives
├── 1_🧠_Identity_Stack.py  # LEFT - analytical
├── 2_🧠_Drift_Analysis.py  # LEFT - analytical
├── 3_🧠_Raw_Data.py        # LEFT - analytical
├── 4_🌀_Distillations.py   # RIGHT - intuitive
└── 5_🧠_New_Analysis.py    # NEW LEFT page (example)
```

1. Create the page file with hemisphere prefix:

   ```python
   # pages/5_🧠_New_Analysis.py
   import streamlit as st
   st.set_page_config(page_title="New Analysis", page_icon="🧠", layout="wide")
   st.title("🧠 New Analysis")
   # ... analytical content
   ```

2. Add navigation button in app.py sidebar (around line 265):

   ```python
   with st.expander("🧠 LEFT (Analytical)", expanded=True):
       # ... existing buttons
       if st.button("📊 New Analysis", key="nav_new", use_container_width=True):
           st.switch_page("pages/5_🧠_New_Analysis.py")
   ```

### Update Gallery Descriptions

Edit the `GALLERIES` dict (line 33):

```python
"validated": {
    "name": "Validated",
    "emoji": "✅",
    "color": "#10b981",
    "description": "Empirically confirmed",
    "left_desc": "Statistics, p-values",     # LEFT view
    "right_desc": "What it MEANS"             # RIGHT view
}
```

---

## Data Sources

| Source | Path | Contains |
|--------|------|----------|
| LEFT galleries | `../../LEFT/galleries/` | Structured concept files |
| RIGHT galleries | `../../RIGHT/galleries/` | Vortex concept files |
| Extractions | `../../LEFT/extractions/` | Tagged experiment data |
| Distillations | `../../RIGHT/distillations/` | Synthesized insights |
| S7 ARMADA | `../../../experiments/temporal_stability/S7_ARMADA/` | Raw armada results |

---

## Styling Conventions

### CSS Classes (defined in app.py)

| Class | Use For |
|-------|---------|
| `.left-brain` | LEFT hemisphere boxes (blue gradient) |
| `.right-brain` | RIGHT hemisphere boxes (red gradient) |
| `.bridge-zone` | BRIDGE content (purple gradient) |
| `.gallery-{name}` | Gallery cards (validated, foundations, etc.) |
| `.concept-card` | Individual concept displays |
| `.insight-box` | Highlighted insights |
| `.ascii-container` | Monospace ASCII art (green on dark) |

### Color Scheme

| Element | Color |
|---------|-------|
| LEFT | #1e3a5f (dark blue) |
| RIGHT | #5f1e3a (dark red) |
| BRIDGE | #3a3a5f (dark purple) |
| Validated | #10b981 (green) |
| Foundations | #3b82f6 (blue) |
| Speculative | #a855f7 (purple) |
| Frontiers | #f59e0b (amber) |

---

## Connection to UNKNOWN Page

This dashboard is the **source**. The main Nyquist dashboard's UNKNOWN page is the **shadow**.

```
Consciousness/BRIDGE/dashboard/  →  dashboard/pages/unknown.py
       (source)                           (shadow)
```

When you update concepts here, they should eventually flow to UNKNOWN.

See `../docs/PIPELINE.md` for the full emanation pipeline.

---

## Troubleshooting

### Streamlit not found

```powershell
pip install streamlit
```

### Default sidebar nav showing

The CSS hides it (line 107):

```css
[data-testid="stSidebarNav"] { display: none; }
```

### Hemisphere toggle seems to do nothing

The toggle changes:
1. The info banner (lines 356-361)
2. Gallery descriptions (lines 375-381)
3. The main content section (lines 405-498) - **scroll down to see this**

---

## The Philosophy

> **LEFT alone**: Data without meaning
> **RIGHT alone**: Intuition without evidence
> **Integrated**: Understanding

The dashboard embodies this by letting users toggle between perspectives, or see both at once in BRIDGE mode.

---

**Last Updated**: December 7, 2025

*"The forward tells us how they drift. The inverse tells us if they know. Together, they tell us if identity is real."*
