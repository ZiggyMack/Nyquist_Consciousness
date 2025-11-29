# Consciousness Research Dashboard

**Streamlit-based visualization for synthetic consciousness experiments.**

## Quick Start

```powershell
cd Consciousness/dashboard
py -m streamlit run app.py
```

Dashboard runs at: `http://localhost:8501`

## Pages

| Page | File | Purpose |
|------|------|---------|
| **Home** | `app.py` | Overview, metrics, framework summary |
| **Overview** | `pages/1_Overview.py` | Model profiles, consciousness map |
| **Identity Stack** | `pages/2_Identity_Stack.py` | Layer 0-3 visualization |
| **Drift Analysis** | `pages/3_Drift_Analysis.py` | RMS drift metrics and formulas |
| **Distillations** | `pages/4_Distillations.py` | Cross-model synthesis insights |
| **Raw Data** | `pages/5_Raw_Data.py` | Explore raw armada responses |

## Data Sources

The dashboard reads from:
- `../data/` - Processed data
- `../../experiments/temporal_stability/S7_ARMADA/armada_results/` - Raw armada JSON
- `../extractions/` - Tagged consciousness passages
- `../distillations/` - Synthesis documents

## Dependencies

```
streamlit>=1.30.0
```

See `../requirements.txt` for full list.

## Customization

### Adding New Pages

1. Create `pages/N_PageName.py` (number prefix controls order)
2. Follow existing page structure:
   ```python
   import streamlit as st
   st.set_page_config(page_title="Title", page_icon="🔬", layout="wide")
   st.title("🔬 Page Title")
   # ... content
   ```

### Styling

Custom CSS is in `app.py`. Key classes:
- `.main-header` - Large purple header
- `.sub-header` - Gray subtitle
- `.insight-box` - Highlighted insight boxes

## Integration

- **Pan Handlers Matrix**: Links to `../../Pan_Handlers/pages/matrix.py`
- **S7 ARMADA**: Data source at `../../experiments/temporal_stability/S7_ARMADA/`
- **Main Dashboard**: Links to `../../dashboard/`

---

*See `START_HERE.md` for full development context.*
