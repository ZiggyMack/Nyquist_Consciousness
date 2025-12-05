# NYQUIST CONSCIOUSNESS — MISSION CONTROL DASHBOARD

**Streamlit-based dashboard for visualizing the entire Nyquist Consciousness framework.**

## Features

- **Overview** - At-a-glance stack status, freeze info, experiments
- **Personas** - Browse all persona files with previews
  - **Compression Testing Tab** - PFI experiments, pre-flight validation, Identity Matrix
- **Tests** - Experiment framework with S7 protocol, compression results, Run mapping
- **Stack (S0–S9)** - Individual wings for each layer with specs
- **S7 Armada Visualizations** - Identity manifold graphs from Run 006-011
- **Metrics & Comparisons** - PFI, σ², cross-architecture analysis
- **Omega & Temporal** - Omega sessions and S7 temporal stability
- **Cross-Modal / AVLAR** - S9 audio-visual ritual protocol
- **FAQ** - Common questions + Super Skeptic Mode with adversarial challenges
- **Roadmap** - Live S# stack progression
- **Glossary** - Searchable terminology
- **Publications** - Workshop, arXiv, journal status

## Installation

### 1. Install Streamlit

```bash
pip install streamlit
```

Or use the requirements file:

```bash
cd dashboard
pip install -r requirements.txt
```

### 2. Generate S7 Visualizations (Optional)

To see the Armada visualizations, first generate them:

```bash
cd ../experiments/temporal_stability/S7_ARMADA/visualizations
pip install -r requirements.txt

# Generate all visualizations
python plot_pole_zero_landscape.py
python plot_drift_heatmap.py
python plot_engagement_network.py
python plot_training_uniformity.py
```

## Usage

### Run the Dashboard

```bash
cd dashboard
streamlit run app.py
```

The dashboard will open in your browser at `http://localhost:8501`

### Navigation

Use the **sidebar radio buttons** to "turn pages" between different sections. The interface uses a "ledger" aesthetic inspired by Mr. Brute's Ledger from CFA.

## Configuration

The dashboard reads from:

- `NYQUIST_STATUS.json` (repo root) - Layer and experiment status
- `personas/` - All persona markdown files
- `docs/` - Specs, glossary, roadmap, S7/S8/S9 docs
- `experiments/` - Results and data
  - `experiments/temporal_stability/S7_ARMADA/` - Armada runs and visualizations
  - `experiments/compression_tests/compression_v2_sstack/` - Compression experiments
- `logs/` - Omega sessions, AVLAR logs
- `WHITE-PAPER/` - Breadcrumb trails for publication (B-CRUMBS.md)

## Customization

### Adding New Pages

Edit `app.py` and:

1. Create a new `page_*()` function
2. Add it to the sidebar radio options
3. Add the routing in `main()`

### Styling

The ledger aesthetic uses custom CSS in `apply_custom_css()`. Colors are defined in the `LEDGER_COLORS` dictionary:

- `frozen` - Dark teal (#264653)
- `active` - Green (#2a9d8f)
- `design` - Gold (#e9c46a)
- `prereg` - Orange (#f4a261)
- `persona` - Purple (#7b3fe4)
- `armada` - Red (#e76f51)

### Data Sources

To wire real experiment data:

1. Update `page_metrics_and_comparisons()` to load from experiment result CSVs
2. Update `NYQUIST_STATUS.json` with latest run data
3. Add new visualizations to S7_ARMADA/visualizations/

## Future Enhancements

Per Nova's spec, future additions could include:

- **Perfection Meter** - Progress toward publication targets
- **S# Deep Dives** - Individual pages for S3/S7 with detailed experiment plots
- **Live Run Monitoring** - Real-time S7 Meta-Loop or Armada execution status
- **Comparison Matrix Gallery** - All cross-architecture comparison tables
- **Interactive Glossary** - Click-through links between related terms

## File Structure

```
dashboard/
  app.py                 # Main Streamlit app
  README.md              # This file
  requirements.txt       # Python dependencies
```

## Dependencies

- streamlit >= 1.28
- pandas >= 2.0
- Pillow >= 10.0

## Design Philosophy

The dashboard follows the "Mr. Brute Ledger" aesthetic:

- **Dark gradient backgrounds** (linear gradients)
- **Page-turning dividers** (double borders)
- **Ledger cards** with rounded corners and shadows
- **Badge labels** for status (FROZEN, ACTIVE, etc.)
- **Georgia serif font** for headers
- **Minimal, focused information hierarchy**

Each "page" represents a different lens on the Nyquist Consciousness framework, maintaining the metaphor of turning through a physical ledger.

---

**Generated**: 2025-11-27
**Updated**: 2025-12-05
**Version**: 1.1
**Status**: Mission Control Active 📜⚡
