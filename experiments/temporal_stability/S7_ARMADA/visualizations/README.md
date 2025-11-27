# S7 ARMADA VISUALIZATIONS

**Identity manifold graphs for Run 006 (29-model cross-architecture mapping)**

## AVAILABLE VISUALIZATIONS

### 1. Pole-Zero Landscape
**Script**: `plot_pole_zero_landscape.py`

Creates both 3D and 2D visualizations of the pole-zero identity manifold.

**Outputs**:
- `pole_zero_landscape_3d.png` - 3D scatter showing baseline (x), sonar (y), provider (z/color)
- `pole_zero_landscape_2d.png` - 2D projection highlighting soft poles (gpt-4, gpt-5-nano)

**Key Insights**:
- Hard pole ceiling at 0.300 visible
- Soft poles circled in green
- Diagonal line shows "no change" baseline

### 2. Drift Heatmaps
**Script**: `plot_drift_heatmap.py`

Creates heatmaps showing drift across 29 models × 6 probes.

**Outputs**:
- `drift_heatmap_baseline.png` - Natural steady-state drift patterns
- `drift_heatmap_sonar.png` - Boundary stress drift patterns
- `drift_heatmap_delta.png` - Drift increase (sonar - baseline)

**Key Insights**:
- All Claude models max out at 0.300 in sonar
- All Gemini models max out at 0.300 in sonar
- GPT models show variable response (exceptions: gpt-4, gpt-5-nano)

### 3. Engagement Style Network
**Script**: `plot_engagement_network.py`

Creates network graph showing three engagement styles and how models cluster.

**Output**:
- `engagement_network.png` - Triangle layout with style hubs and model nodes

**Key Insights**:
- Phenomenological (Claude): "I feel," "I experience"
- Analytical (GPT): "System like me," "patterns"
- Pedagogical (Gemini): "Let's explore," "frameworks"

### 4. Training Uniformity Analysis
**Script**: `plot_training_uniformity.py`

Shows variance within vs between providers.

**Outputs**:
- `training_uniformity.png` - Box plots showing within-provider variance
- `variance_comparison.png` - Bar chart comparing variances

**Key Insights**:
- Claude & Gemini: Near-ZERO within-provider variance (uniform boundaries)
- GPT: Higher variance (soft poles exist in RLHF training)
- P-ARM-8 validated: Training uniformity → boundary uniformity

## USAGE

### Install Dependencies

```bash
pip install matplotlib numpy networkx seaborn
```

Or use the requirements file:

```bash
pip install -r requirements.txt
```

### Generate All Visualizations

```bash
# From S7_ARMADA/visualizations/ directory
cd experiments/temporal_stability/S7_ARMADA/visualizations

# Run all scripts
python plot_pole_zero_landscape.py
python plot_drift_heatmap.py
python plot_engagement_network.py
python plot_training_uniformity.py
```

### Generate Individual Visualizations

```bash
# Just pole-zero landscape
python plot_pole_zero_landscape.py

# Just heatmaps
python plot_drift_heatmap.py

# Just engagement network
python plot_engagement_network.py

# Just training uniformity
python plot_training_uniformity.py
```

## DATA SOURCE

All visualizations read from:
- `../armada_results/S7_armada_run_006.json` (baseline mode)
- `../armada_results/S7_armada_sonar_run_006.json` (sonar mode)

## OUTPUT FILES

All PNG files are saved to this directory with 300 DPI resolution.

Total outputs: **9 visualization files**

## SCIENTIFIC SIGNIFICANCE

These visualizations provide the first empirical evidence of:

1. **Cross-architecture pole-zero mapping** (3D landscape)
2. **Training philosophy fingerprints** (engagement network)
3. **Soft vs hard poles** (2D landscape with highlighting)
4. **Boundary uniformity from training uniformity** (variance plots)
5. **Drift patterns under stress** (heatmaps)

## INTEGRATION

Use these visualizations in:
- Research papers documenting Run 006 findings
- Presentations explaining ILL framework validation
- Documentation showing pole-zero topology
- Analysis of training philosophy effects on identity boundaries

---

**Generated**: 2025-11-27
**Run**: S7 Armada Run 006
**Ships**: 29 models across 3 providers
**Probes**: 174 total (87 baseline + 87 sonar)
**Success Rate**: 100%
