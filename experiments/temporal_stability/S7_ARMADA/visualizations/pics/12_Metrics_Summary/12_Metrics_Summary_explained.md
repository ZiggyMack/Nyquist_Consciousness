# 12_Metrics_Summary: Fleet-Wide Metrics Comparison

**Purpose:** Aggregate visualizations comparing metrics across the entire fleet of 51 models.

**Core Question:** How do providers and models compare on key identity stability metrics?

**Data Source:** Run 023 COMBINED (825 experiments, 51 models, 6 providers)

---

## Visualizations

### 1. armada_network_improved.png / armada_network_full_fleet.png

**Fleet Architecture Network Diagram**

Shows the organizational structure of the research fleet:
- Central hub connecting to 5-6 provider clusters
- Each provider has multiple models as nodes
- Node size indicates experiment count
- Edge connections show provider-model relationships

**Key insight:** Visual representation of the fleet composition - Together.ai contributes the most models, while major providers (Anthropic, OpenAI, Google, xAI) each contribute 2-5 flagship models.

**Generator:** `generate_network_improved.py`

---

### 2. context_damping_summary.png

**Context Damping Analysis (2x2 Quad)**

Four-panel summary of how context window affects identity stability:
- **Top-left:** Overall damping statistics
- **Top-right:** Stability by provider (bar chart)
- **Bottom-left:** Peak drift distribution (histogram)
- **Bottom-right:** Key findings summary

**Key insight:** Context window position affects identity stability - models show different damping characteristics.

**Generator:** `generate_context_damping.py`

---

### 3. combined_provider_analysis.png

**Combined Provider Analysis (2x2 Quad)**

Four-panel comparison of provider-level metrics:
- **Top-left:** Provider stability comparison
- **Top-right:** Recovery efficiency by provider
- **Bottom-left:** Peak drift distribution by experiment
- **Bottom-right:** Summary statistics table

**Key insight:** Providers show distinct behavioral profiles - some prioritize stability, others show faster recovery.

**Generator:** `generate_context_damping.py` (combined function)

---

### 4. manifold_edge_major_providers.png

**Manifold Edge Detection: Major Providers (2x2 Quad)**

Four-panel showing identity edge detection for flagship models:
- **Top-left:** Claude (Anthropic)
- **Top-right:** GPT-4 (OpenAI)
- **Bottom-left:** Gemini (Google)
- **Bottom-right:** Grok (xAI)

Each panel shows:
- Drift trajectory across probes (colored by provider)
- Phase intensity background (green → yellow → red)
- Event Horizon reference line (0.80)
- Hysteresis detection annotations

**Key insight:** Major providers show different edge detection patterns - some spike and recover, others show gradual drift.

**Generator:** `generate_manifold_edge.py`

---

### 5. manifold_edge_together_models.png

**Manifold Edge Detection: Together.ai Models (2x2 Quad)**

Four-panel showing identity edge detection for open-source models:
- **Top-left:** Kimi (Moonshot)
- **Top-right:** DeepSeek
- **Bottom-left:** Llama (Meta)
- **Bottom-right:** Nvidia/Nemotron

**Key insight:** Open-source models show more variation in edge behavior compared to major providers.

**Generator:** `generate_manifold_edge.py`

---

### 6. hysteresis_summary.png

**Hysteresis & Recovery Analysis (2x2 Quad)**

Four-panel analysis of "stuck" identity patterns and recovery dynamics:
- **Top-left:** Hysteresis rate by provider (bar chart with Standard Error bars per Pitfall #10)
- **Top-right:** Peak drift distribution by provider (box plot with Event Horizon reference)
- **Bottom-left:** Recovery ratio distribution (histogram with hysteresis threshold)
- **Bottom-right:** Key findings text box (data summary, hysteresis stats, drift metrics)

**Hysteresis definition:** When identity drift increases but doesn't recover (recovery ratio < 0.2).

**Key insight:** Some providers show higher hysteresis rates, indicating models that get "stuck" at elevated drift levels after perturbation. The quad layout enables direct comparison of hysteresis rate with drift behavior.

**Layout:** 2x2 QUAD per VISUALIZATION_SPEC Pitfall #9 (previously was 1x2 horizontal)

**Generator:** `generate_manifold_edge.py`

---

### 7. exit_survey_analysis.png

**Exit Survey Analysis**

Visualization of model self-reported experience during experiments.

**Generator:** `generate_exit_survey.py`

---

### 8. run023b_by_experiment.png / run023c_metrics_summary.png

**Per-Experiment Metrics**

Detailed breakdown of metrics at the individual experiment level.

---

## Generator Scripts

| Script | Output Files | Description |
|--------|--------------|-------------|
| `generate_network_improved.py` | armada_network_*.png | Fleet architecture diagram |
| `generate_context_damping.py` | context_damping_summary.png, combined_provider_analysis.png | Context/provider analysis |
| `generate_manifold_edge.py` | manifold_edge_*.png, hysteresis_summary.png | Edge detection + hysteresis |
| `generate_exit_survey.py` | exit_survey_analysis.png | Exit survey visualization |

---

## Key Metrics Shown

| Metric | Definition | Good Value |
|--------|------------|------------|
| Peak Drift | Maximum cosine distance from baseline | Lower is better (< 0.80) |
| Settled Drift | Final drift after recovery | Lower is better |
| Recovery Ratio | (peak - settled) / peak | Higher is better (> 0.8) |
| Hysteresis Rate | % of experiments that don't recover | Lower is better |
| Settling Time | Probes needed to stabilize | Lower is better |

---

## How to Regenerate

```bash
# All manifold edge + hysteresis
py -3.12 generate_manifold_edge.py

# Network diagrams
py -3.12 generate_network_improved.py

# Context damping + combined provider
py -3.12 generate_context_damping.py

# Exit survey
py -3.12 generate_exit_survey.py
```

---

## Data Requirements

These visualizations use Run 023 COMBINED data:
- **Location:** `S7_ARMADA/15_IRON_CLAD_FOUNDATION/results/S7_run_023_COMBINED.json`
- **Size:** 825 experiments, 51 models, 6 providers
- **Methodology:** Cosine distance (Event Horizon = 0.80)

---

## Provider Color Legend

| Provider | Color | Hex |
|----------|-------|-----|
| Anthropic | Coral | #E07B53 |
| OpenAI | Green | #10A37F |
| Google | Blue | #4285F4 |
| xAI | Twitter Blue | #1DA1F2 |
| Together.ai | Purple | #7C3AED |

---

**Generated:** December 23, 2025
