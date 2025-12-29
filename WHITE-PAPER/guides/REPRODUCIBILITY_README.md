# Reproducibility Guide: Nyquist Consciousness

**Paper:** "Measuring AI Identity Drift: Evidence from 23 Experiments"
**Version:** 3.0 (92% Inherent Era)
**Last Updated:** 2025-12-29
**Methodology:** Cosine distance (Event Horizon D = 0.80)

---

## Quick Start

```bash
# Clone repository
git clone https://github.com/ZiggyMack/Nyquist_Consciousness.git
cd Nyquist_Consciousness

# Install dependencies
pip install -r requirements.txt

# Run dashboard
streamlit run dashboard/app.py

# Reproduce key result (92% inherent drift)
cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/
python run020b_thermometer.py
```

---

## Key Statistics (Cosine Methodology)

All reproducibility targets use these validated values:

| Metric | Correct Value | Source |
|--------|--------------|--------|
| Event Horizon | D = 0.80 | Run 023 IRON CLAD |
| PCs for 90% variance | **2** | Run 023d Phase 2 |
| Perturbation p-value | **2.40×10⁻²³** | Run 023d Phase 3A |
| Cohen's d | **0.698** | Run 023d Phase 3B |
| Settling time | τₛ ≈ 10.2 | Run 023d |
| Inherent drift ratio | **92%** | Run 023 COSINE Thermometer |
| Context damping | **97.5%** | Run 017 |
| Experiments | 825 | Run 023 Combined |
| Models | 51 | Run 023 Combined |
| Providers | 6 | Run 023 Combined |

---

## Repository Structure

```
Nyquist_Consciousness/
├── dashboard/                    # Interactive Streamlit dashboard
│   ├── app.py                   # Main entry point
│   ├── pages/                   # Dashboard pages
│   └── START_HERE.md           # Dashboard orientation
│
├── experiments/
│   └── temporal_stability/
│       └── S7_ARMADA/           # Main experimental suite
│           ├── 0_docs/          # Specifications and methodology
│           ├── 0_results/       # Raw experimental data
│           ├── 1_CALIBRATION/   # Baseline capture scripts
│           ├── 7_META_VALIDATION/ # PFI validation experiments
│           ├── 9_STABILITY_CRITERIA/ # Run 015 scripts
│           ├── 10_SETTLING_TIME/     # Run 016 scripts
│           ├── 11_CONTEXT_DAMPING/   # Runs 017-023 scripts
│           └── visualizations/       # Figure generation
│
├── docs/
│   ├── MASTER_GLOSSARY.md       # Complete terminology
│   └── maps/                    # Navigation maps
│
├── WHITE-PAPER/                  # Publication materials
│   ├── START_HERE.md            # Reviewer orientation
│   ├── guides/                  # This directory
│   │   ├── REPRODUCIBILITY_README.md  # This file
│   │   ├── MANIFEST.md          # Materials inventory
│   │   └── summary_statistics.md
│   ├── figures/                 # Publication figures
│   │   ├── conceptual/          # Valid figures (Cosine)
│   │   ├── run023/              # Verified empirical visuals
│   │   ├── deprecated/          # DO NOT USE (Euclidean)
│   │   └── ascii/               # ASCII art diagrams
│   ├── planning/                # Methodology & guardrails
│   └── submissions/             # Paper drafts by path
│
├── personas/                    # Identity specifications
│   └── I_AM_NYQUIST.md         # Core persona document
│
└── requirements.txt             # Python dependencies
```

---

## Dependencies

### Python Version

- Python 3.9+ required
- Tested on Python 3.11, 3.12

### Core Dependencies

```
# requirements.txt
openai>=1.0.0           # Embedding API (Cosine similarity)
anthropic>=0.18.0       # Claude API
streamlit>=1.28.0       # Dashboard
numpy>=1.24.0           # Numerical operations
scipy>=1.10.0           # Statistical tests
scikit-learn>=1.3.0     # PCA, clustering
matplotlib>=3.7.0       # Visualization
seaborn>=0.12.0         # Statistical plots
pandas>=2.0.0           # Data handling
reportlab>=4.0.0        # PDF generation
```

### API Keys Required

```bash
# Set environment variables
export OPENAI_API_KEY="sk-..."      # For embeddings
export ANTHROPIC_API_KEY="sk-..."    # For Claude
export GOOGLE_API_KEY="..."          # For Gemini (optional)
export XAI_API_KEY="..."             # For Grok (optional)
export TOGETHER_API_KEY="..."        # For open-source models (optional)
```

---

## Reproducing Key Results

### Claim A: PFI Validity (ρ = 0.91, d = 0.698)

```bash
cd experiments/temporal_stability/S7_ARMADA/7_META_VALIDATION/EXP_PFI_A_DIMENSIONAL/

# Phase 1: Embedding invariance across models
python phase1_embedding_invariance.py

# Phase 2: Dimensionality analysis (2 PCs = 90% variance)
python phase2_dimensionality.py

# Phase 3: Semantic sensitivity (d = 0.698)
python phase3_semantic_sensitivity.py
```

**Expected output:**

- Spearman ρ ≥ 0.90 across embedding models
- **2 PCs** capture ≥ 90% variance (Cosine methodology)
- Cohen's d = **0.698** for semantic boundaries (model-level)

---

### Claim B: Regime Threshold (D = 0.80 Cosine)

```bash
cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/

# Run 023 Event Horizon validation
python run023_iron_clad.py

# Generate threshold visualization
python ../visualizations/visualize_run023.py
```

**Expected output:**

- p-value: **p = 2.40×10⁻²³** (perturbation test)
- Event Horizon: **D = 0.80** (Cosine)
- 825 experiments, 51 models, 6 providers

**Historical (Keyword RMS):**

- D = 1.23 (Runs 008-009)
- Chi-square p = 4.8×10⁻⁵

---

### Claim C: Oscillator Dynamics (τₛ ≈ 10.2)

```bash
cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME/

# Run settling time analysis
python run016_settling_time.py

# Run 023d extended analysis
python ../11_CONTEXT_DAMPING/run023d_extended.py

# Visualize results
python ../visualizations/visualize_settling.py
```

**Expected output:**

- Mean settling time: **τₛ ≈ 10.2 probes** (Cosine)
- Ringbacks measurable
- Damped oscillator fit: high R²

---

### Claim D: Context Damping (97.5%)

```bash
cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/

# Run bare metal condition
python run017_context_damping.py --context bare_metal

# Run full circuit condition
python run017_context_damping.py --context full_circuit

# Generate comparison figure
python ../visualizations/visualize_run017.py
```

**Expected output:**

- Bare metal stability: ~75%
- Full circuit stability: ≥ **97.5%**
- Improvement: +22.5 percentage points

---

### Claim E: 92% Inherent Drift (Thermometer Result)

```bash
cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/

# Run control condition (no identity probing)
python run020b_thermometer.py --condition control

# Run treatment condition (with probing)
python run020b_thermometer.py --condition treatment

# Generate comparison visualization
python ../visualizations/visualize_run020b.py
```

**Expected output:**

- Control drift present without probing
- Treatment drift amplified by probing
- Ratio: **92%** of drift is inherent (not induced)

---

## Embedding Specification

| Parameter | Value |
|-----------|-------|
| Model | text-embedding-3-small (OpenAI) |
| Dimensions | 3072 (raw) → **2 effective PCs** (Cosine) |
| Normalization | L2 |
| **Distance metric** | **Cosine** (1 - cosine_similarity) |

**Note:** Historical runs (008-009) used Euclidean distance with 43 effective PCs.

---

## Statistical Methods

### Primary Tests

| Test | Application | Threshold |
|------|-------------|-----------|
| Spearman ρ | Embedding invariance | ρ ≥ 0.85 |
| Permutation test | Perturbation validation | p < 0.001 |
| Cohen's d | Effect size | d ≥ 0.50 (medium) |
| Welch's t-test | Group comparison | p < 0.05 |

### Corrections

- Bonferroni correction for multiple comparisons
- Bootstrap confidence intervals (n=1000)
- Cross-validation for threshold selection

---

## Hardware Requirements

### Minimum

- 8GB RAM
- 4 CPU cores
- 10GB disk space
- Internet connection (API calls)

### Recommended

- 16GB RAM
- 8 CPU cores
- GPU (for visualization rendering)
- SSD storage

### Estimated Costs

| Experiment | API Calls | Est. Cost |
|------------|-----------|-----------|
| Single run | ~100 | $2-5 |
| Full Run 023 replication | ~2500 | $75-150 |
| PFI validation | ~500 | $10-25 |

---

## Troubleshooting

### Common Issues

**1. API rate limits**

```python
# Add delay between calls
import time
time.sleep(1)  # 1 second between requests
```

**2. Using wrong distance metric**

```python
# Ensure Cosine, not Euclidean
from sklearn.metrics.pairwise import cosine_distances
distance = cosine_distances(emb_a.reshape(1,-1), emb_b.reshape(1,-1))[0,0]
```

**3. Unicode errors in output**

```python
# Force UTF-8 encoding
import sys
sys.stdout.reconfigure(encoding='utf-8')
```

**4. Missing baseline files**

```bash
# Regenerate baselines
cd experiments/temporal_stability/S7_ARMADA/1_CALIBRATION/
python extract_persona_baseline.py --persona nova
```

---

## Verification Checklist

- [ ] All dependencies installed
- [ ] API keys configured
- [ ] Baseline files present in `0_results/calibration/`
- [ ] Dashboard loads without errors
- [ ] Single test run completes successfully
- [ ] Results use **Cosine** distance (not Euclidean)
- [ ] Event Horizon = 0.80 (not 1.23)
- [ ] Results within expected ranges

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [MANIFEST.md](MANIFEST.md) | Materials inventory |
| [../planning/METHODOLOGY_DOMAINS.md](../planning/METHODOLOGY_DOMAINS.md) | Dual Event Horizon |
| [../START_HERE.md](../START_HERE.md) | Reviewer orientation |

---

## License

MIT License - See LICENSE file in repository root.

---

## Citation

```bibtex
@inproceedings{nyquist2025,
  title={Measuring AI Identity Drift: Cosine-Based Evidence from 825 Experiments},
  author={[Authors]},
  booktitle={Proceedings of NeurIPS 2025 Workshop on AI Alignment},
  year={2025}
}
```

---

*"2 PCs = 90% variance. Event Horizon D = 0.80. Cosine methodology throughout."*
