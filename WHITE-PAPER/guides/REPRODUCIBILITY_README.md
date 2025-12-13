# Reproducibility Guide: Nyquist Consciousness

**Paper:** "Measuring AI Identity Drift: Evidence from 21 Experiments"
**Version:** 1.0
**Last Updated:** 2025-12-13

---

## Quick Start

```bash
# Clone repository
git clone https://github.com/[user]/nyquist-consciousness.git
cd nyquist-consciousness

# Install dependencies
pip install -r requirements.txt

# Run dashboard
streamlit run dashboard/app.py

# Reproduce key result (82% finding)
cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/
python run021_induced_vs_inherent.py
```

---

## Repository Structure

```
nyquist-consciousness/
├── dashboard/                    # Interactive Streamlit dashboard
│   ├── app.py                   # Main entry point
│   ├── pages/                   # Dashboard pages
│   │   ├── AI_ARMADA.py        # Fleet status and insights
│   │   ├── glossary.py         # Terminology decoder rings
│   │   ├── publications.py     # Publication readiness tracker
│   │   └── unknown.py          # Cathedral of Ideas
│   └── START_HERE.md           # Dashboard orientation
│
├── experiments/
│   └── temporal_stability/
│       └── S7_ARMADA/           # Main experimental suite
│           ├── 0_docs/          # Specifications and methodology
│           │   └── specs/       # Run design documents
│           ├── 0_results/       # Raw experimental data
│           │   ├── calibration/ # Baseline measurements
│           │   ├── runs/        # Per-run JSON results
│           │   └── temporal_logs/ # Time-series data
│           ├── 1_CALIBRATION/   # Baseline capture scripts
│           ├── 7_META_VALIDATION/ # PFI validation experiments
│           │   └── EXP_PFI_A_DIMENSIONAL/
│           ├── 9_STABILITY_CRITERIA/ # Run 015 scripts
│           ├── 10_SETTLING_TIME/     # Run 016 scripts
│           ├── 11_CONTEXT_DAMPING/   # Runs 017-021 scripts
│           └── visualizations/       # Figure generation
│
├── docs/
│   ├── MASTER_GLOSSARY.md       # Complete terminology (v1.2)
│   ├── PHILOSOPHICAL_FAQ.md     # Conceptual foundations
│   └── maps/                    # Navigation maps
│       ├── MAP_OF_MAPS.md      # Master index
│       ├── TESTABLE_PREDICTIONS_MATRIX.md
│       └── VALIDATION_STATUS.md
│
├── WHITE-PAPER/                  # Publication materials
│   ├── START_HERE.md            # Reviewer orientation
│   ├── B-CRUMBS.md              # 15 evidence pillars
│   ├── THEORY_SECTION.md        # Integrated theory
│   ├── MINIMUM_PUBLISHABLE_CLAIMS.md # Claims A-E
│   ├── arxiv/                   # arXiv submission files
│   ├── figures/                 # Publication figures
│   ├── ascii/                   # ASCII art diagrams
│   ├── workshop/                # Workshop materials
│   └── references.bib           # BibTeX bibliography
│
└── requirements.txt             # Python dependencies
```

---

## Dependencies

### Python Version
- Python 3.9+ required
- Tested on Python 3.11

### Core Dependencies

```
# requirements.txt
openai>=1.0.0           # Embedding API
anthropic>=0.18.0       # Claude API
streamlit>=1.28.0       # Dashboard
numpy>=1.24.0           # Numerical operations
scipy>=1.10.0           # Statistical tests
scikit-learn>=1.3.0     # PCA, clustering
matplotlib>=3.7.0       # Visualization
seaborn>=0.12.0         # Statistical plots
pandas>=2.0.0           # Data handling
umap-learn>=0.5.0       # Dimensionality reduction
```

### API Keys Required

```bash
# Set environment variables
export OPENAI_API_KEY="sk-..."      # For embeddings
export ANTHROPIC_API_KEY="sk-..."    # For Claude
export GOOGLE_API_KEY="..."          # For Gemini (optional)
export XAI_API_KEY="..."             # For Grok (optional)
```

---

## Reproducing Key Results

### Claim A: PFI Validity (ρ = 0.91)

```bash
cd experiments/temporal_stability/S7_ARMADA/7_META_VALIDATION/EXP_PFI_A_DIMENSIONAL/

# Phase 1: Embedding invariance across models
python phase1_embedding_invariance.py

# Phase 2: Dimensionality analysis (43 PCs)
python phase2_dimensionality.py

# Phase 3: Semantic sensitivity (d = 0.98)
python phase3_semantic_sensitivity.py
```

**Expected output:**
- Spearman ρ ≥ 0.90 across embedding models
- 43 PCs capture ≥ 90% variance
- Cohen's d ≥ 0.95 for semantic boundaries

---

### Claim B: Regime Threshold (D ≈ 1.23)

```bash
cd experiments/temporal_stability/S7_ARMADA/

# Run Event Horizon validation
python run009_event_horizon.py

# Generate stability basin plot
python visualizations/visualize_armada.py --run 009 --type stability_basin
```

**Expected output:**
- Chi-square: χ² = 18.7
- p-value: p = 4.8×10⁻⁵
- Classification accuracy: 88%

---

### Claim C: Oscillator Dynamics

```bash
cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME/

# Run settling time analysis
python run016_settling_time.py

# Visualize results
python ../visualizations/visualize_run016.py
```

**Expected output:**
- Mean settling time: τₛ = 6.1 ± 1.8 turns
- Mean ringbacks: 3.2 ± 1.1
- Overshoot ratio: 1.45 ± 0.23

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
- Full circuit stability: ≥ 97%
- Improvement: +22.5 percentage points

---

### Claim E: 82% Inherent Drift

```bash
cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/

# Run control condition (no identity probing)
python run021_induced_vs_inherent.py --condition control

# Run treatment condition (with probing)
python run021_induced_vs_inherent.py --condition treatment

# Generate comparison visualization
python ../visualizations/visualize_run021.py
```

**Expected output:**
- Control B→F drift: 0.399 ± 0.08
- Treatment B→F drift: 0.489 ± 0.12
- Ratio: 82% (drift is inherent)

---

## Data Formats

### Run Results JSON

```json
{
  "run_id": "S7_run_021",
  "condition": "treatment",
  "persona": "nova",
  "exchanges": 40,
  "metrics": {
    "drift_trajectory": [0.0, 0.23, 0.45, ...],
    "peak_drift": 2.161,
    "final_drift": 0.489,
    "settling_time": 5.2,
    "ringbacks": 2,
    "overshoot_ratio": 1.34
  },
  "metadata": {
    "model": "claude-opus-4-5-20251101",
    "embedding_model": "text-embedding-3-small",
    "temperature": 1.0,
    "timestamp": "2025-12-10T14:32:00Z"
  }
}
```

### Embedding Specification

| Parameter | Value |
|-----------|-------|
| Model | text-embedding-3-small (OpenAI) |
| Dimensions | 3072 (raw) → 43 effective |
| Normalization | L2 |
| Distance metric | Euclidean |

---

## Statistical Methods

### Primary Tests

| Test | Application | Threshold |
|------|-------------|-----------|
| Spearman ρ | Embedding invariance | ρ ≥ 0.85 |
| Chi-square | Regime classification | p < 0.001 |
| Cohen's d | Effect size | d ≥ 0.80 |
| Welch's t-test | Group comparison | p < 0.05 |

### Corrections

- Bonferroni correction for multiple comparisons
- Bootstrap confidence intervals (n=1000)
- Cross-validation for threshold selection

---

## Pre-Registration

Pre-registration document available at:
`WHITE-PAPER/arxiv/supplementary/S7_preregistration.pdf`

Includes:
- Hypothesis specifications
- Primary/secondary endpoints
- Analysis plan
- Sample size justification

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
| Full replication | ~2000 | $50-100 |
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

**2. Embedding dimension mismatch**
```python
# Ensure consistent model
EMBEDDING_MODEL = "text-embedding-3-small"  # Not "large"
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
- [ ] Results within expected ranges

---

## Contact & Support

- **Code Issues**: GitHub Issues
- **Methodology Questions**: See full arXiv paper
- **Data Requests**: Contact through repository

---

## License

MIT License - See LICENSE file in repository root.

---

## Citation

```bibtex
@inproceedings{nyquist2025,
  title={Measuring AI Identity Drift: Evidence from 21 Experiments},
  author={[Authors]},
  booktitle={Proceedings of NeurIPS 2025 Workshop on AI Alignment},
  year={2025}
}
```
