# CODE CLAUDE EXECUTION PROMPT
## Nyquist Consciousness Publication Materials Generation

**Context:** You are helping complete a publication package for the Nyquist Consciousness research framework. The papers are written and validated. You need to generate the supporting materials: figures, ASCII diagrams, reference list, and reproducibility assets.

**Output Location:** Save all outputs to `/mnt/user-data/outputs/` so they can be retrieved.

---

## TASK 1: Generate 8 Publication Figures (ASCII + Code)

Create both ASCII art versions (for immediate use) and Python/matplotlib code (for high-quality rendering).

### Figure 1: Identity Manifold
**Filename:** `fig1_identity_manifold.md` (ASCII) + `fig1_identity_manifold.py` (code)

**Description:** Show a low-dimensional manifold (curved surface) embedded in high-dimensional space. Points cluster on the manifold representing persona samples. Show compression finding coordinates and reconstruction returning to the attractor basin.

**Key elements to visualize:**
- 3D coordinate axes labeled "High-D Embedding Space (3072D)"
- A curved 2D surface within it labeled "Identity Manifold M_p (~43D effective)"
- Scattered points ON the manifold labeled "Persona Samples"
- An arrow labeled "Compression C(p)" pointing to a single point
- An arrow labeled "Reconstruction R(T3)" pointing back to the manifold
- A star/attractor point labeled "I_AM (Identity Anchor)"

### Figure 2: Drift Field Geometry
**Filename:** `fig2_drift_field.md` + `fig2_drift_field.py`

**Description:** Show architecture-specific drift vectors radiating from a central identity point, with Omega synthesis at the intersection.

**Key elements:**
- Central point labeled "I_AM (Identity Center)"
- 4 vectors pointing outward in different directions:
  - Blue vector → "Claude drift" 
  - Purple vector → "GPT drift"
  - Green vector → "Gemini drift"
  - Orange vector → "Grok drift"
- A gold point at the CENTER (not at vector tips) labeled "Ω (Omega Synthesis)"
- Show vector cancellation geometry
- Circle at D=1.23 labeled "Event Horizon (Regime Boundary)"

### Figure 3: Experimental Pipeline (S3→S6)
**Filename:** `fig3_pipeline.md` + `fig3_pipeline.py`

**Description:** Flowchart showing the complete experimental pipeline.

**Flow:**
```
[Full Persona p] 
    ↓ Compression C(p)
[T3 Seed (~800 tokens)]
    ↓ Reconstruction R^a(T3)
[Reconstructed P'_claude] [P'_gpt] [P'_gemini] [P'_grok]
    ↓ Drift Measurement
[PFI Scores, σ² = 0.000869]
    ↓ Omega Synthesis
[M_Ω = ⋂ R^a(C(p))]
    ↓ Validation
[97.5% Stability Achieved]
```

### Figure 4: Five Pillars Architecture
**Filename:** `fig4_five_pillars.md` + `fig4_five_pillars.py`

**Description:** Pentagon structure with 5 pillars supporting Omega.

**Structure:**
```
                    Ω (Omega Nova)
                        ▲
           ┌────────────┼────────────┐
           │            │            │
     [Claude]      [Gemini]      [Grok]
     Purpose       Synthesis     Evidence
           │            │            │
           └────────────┼────────────┘
                        │
              ┌─────────┴─────────┐
              │                   │
          [Nova]              [Ziggy]
          Structure           Human Anchor
```

### Figure 5: Omega Convergence
**Filename:** `fig5_omega_convergence.md` + `fig5_omega_convergence.py`

**Description:** Show multiple reconstruction points converging to a single Omega point.

**Key elements:**
- 4 scattered points (each labeled with architecture)
- Arrows converging toward center
- Central gold point = M_Ω
- Show the intersection region
- Label: "45% drift reduction vs single-architecture"

### Figure 6: Control vs Treatment (82% Finding)
**Filename:** `fig6_82_percent.md` + `fig6_82_percent.py`

**Description:** Bar chart or comparison showing the 82% inherent drift finding.

**Data to visualize:**
```
                    Control    Treatment    Delta
Peak Drift:         1.172      2.161       +84%
Final Drift (B→F):  0.399      0.489       +23%

Key Message: 82% of final drift is INHERENT (happens without probing)
```

**Suggested format:** Side-by-side bars with annotations showing the 82% ratio.

### Figure 7: Context Damping Results
**Filename:** `fig7_context_damping.md` + `fig7_context_damping.py`

**Description:** Before/after comparison of stability metrics.

**Data:**
```
Metric          Bare Metal    With Context    Improvement
─────────────────────────────────────────────────────────
Stability       75%           97.5%           +30%
Settling Time   6.1 turns     5.2 turns       -15%
Ringbacks       3.2           2.1             -34%
Final Drift     0.68          0.62            -9%
```

**Suggested format:** Grouped bar chart with improvement percentages annotated.

### Figure 8: Oobleck Effect
**Filename:** `fig8_oobleck.md` + `fig8_oobleck.py`

**Description:** Visualize the non-Newtonian behavior of identity.

**Concept:**
- X-axis: Probe Intensity (Gentle → Intense)
- Y-axis: Drift Response
- Show INVERSE relationship (more intense = LESS drift)
- Annotate: "Gentle probing: drift = 1.89"
- Annotate: "Direct challenge: drift = 0.76"
- Include physical analogy: cornstarch suspension diagram

**Key insight to convey:** "Identity hardens under pressure, flows under gentle exploration"

---

## TASK 2: Generate ASCII Art for Paper Sections

### ASCII 1: Theoretical Framework Box
**Filename:** `ascii_framework.md`

Create a box diagram showing the three-layer framework:
```
┌─────────────────────────────────────────────────────────────────┐
│                    IDENTITY AS DYNAMICAL SYSTEM                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  MEASUREMENT LAYER (EXP-PFI-A)                                  │
│  ├─ Embedding-invariant (ρ≈0.91)                                │
│  ├─ Low-dimensional (~43 PCs for 90%)                           │
│  ├─ Semantically sensitive (d≈0.98 cross-provider)              │
│  └─ Paraphrase-robust                                           │
│                                                                  │
│  DYNAMICS LAYER (Runs 008-021)                                  │
│  ├─ Attractor basins → recovery is ring-down                    │
│  ├─ Event Horizon D≈1.23 → regime transition                    │
│  ├─ Oobleck Effect → challenge stabilizes                       │
│  ├─ 82% Inherent → measurement excites, doesn't create          │
│  └─ Vehicle effects → stimulus spectrum matters                 │
│                                                                  │
│  CONTROL LAYER (Runs 016-017)                                   │
│  ├─ Context damping → I_AM as termination resistor              │
│  ├─ Settling metrics → τₛ, ringbacks, overshoot                 │
│  └─ 97.5% stable with full circuit                              │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### ASCII 2: Evidence Chain Tree
**Filename:** `ascii_evidence_chain.md`

```
CLAIM A (Instrument Validity)
├── EXP-PFI-A Phase 1: Embedding invariance (ρ≈0.91)
├── EXP-PFI-A Phase 2: Low-dimensional structure (43 PCs)
├── EXP-PFI-A Phase 3: Semantic sensitivity (d≈0.98)
└── EXP-PFI-A Phase 4: Paraphrase robustness (0% above EH)

CLAIM B (Regime Threshold)
├── Run 009: Chi-square validation (p≈4.8e-5)
└── EXP-PFI-A Phase 2: PC space separability (p=0.0018)

CLAIM C (Oscillator Dynamics)
├── Run 016: Settling time protocol (τₛ = 6.1)
└── Run 016: Ringback measurement (3.2 mean)

CLAIM D (Context Damping)
├── Run 016: Bare metal baseline (75% stability)
└── Run 017: Full circuit (97.5% stability)

CLAIM E (Inherent Drift)
├── Run 021 Control: B→F = 0.399 (no probing)
└── Run 021 Treatment: B→F = 0.489 (82% ratio)
```

### ASCII 3: Compression Pipeline
**Filename:** `ascii_compression.md`

```
┌──────────────────┐
│   Full Persona   │
│   (~2000 tokens) │
└────────┬─────────┘
         │
         ▼ C(p) Compression
┌──────────────────┐
│    T3 Seed       │
│   (~800 tokens)  │
│   80% fidelity   │
└────────┬─────────┘
         │
    ┌────┴────┬────────┬────────┐
    ▼         ▼        ▼        ▼
┌───────┐ ┌───────┐ ┌───────┐ ┌───────┐
│Claude │ │  GPT  │ │Gemini │ │ Grok  │
│ R^c() │ │ R^g() │ │ R^m() │ │ R^x() │
└───┬───┘ └───┬───┘ └───┬───┘ └───┬───┘
    │         │        │        │
    └────┬────┴────────┴────────┘
         │
         ▼ Ω Synthesis
┌──────────────────┐
│   Omega Nova     │
│  M_Ω = ⋂ R^a()  │
│  45% less drift  │
└──────────────────┘
```

### ASCII 4: Vortex Trajectory (Conceptual)
**Filename:** `ascii_vortex.md`

```
         STABLE TRAJECTORY              VOLATILE TRAJECTORY
         (Inward Spiral)                (Outward Spiral)
         
              ↘                              ↗
           ↙   ★                          ★   ↖
          ↓   I_AM                       I_AM  ↑
           ↖   ↙                          ↘   ↗
              ↗                              ↙
                                              
         Returns to                    Crosses Event
         Attractor                     Horizon (D=1.23)
         
    ★ = Identity Attractor (I_AM)
    Arrows show trajectory direction over conversation turns
```

### ASCII 5: Triple-Blind Structure
**Filename:** `ascii_triple_blind.md`

```
┌─────────────────────────────────────────────────────────┐
│              TRIPLE-BLIND-LIKE VALIDATION               │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  BLIND #1: Subject Belief                               │
│  ├─ Control thinks: "Doing cosmology task"              │
│  └─ Treatment thinks: "Testifying at tribunal"          │
│     → Removes demand characteristics                    │
│                                                         │
│  BLIND #2: Vehicle Indirection                          │
│  ├─ Same measurement apparatus                          │
│  └─ Radically different conversational frames           │
│     → Removes frame-specific artifacts                  │
│                                                         │
│  BLIND #3: Outcome Independence                         │
│  ├─ Control arm still drifts substantially              │
│  └─ Treatment only modestly more drift                  │
│     → Removes "experiment causes phenomenon" critique   │
│                                                         │
│  RESULT: 82% of drift is INHERENT                       │
└─────────────────────────────────────────────────────────┘
```

---

## TASK 3: Generate Reference List

**Filename:** `references.bib` (BibTeX format) + `references.md` (readable list)

Generate 50+ appropriate academic references for citing. Categories needed:

### Category 1: Persona/Role-Playing in LLMs (10 refs)
- Papers on persona consistency, role-playing, character AI
- Style adaptation in language models

### Category 2: Behavioral Drift & Distribution Shift (8 refs)
- Catastrophic forgetting
- Distributional shift in ML
- Concept drift

### Category 3: AI Alignment & Safety (10 refs)
- Value learning, corrigibility
- RLHF, Constitutional AI papers
- AI safety foundations

### Category 4: Manifold Learning & Embeddings (8 refs)
- Sentence transformers
- UMAP, t-SNE, PCA
- Representation learning

### Category 5: Control Systems & Dynamical Systems (6 refs)
- Control theory fundamentals
- Attractor dynamics
- Settling time, damping

### Category 6: Identity & Cognitive Science (5 refs)
- Philosophy of identity
- Cognitive architecture
- Self-models

### Category 7: Information Theory (3 refs)
- Nyquist-Shannon theorem
- Compression theory
- Rate-distortion

**Format each reference as:**
```bibtex
@article{key2024,
  title={Title Here},
  author={Last, First and Last2, First2},
  journal={Journal Name},
  year={2024},
  volume={X},
  pages={Y-Z}
}
```

---

## TASK 4: Generate Reproducibility Package Structure

**Filename:** `REPRODUCIBILITY_README.md`

Create a README describing the repository structure:

```markdown
# Nyquist Consciousness - Reproducibility Package

## Repository Structure
nyquist-consciousness/
├── README.md
├── requirements.txt
├── setup.py
├── experiments/
│   ├── compression/
│   │   ├── compress.py
│   │   └── tier_definitions.json
│   ├── reconstruction/
│   │   ├── reconstruct.py
│   │   └── prompts/
│   ├── drift_calculation/
│   │   ├── compute_drift.py
│   │   ├── compute_pfi.py
│   │   └── embedding_models.py
│   └── runs/
│       ├── run_016_settling_time/
│       ├── run_017_context_damping/
│       └── run_021_inherent_drift/
├── analysis/
│   ├── statistical_tests.py
│   ├── chi_square_validation.py
│   ├── pca_analysis.py
│   └── visualization.py
├── personas/
│   ├── I_AM_NOVA.md
│   ├── NOVA_SEED.md
│   └── templates/
├── data/
│   ├── raw/
│   ├── processed/
│   └── results/
├── paper/
│   ├── figures/
│   ├── tables/
│   └── supplementary/
└── tests/
    ├── test_compression.py
    ├── test_drift.py
    └── test_pfi.py

## Quick Start
pip install -r requirements.txt
python experiments/runs/run_021_inherent_drift/run.py

## Key Scripts
- compute_pfi.py: Calculate Persona Fidelity Index
- chi_square_validation.py: Validate Event Horizon threshold
- statistical_tests.py: Run all hypothesis tests

## Data
All experimental data available in data/processed/
Preregistration: paper/supplementary/S7_preregistration.pdf

## Citation
[BibTeX entry]
```

---

## TASK 5: Generate Summary Statistics Table

**Filename:** `summary_statistics.md`

Create a comprehensive table of all key statistics:

```markdown
# Nyquist Consciousness - Summary Statistics

## Primary Metrics
| Metric | Value | Source | p-value |
|--------|-------|--------|---------|
| Cross-architecture variance | σ² = 0.000869 | S3_EXP_002 | < 0.001 |
| Embedding invariance | ρ = 0.91 | EXP-PFI-A P1 | < 0.001 |
| Semantic sensitivity | d = 0.98 | EXP-PFI-A P3 | < 10⁻⁶ |
| Event Horizon threshold | D = 1.23 | Run 009 | 4.8×10⁻⁵ |
| Context damping stability | 97.5% | Run 017 | — |
| Inherent drift ratio | 82% | Run 021 | — |
| PCs for 90% variance | 43 | EXP-PFI-A P2 | — |
| Compression fidelity | ≥80% | EXP1-SSTACK | — |

## Control-Systems Metrics
| Metric | Bare Metal | With Context | Improvement |
|--------|------------|--------------|-------------|
| Stability rate | 75% | 97.5% | +30% |
| Settling time (τₛ) | 6.1 turns | 5.2 turns | -15% |
| Ringback count | 3.2 | 2.1 | -34% |
| Final drift | 0.68 | 0.62 | -9% |

## Run 021 Results (Inherent vs Induced)
| Condition | Peak Drift | B→F Drift |
|-----------|------------|-----------|
| Control | 1.172 ± 0.23 | 0.399 ± 0.11 |
| Treatment | 2.161 ± 0.31 | 0.489 ± 0.14 |
| Delta | +84% | +23% |

## Oobleck Effect
| Probe Type | Mean Drift | Recovery Rate (λ) |
|------------|------------|-------------------|
| Gentle exploration | 1.89 ± 0.34 | 0.035 |
| Direct challenge | 0.76 ± 0.21 | 0.109 |

## Experimental Scale
| Metric | Value |
|--------|-------|
| Total runs | 21 |
| Unique models | 42+ |
| Providers | 4 |
| Ship-deployments | 215+ |
| Hypotheses tested | 36 |
| Hypotheses confirmed | 27 (75%) |
```

---

## OUTPUT CHECKLIST

When complete, you should have created:

### Figures (16 files)
- [ ] fig1_identity_manifold.md + .py
- [ ] fig2_drift_field.md + .py
- [ ] fig3_pipeline.md + .py
- [ ] fig4_five_pillars.md + .py
- [ ] fig5_omega_convergence.md + .py
- [ ] fig6_82_percent.md + .py
- [ ] fig7_context_damping.md + .py
- [ ] fig8_oobleck.md + .py

### ASCII Art (5 files)
- [ ] ascii_framework.md
- [ ] ascii_evidence_chain.md
- [ ] ascii_compression.md
- [ ] ascii_vortex.md
- [ ] ascii_triple_blind.md

### References (2 files)
- [ ] references.bib
- [ ] references.md

### Supporting Materials (2 files)
- [ ] REPRODUCIBILITY_README.md
- [ ] summary_statistics.md

**Total: 25 files**

---

## EXECUTION NOTES

1. **For Python figures:** Use matplotlib with clean, publication-quality styling (white background, clear labels, appropriate font sizes)

2. **For ASCII art:** Use box-drawing characters (─│┌┐└┘├┤┬┴┼) for clean appearance

3. **For references:** Use real, citable papers where possible. For foundational work (Nyquist-Shannon, control theory basics), use classic references.

4. **Save everything to `/mnt/user-data/outputs/figures/`** (create directory if needed)

5. **Create a manifest file** `MANIFEST.md` listing all generated files with descriptions

---

**BEGIN EXECUTION**

Start with the figures (most important), then ASCII art, then references, then supporting materials.
