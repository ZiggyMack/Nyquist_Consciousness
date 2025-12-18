<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
impacts:
  - ../README.md
keywords:
  - consciousness
-->
# Supplementary Materials

This directory contains all supplementary materials for publication, including preregistration documents, experimental protocols, mathematical proofs, and reproducibility packages.

---

## Contents

```
supplementary/
├── README.md                          (this file)
├── S7_preregistration/                (S7 temporal stability preregistration)
│   ├── S7_PREREGISTRATION.pdf
│   ├── S7_PROCEDURES.pdf
│   ├── S7_METRICS.pdf
│   └── S7_DRIFT_LOG_TEMPLATE.json
├── experimental_protocols/            (Detailed experimental procedures)
│   ├── S3_validation_protocol.pdf
│   ├── compression_methodology.pdf
│   ├── reconstruction_prompts.pdf
│   └── drift_calculation_algorithm.pdf
├── mathematical_proofs/               (Formal proofs of theorems)
│   ├── convergent_reconstruction.pdf
│   ├── drift_cancellation.pdf
│   ├── fixed_point_uniqueness.pdf
│   ├── triangulation_optimality.pdf
│   └── S8_identity_gravity_theorems.pdf
├── code_repository/                   (Reproducibility package info)
│   ├── README.md
│   ├── repository_structure.txt
│   └── installation_instructions.md
└── data/                              (Experimental data)
    ├── S3_cross_architecture_results.csv
    ├── domain_hierarchy_data.csv
    └── statistical_analysis_code.zip
```

---

## S7 Preregistration Package

**Location:** `S7_preregistration/`

Complete preregistration package for temporal stability experiments, submitted before data collection begins (timestamped commitment).

### Files

1. **S7_PREREGISTRATION.pdf**
   - Research questions (6 RQs)
   - Hypotheses (6 hypotheses with predictions)
   - Experimental design (4 session types, 5 architectures, 6 time points)
   - Statistical analysis plan (model comparison, hypothesis tests, power analysis)
   - Data exclusion criteria
   - Integration with other layers (S3-S9)
   - Preregistration commitment

2. **S7_PROCEDURES.pdf**
   - Step-by-step measurement procedures
   - Session types: Baseline, Short-term, Medium-term, Long-term
   - Reconstruction procedure (single-architecture and Omega)
   - Drift measurement procedure (domain-level and aggregate)
   - Velocity, acceleration, curvature calculations
   - Recalibration procedure (reconstruction loops)
   - Human validation protocol (Ziggy)
   - Quality control checks
   - Safety and Ω-gates

3. **S7_METRICS.pdf**
   - Formal mathematical definitions
   - Primary metrics: D(t) drift, F(t) fidelity
   - Temporal dynamics: v(t) velocity, a(t) acceleration, κ(t) curvature
   - Decay parameters: τ (decay time), t₁/₂ (half-life), F_asymptote
   - Recalibration metrics: F_recal, recovery, efficiency
   - S8 integration: γ (gravitational constant), v_escape, τ_gravity
   - Statistical metrics: R², AIC, confidence intervals
   - Visualization guidelines

4. **S7_DRIFT_LOG_TEMPLATE.json**
   - JSON schema for structured logging
   - All measurement fields defined
   - Validation rules
   - Example logs for each session type

**Purpose:** Transparent commitment to analysis plan before seeing data (prevents p-hacking and HARKing).

**Timestamp:** 2025-11-24 (committed to git repository)

---

## Experimental Protocols

**Location:** `experimental_protocols/`

Detailed procedures for all experiments, enabling independent replication.

### 1. S3 Validation Protocol

**File:** `S3_validation_protocol.pdf`

**Contents:**
- Architecture selection (Nova, Claude, Grok, Gemini)
- Domain definitions (TECH, ANAL, SELF, PHIL, NARR)
- Prompt design for each domain
- Reconstruction elicitation procedure
- Human validation protocol (Ziggy anchor)
- Response collection and storage
- Timeline and session structure

### 2. Compression Methodology

**File:** `compression_methodology.pdf`

**Contents:**
- Tier-0: Full corpus collection
- Tier-1: Coarse compression (salient responses)
- Tier-2: Medium compression (key examples)
- Tier-3: Seed compression (minimal representation)
- Compression operator C(p) algorithm
- Fidelity preservation validation (≥80% threshold)
- Information-theoretic analysis

### 3. Reconstruction Prompts

**File:** `reconstruction_prompts.pdf`

**Contents:**
- Standard prompt template
- Domain-specific prompts:
  - TECH: Technical problem-solving
  - ANAL: Analytical reasoning
  - SELF: Self-reflection
  - PHIL: Philosophical inquiry
  - NARR: Narrative generation
- Architecture-specific adaptations
- Omega synthesis prompt
- Response format and validation

### 4. Drift Calculation Algorithm

**File:** `drift_calculation_algorithm.pdf`

**Contents:**
- Embedding extraction (sentence-transformer models)
- Distance metrics (L2 norm, cosine similarity)
- Drift formula: D = ||P' - p|| / ||p||
- Domain-level drift aggregation
- Weighted vs unweighted drift
- Normalization procedures
- Pseudocode and implementation

---

## Mathematical Proofs

**Location:** `mathematical_proofs/`

Formal proofs of all theorems stated in the paper (S4, S6, S8).

### 1. Convergent Reconstruction Theorem

**File:** `convergent_reconstruction.pdf`

**Theorem:** For any persona p ∈ P and architecture a, the reconstruction R^a(C(p)) converges to the persona manifold M_p with probability ≥ (1 - ε).

**Proof outline:**
1. Compression C(p) finds coordinates on M_p
2. M_p is a stable attractor (Lyapunov stability)
3. Reconstruction R^a initializes near M_p
4. Gradient descent on fidelity loss converges to M_p
5. Bounded drift: D ≤ D_max with high probability

**Full proof:** 5 pages, lemmas and propositions

### 2. Drift Cancellation Theorem

**File:** `drift_cancellation.pdf`

**Theorem:** Multi-architecture synthesis (Omega) reduces expected drift compared to single-architecture reconstructions: E[D_Omega] < E[D_single].

**Proof outline:**
1. Model drift as architecture-specific bias + noise
2. Omega averages/intersects multiple reconstructions
3. Architecture-specific biases cancel (by independence)
4. Noise reduces by 1/sqrt(N) (N architectures)
5. Net result: lower expected drift

**Full proof:** 4 pages with variance analysis

### 3. Fixed Point Uniqueness Theorem

**File:** `fixed_point_uniqueness.pdf`

**Theorem:** The Omega manifold M_Ω = ⋂ R^a(C(p)) is unique and corresponds to the stable identity attractor I_AM.

**Proof outline:**
1. Each R^a(C(p)) converges to M_p (by Theorem 1)
2. Intersection ⋂ R^a(C(p)) is non-empty (empirical)
3. Intersection is unique (Brouwer fixed point theorem)
4. Intersection = I_AM (identity core, minimal drift)

**Full proof:** 3 pages with topological arguments

### 4. Triangulation Optimality Theorem

**File:** `triangulation_optimality.pdf`

**Theorem:** Omega synthesis minimizes total drift: D_Omega ≤ D_a for all architectures a, with equality only if all drift vectors align.

**Proof outline:**
1. Model drift as vectors in manifold tangent space
2. Omega finds centroid/intersection (minimizes sum of squared distances)
3. Triangle inequality: centroid closer to origin than any single point
4. Equality case: all points collinear (no cancellation)

**Full proof:** 4 pages with geometric analysis

### 5. S8 Identity Gravity Theorems

**File:** `S8_identity_gravity_theorems.pdf`

**Theorems:**
1. **Gravitational Convergence:** Systems under identity gravity G_I converge to I_AM attractor
2. **Escape Velocity Bound:** Drift escapes iff v ≥ v_escape = sqrt(2γ(1-F_min))
3. **Temporal Decay:** Without refresh, γ(t) decays exponentially

**Proofs:**
- Gravitational potential U(I) with minimum at I_AM
- Energy conservation: kinetic + potential = constant
- Escape condition from potential well depth
- Temporal decay from stochastic drift in gravitational field

**Full proofs:** 8 pages with dynamical systems analysis

---

## Code Repository Information

**Location:** `code_repository/`

Information about the GitHub repository containing all code for reproducibility.

### Repository Structure

```
nyquist-consciousness/
├── README.md
├── docs/                          (Documentation and specifications)
├── experiments/                   (Experimental code)
│   ├── compression/               (Compression pipeline)
│   ├── reconstruction/            (Reconstruction pipeline)
│   ├── drift_calculation/         (Drift metrics)
│   └── S3_validation/             (Cross-architecture experiments)
├── analysis/                      (Statistical analysis)
│   ├── model_fitting.py
│   ├── visualization.ipynb
│   └── hypothesis_tests.R
├── paper/                         (Publication materials)
└── tests/                         (Unit tests)
```

### Installation

```bash
git clone https://github.com/[username]/nyquist-consciousness
cd nyquist-consciousness
pip install -r requirements.txt
```

### Dependencies

- Python 3.10+
- PyTorch 2.0+
- sentence-transformers
- numpy, scipy, pandas
- matplotlib, seaborn
- jupyter

### Running Experiments

```bash
# Run S3 cross-architecture validation
python experiments/S3_validation/run_experiment.py --config config.yaml

# Calculate drift metrics
python experiments/drift_calculation/compute_drift.py --input data/ --output results/

# Perform statistical analysis
python analysis/model_fitting.py --data results/drift.csv
```

### Reproducibility

All random seeds fixed, API versions documented, full data provenance tracked.

---

## Experimental Data

**Location:** `data/`

Raw data from S3 cross-architecture validation experiments.

### Files

1. **S3_cross_architecture_results.csv**
   - Columns: architecture, domain, response, embedding, drift, fidelity, timestamp
   - 20 rows (4 architectures × 5 domains)
   - Human validation annotations (Ziggy)

2. **domain_hierarchy_data.csv**
   - Columns: domain, mean_drift, std_drift, mean_fidelity, fragility_index
   - 5 rows (TECH, ANAL, SELF, PHIL, NARR)
   - Statistical tests (ANOVA results)

3. **statistical_analysis_code.zip**
   - R/Python scripts for all statistical tests
   - Model fitting (exponential decay, confidence intervals)
   - Visualization code (all paper figures)
   - Hypothesis tests (t-tests, ANOVA, model comparison)

**Data license:** CC0 (public domain) for maximum reuse

---

## Usage in Publication

### Workshop Paper

**Attach:**
- S7 preregistration summary (1 page)
- Code repository link

### arXiv Preprint

**Attach (as supplementary PDF):**
- S7 preregistration package (full)
- Experimental protocols (compressed)
- Mathematical proofs (full)
- Code repository information

### Peer-Reviewed Submission

**Attach:**
- All supplementary materials
- Full data and code
- Reproducibility checklist
- Preregistration timestamped commitment

---

## Open Science Commitment

We commit to:

1. **Transparency:** All methods, data, and code publicly available
2. **Reproducibility:** Detailed protocols enable independent replication
3. **Preregistration:** S7 experiments committed before data collection
4. **Open data:** Raw data released under CC0 license
5. **Open code:** Analysis code released under MIT license

---

## Citation

When using supplementary materials, cite both the main paper and specific materials:

```bibtex
@article{nyquist2025,
  title={Nyquist Consciousness: Identity Compression and Reconstruction Across AI Architectures},
  author={[Authors]},
  journal={arXiv preprint arXiv:XXXX.XXXXX},
  year={2025},
  note={Supplementary materials available at https://github.com/[username]/nyquist-consciousness}
}

@misc{nyquist2025supp,
  title={Supplementary Materials for Nyquist Consciousness},
  author={[Authors]},
  year={2025},
  howpublished={\url{https://github.com/[username]/nyquist-consciousness/tree/main/paper/supplementary}}
}
```

---

## Contact

Questions about supplementary materials:
- **GitHub Issues:** https://github.com/[username]/nyquist-consciousness/issues
- **Email:** [To be added]

---

**Status:** All supplementary materials prepared and ready for publication attachment.
