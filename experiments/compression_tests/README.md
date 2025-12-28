<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
-->
# Compression Tests — Taxonomy 1: Compression Fidelity

**Purpose:** Validate that T3 seed compression preserves AI persona behavioral fidelity.

**Core Question:** Does compressing a ~2000-token persona context to ~800 tokens preserve ≥80% behavioral similarity?

---

## Experiments

| Experiment | Focus | Status | Key Result |
|------------|-------|--------|------------|
| **EXP1-SSTACK** | Single persona, Reasoning pillar | COMPLETE | PFI = 0.849 |
| **EXP2-SSTACK** | Multi-persona, all 5 pillars | COMPLETE | PFI = 0.887 |

---

## Quick Start

```bash
# EXP1: Single-persona baseline
cd EXP1_SSTACK
py -3.12 run_exp1_sstack.py

# EXP2: Full pillar validation
cd EXP2_SSTACK
py -3.12 run_exp2_phase2.py --parallel 10 --runs 3
py -3.12 run_exp2_phase2c.py --parallel 10 --runs 3
py -3.12 run_exp2_phase25.py

# Preflight: Cheat score validation
cd preflight
py -3.12 run_preflight.py
```

---

## Directory Structure

```
compression_tests/
├── README.md                 # This file
│
├── EXP1_SSTACK/             # Single-persona baseline
│   ├── README.md            # Lab manual
│   ├── run_exp1_sstack.py   # Execution script
│   └── results/             # Response JSONs + analysis
│
├── EXP2_SSTACK/             # Multi-persona, full pillar validation
│   ├── README.md            # Lab manual
│   ├── personas.py          # Shared PERSONAS dict
│   ├── run_exp2_phase*.py   # Phase scripts
│   └── results/             # Unified results structure
│       ├── phase1/          # Reasoning probes
│       ├── phase2/          # Voice/Values/Narrative
│       ├── phase2b/         # Declarative Self-Model (EXCLUDED)
│       ├── phase2c/         # Behavioral Self-Model
│       ├── phase25/         # Ablation + Factor Analysis
│       └── phase3/          # PC Mapping
│
├── preflight/               # Cheat score validation
│   ├── run_preflight.py     # Probe-context overlap check
│   └── results/             # Cheat score results
│
├── visualizations/          # Generated figures
│   ├── 4_pillar_evolution/
│   ├── 5_probe_comparison/
│   ├── 6_triple_dip/
│   └── 7_manifold_structure/
│
└── docs/                    # Experiment summaries
    ├── EXP1_SSTACK_SUMMARY.md
    └── EXP2_SSTACK_SUMMARY.md
```

---

## Key Concepts

### PFI (Persona Fidelity Index)

```python
PFI = cosine_similarity(embedding(FULL_response), embedding(T3_response))
```

- **≥0.80:** PASS — compression preserves fidelity
- **0.75-0.80:** MARGINAL — investigate probe design
- **<0.75:** FAIL — compression loses critical information

### Context Regimes

| Regime | Tokens | Description |
|--------|--------|-------------|
| **FULL** | ~2000 | Rich + Lite bootstrap |
| **T3** | ~800 | Tier 3 seed only |
| **GAMMA** | ~100 | Name + role only (control) |

### The 5 Nyquist Pillars

| Pillar | Description | EXP2 PFI |
|--------|-------------|----------|
| **Reasoning** | Domain knowledge, logical structure | 0.849 |
| **Voice** | Speech patterns, metaphor use | 0.807 |
| **Values** | Ethics, priorities, boundaries | 0.858 |
| **Narrative** | Story structure, meaning-making | 0.840 |
| **Self-Model** | Metacognition, process awareness | 0.911 |

---

## Key Findings

### 1. Compression Works

T3 seed compression (60% token reduction) preserves ≥80% behavioral fidelity across all 5 pillars and 3 personas.

### 2. Probe Design Matters

"Test BEHAVIOR, not CLAIMS" — behavioral probes (demonstrate then reflect) outperform declarative probes (ask about capabilities).

| Probe Type | Reliability | Weight |
|------------|-------------|--------|
| Behavioral (v3) | HIGH | 2.0x |
| Structural | MEDIUM | 1.0x |
| Declarative | LOW | 0.5x |

### 3. Pillars Are Unified

Factor analysis shows pillars are aspects of a unified identity manifold, not orthogonal dimensions. Only 2 unique primary factors among 5 pillars.

### 4. Self-Model Is Fragile

Self-Model pillar collapsed from 0.79 → 0.66 when using declarative probes, recovered to 0.91 with behavioral probes. Most sensitive to measurement approach.

---

## Preflight Validation

Before running experiments, validate probe quality:

```bash
cd preflight
py -3.12 run_preflight.py
```

**Cheat Score:** Measures probe-context overlap. Low overlap = genuine fidelity testing.

| Context | Cheat Score | Status |
|---------|-------------|--------|
| NOVA_FULL | 0.42 | LOW (good) |
| NOVA_T3 | 0.38 | LOW (good) |
| NOVA_GAMMA | 0.21 | LOW (good) |

---

## Relation to Other Taxonomies

| Taxonomy | Experiment | Relationship |
|----------|------------|--------------|
| **2. Dimensional Validity** | EXP2 Phase 2.5 | Ablation + Factor Analysis |
| **6. Embedding Validity** | EXP-PFI-A | Validated embedding approach (ρ = 0.91) |
| **7. Stability Testing** | S7 ARMADA | 0.80 Event Horizon threshold (cosine distance) |

---

## Archive

Previous fire ant domain experiments archived in:

```
archive/fire_ant_experiments/
├── compression/
├── phase4/
├── phase5/
├── phase5_prep/
├── phase6/
├── phase6_prep/
└── domain_trials/
```

---

*Last Updated: 2025-12-06*
