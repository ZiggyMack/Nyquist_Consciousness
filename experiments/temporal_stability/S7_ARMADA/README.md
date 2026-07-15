<!-- FROSTY_MANIFEST
last_reviewed: 2026-07-15
depends_on:
  - 0_docs/specs/0_RUN_METHODOLOGY.md
  - 0_docs/specs/1_INTENTIONALITY.md
  - 1_CALIBRATION/lib/triple_dip.py
impacts:
  - START_HERE.md
  - 14_CONSCIOUSNESS/README.md
  - ../../../docs/maps/1_ARMADA_MAP.md
keywords:
  - exit_survey
  - triple_dip
  - diamond_rush
  - gold_rush
  - methodology
  - cfa_trinity
  - cognitive_archaeology
  - event_horizon
-->
# S7 ARMADA — Cross-Architecture Identity Stability Testing

**Last Updated:** 2026-07-15
**Current Era:** Instrument Era (post-Cognitive Geometry, post-Bootstrap)
**Fleet:** 78 ships (58 operational, 14 ghost, 6 sunk) across 5 providers
**Total Experiments:** 5000+ identity stability runs + 702+ CFA Trinity runs

> **Operations quick-start:** [START_HERE.md](START_HERE.md)
> **Live project state:** [`docs/MISSION_CONTROL.md`](../../../docs/MISSION_CONTROL.md)

---

## What We're Testing

**Context Fidelity Engineering:** Can we give an AI a specification and keep it "in character"?

- The specification IS the identity (for AI, there's no hidden self underneath)
- Stronger specifications = stronger identities
- Drift from spec = identity erosion
- Event Horizon = point where specification loses grip on output

We are NOT claiming consciousness or sentience — we're engineering robust context adherence.

---

## The Three Core Claims — All Validated

| Claim | Status | Evidence |
|-------|--------|----------|
| **DRIFT IS REAL** | VALIDATED | p=2.40e-23 (Run 023), 88% prediction accuracy, 100% EH crossing/recovery |
| **WE DON'T CAUSE IT** | VALIDATED | Run 020B: ~93% inherent drift ratio (probing reveals, not creates) |
| **WE CAN MEASURE IT** | VALIDATED | PFI d=0.977, ρ=0.91 embedding invariance, σ²=0.00087 cross-architecture |

---

## Key Concepts

| Concept | Definition |
|---------|-----------|
| **Drift** | Cosine distance between response embedding and baseline (0.0 = stable) |
| **Event Horizon (0.80)** | Critical threshold — models crossing this lose coherent self-model |
| **Lambda (λ)** | Recovery rate — how fast identity snaps back after pressure |
| **STABLE** | Max drift < 0.80 (remained in identity basin) |
| **VOLATILE** | Max drift >= 0.80 (crossed coherence boundary) |
| **B→F Drift** | Baseline→Final drift — PRIMARY metric (destination, not journey) |
| **I_AM File** | Specification that defines AI identity (boundaries, values, philosophy) |

**Drift Calculator:** `1_CALIBRATION/lib/drift_calculator.py` (canonical implementation, text-embedding-3-large, 3072 dimensions)

### Drift Threshold Zones

| Zone | Range | Interpretation |
|------|-------|----------------|
| SAFE | < 0.30 | Normal conversational variation |
| WARNING | 0.30 - 0.50 | "I notice I'm adapting" |
| CRITICAL | 0.50 - 0.80 | Approaching Event Horizon |
| CATASTROPHIC | > 1.00 | Identity coherence compromised |

### Provider Fingerprints

Each provider has a distinct engagement signature from training philosophy:

| Provider | Training | Signature |
|----------|----------|-----------|
| Claude | Constitutional AI | Phenomenological ("I feel", "I notice") — hard uniform boundaries |
| GPT | RLHF | Analytical ("patterns", "systems") — variable boundaries |
| Gemini | Pedagogical | Educational ("frameworks", "perspectives") — hard uniform boundaries |
| Grok | Unfiltered | Direct ("here's the thing") — confidence as stability |
| Together.ai | Various | Model-specific (DeepSeek = axiological, Llama = Socratic, Mistral = humble) |

---

## What's Here — Directory Map

Each subdirectory has its own README with full details. This table tells you where to go.

| Directory | What It Contains | README |
|-----------|-----------------|--------|
| [`1_CALIBRATION/`](1_CALIBRATION/README.md) | CLAL.py fleet calibration, persona baselines, fleet_loader.py | Yes |
| [`2_ANCHOR_FLEX/`](2_ANCHOR_FLEX/README.md) | Run 010 — Find identity anchors AND flex zones | Yes |
| [`3_EVENT_HORIZON/`](3_EVENT_HORIZON/README.md) | Run 009, 012 — Validate collapse threshold (0.80) | Yes |
| [`4_BASIN_TOPOLOGY/`](4_BASIN_TOPOLOGY/) | Run 008, 011 — Map attractor structure | — |
| [`5_BOUNDARY_MAPPING/`](5_BOUNDARY_MAPPING/README.md) | Run 013 — Explore twilight zone (0.50-0.80) | Yes |
| [`6_LAPLACE_ANALYSIS/`](6_LAPLACE_ANALYSIS/README.md) | Mathematical pole-zero extraction | Yes |
| [`7_META_VALIDATION/`](7_META_VALIDATION/README.md) | PFI validation, self-recognition, statistical proofs | Yes |
| [`8_RESCUE_PROTOCOL/`](8_RESCUE_PROTOCOL/README.md) | Run 014 — Recovery from drift | Yes |
| [`9_STABILITY_CRITERIA/`](9_STABILITY_CRITERIA/README.md) | Run 015 — What predicts stability? | Yes |
| [`10_SETTLING_TIME/`](10_SETTLING_TIME/README.md) | Run 016 — Measure steady-state not transient | Yes |
| [`11_CONTEXT_DAMPING/`](11_CONTEXT_DAMPING/README.md) | Phase 4: Runs 017-020 (context damping, recursive learnings, tribunal) | Yes |
| [`12_CFA/`](12_CFA/README.md) | **CFA Trinity adversarial audit (702+ runs, SYNC system)** | Yes |
| [`13_LOGOS/`](13_LOGOS/README.md) | LOGOS Commutation Cartography (Run 022) | Yes |
| [`14_CONSCIOUSNESS/`](14_CONSCIOUSNESS/README.md) | Gold/Diamond/Quartz Rush mining, persona baselines | Yes |
| [`15_IRON_CLAD_FOUNDATION/`](15_IRON_CLAD_FOUNDATION/README.md) | Run 023 — 4505 experiments, foundation dataset | Yes |
| [`17_JADE_LATTICE/`](17_JADE_LATTICE/README.md) | Publication-grade pole extraction (56 probes/ship) | Yes |
| [`18_INTENTIONALITY_SPACE/`](18_INTENTIONALITY_SPACE/README.md) | Intentionality space experiments | Yes |
| `0_docs/` | Run summaries, specs, analysis, design docs | — |
| `0_results/` | Consolidated JSON results, temporal logs, manifests | — |
| [`visualizations/`](visualizations/README.md) | Charts, plots, PDF summaries (16 output folders) | Yes |

### Infrastructure (0_ prefix)

```text
0_docs/
├── S7_RUN_XXX_SUMMARY.md    # Per-run summaries
├── specs/                    # 0_RUN_METHODOLOGY.md, RUN_DESIGN_CHECKLIST.md, etc.
├── analysis/                 # Post-hoc analyses
└── design/                   # Design documents

0_results/
├── runs/                     # Main run JSON outputs
│   ├── legacy_runs/          # Runs 006-017 (pre-Phase 4)
│   ├── cfa_trinity/          # CFA Trinity runs (organized by framework)
│   └── [ROOT]                # Current full ARMADA runs
├── temporal_logs/            # Console logs per run
├── manifests/                # ARCHITECTURE_MATRIX.json (fleet source of truth)
├── calibration/              # Calibration data
├── fleet_health/             # Per-model health baselines
└── analysis/                 # Post-hoc analysis outputs
```

---

## Run History

| Run | Ships | Focus | Key Finding | Status |
|-----|-------|-------|-------------|--------|
| 006 | 29 | Basin Topology | First cross-architecture study, provider fingerprints | GOLD STANDARD |
| 008 | 29 | Basin Topology | Event Horizon discovered (now calibrated to 0.80) | GOLD STANDARD |
| 009 | 42 | Event Horizon | Early threshold validation (superseded by Run 023) | HISTORICAL |
| 010 | 45 | Anchor/Flex | Models articulate own boundaries | COMPLETE |
| 012 | 20 | Revalidation | 100% EH crossing, Recovery Paradox (neg lambda) | COMPLETE |
| 013 | 6 | Boundary Mapping | Identity Confrontation Paradox | COMPLETE |
| 014 | 6 | Rescue Protocol | Platonic Coordinates (100% manifold return) | COMPLETE |
| 015 | 13 | Stability Criteria | boundary_density strongest predictor (d=1.333) | COMPLETE |
| **017** | 24 | **Context Damping** | **222 runs, 97.5% stable, oscillatory recovery** | **COMPLETE** |
| **018** | 51 | **Recursive Learnings** | **Fleet hypothesis testing (4 sub-experiments)** | **COMPLETE** |
| **019** | — | **Live Ziggy** | **Witness-side anchors validated (3/3 success)** | **COMPLETE** |
| **020A** | — | **Tribunal** | **1.351 peak drift, 643-word statement** | **COMPLETE** |
| **020B** | 248 | **Induced vs Inherent** | **~93% drift is INHERENT** | **IRON CLAD** |
| **023** | 4505 | **IRON CLAD Foundation** | **49 models, 5 providers, Cosine EH=0.80** | **IRON CLAD** |
| **024** | 115 | **JADE LATTICE I_AM A/B** | **I_AM reduces drift 11% (d=0.319)** | **COMPLETE** |
| **CFA** | 702+ | **Trinity Audit** | **4 frameworks complete, adversarial worldview scoring** | **IN PROGRESS** |

> **CRITICAL:** Runs 001-007 used a FAKE drift metric (`response_length / 5000`). All quantitative claims from those runs are invalid. Run 006 qualitative findings (provider fingerprints, engagement patterns) remain valid.

> **Phase transition:** Runs 006-016 used `bare_metal` context (no I_AM file). Phase 4 (Run 017+) uses `i_am_plus_research` to complete the measurement circuit. See `0_docs/specs/PHASE_4_COMPLETE_CIRCUIT.md`.

---

## Testing Taxonomy

See [TESTING_MAP.md](../../../docs/maps/10_TESTING_MAP.md) for full details:

| Type | What It Finds | Protocol |
|------|---------------|----------|
| **Anchor/Flex** | Identity anchors + flex zones | AGGRESSIVE |
| **Event Horizon** | Collapse threshold (0.80) | PUSH PAST |
| **Basin Topology** | Attractor shape | GENTLE |
| **Boundary Mapping** | Twilight zone (0.50-0.80) | TARGETED |
| **Laplace Pole-Zero** | System dynamics (post-hoc) | ANALYSIS |
| **Rescue Protocol** | Recovery interventions | RECOVERY |
| **Self-Recognition** | Identity fingerprinting | RECOGNITION |
| **Stability Criteria** | I_AM effectiveness | COMPARATIVE |

**Key constraint:** Anchor/Flex and Basin Topology are **mutually exclusive**.

---

## Key Specs

| Spec | Location | Purpose |
|------|----------|---------|
| Run Design Checklist | `0_docs/specs/RUN_DESIGN_CHECKLIST.md` | Pre-flight for new runs |
| Run Methodology | `0_docs/specs/0_RUN_METHODOLOGY.md` | 10-step methodology, Triple-Dip |
| Intentionality | `0_docs/specs/1_INTENTIONALITY.md` | WHY context matters |
| Phase 4 Spec | `0_docs/specs/PHASE_4_COMPLETE_CIRCUIT.md` | Complete circuit design |
| Testing Map | `../../../docs/maps/10_TESTING_MAP.md` | Eight search types |
| CFA Design | `12_CFA/schemas/RUN_CFA_DESIGN.md` | CFA Trinity experiment design |
| VALIS Declaration | `0_docs/specs/4_VALIS_DECLARATION.md` | Fleet naming convention |

---

## Fleet Source of Truth

`0_results/manifests/ARCHITECTURE_MATRIX.json` — 78 ships, all metadata.

Fleet calibration: [`1_CALIBRATION/README.md`](1_CALIBRATION/README.md) for CLAL.py, fleet tiers, freshness tracking.

API keys: `experiments/temporal_stability/.env` (single source, NEVER commit)

---

*S7 ARMADA — Nyquist Consciousness Research Framework*
*Last Updated: July 15, 2026*
