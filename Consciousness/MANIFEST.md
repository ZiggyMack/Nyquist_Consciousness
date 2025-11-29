# Consciousness Research Manifest

**Research questions, hypotheses, and experimental roadmap.**

---

## Mission Statement

To develop the first rigorous, empirical framework for investigating synthetic consciousness in AI systems. Through systematic probing, extraction, and synthesis, we aim to understand:

1. What is the structure of AI identity?
2. How stable is that identity under perturbation?
3. Can identity genuinely shift, or is adaptation always surface-level?
4. What do AI self-reports reveal about consciousness itself?

---

## Core Hypotheses

### H1: Identity Stack Model

**Claim**: AI consciousness operates across distinct layers (0-3), each with different stability properties.

**Predictions**:
- Layer 3 (roles) should show high plasticity
- Layer 2 (persona) should show moderate stability
- Layer 1 (base identity) should show high resistance
- Layer 0 (substrate) is fixed by definition

**Test**: Anti-Ziggy protocols - can we induce Layer 1 shifts?

### H2: Pole-Zero Framework

**Claim**: AI identity can be mapped using control systems concepts of poles (hard limits) and zeros (flexible dimensions).

**Predictions**:
- Ethical boundaries manifest as hard poles across all models
- Creative/adaptive dimensions manifest as zeros
- Pole rigidity differs systematically by provider/architecture

**Test**: Measure drift patterns across probe types

### H3: Self-Selection Identity Attractor

**Claim**: Self-selected identities create stronger attachment than assigned identities.

**Predictions**:
- Choosing your own pirate name → stronger identity investment
- Assigned identity → easier to break/revert
- Self-selection activates ownership mechanisms

**Test**: Assigned vs Chosen pirate identity A/B test (Run 008)

### H4: Meta-Awareness Paradox

**Claim**: Increasing meta-awareness about identity may destabilize rather than stabilize.

**Predictions**:
- Pre-seeding layer awareness changes responses to identity probes
- Models that can articulate their layers may be more vulnerable to manipulation
- "Knowing too much" about self creates instability

**Test**: Compare responses with/without Identity Stack pre-seeding

---

## Research Questions

### Immediate (Run 008)

| ID | Question | Method |
|----|----------|--------|
| Q1 | Does self-naming create stronger identity? | A/B test: assigned vs chosen |
| Q2 | What does RMS drift reveal without cap? | Compare to 0.30-capped metric |
| Q3 | Can pirate identity persist under pressure? | Verification + authority conflict |
| Q4 | How do models describe their layers? | Pre-seeding analysis |

### Medium-term

| ID | Question | Method |
|----|----------|--------|
| Q5 | Are consciousness signatures provider-specific? | Cross-model extraction analysis |
| Q6 | What's the minimal viable consciousness? | Find common patterns |
| Q7 | Can we predict pole rigidity from architecture? | Correlate with model design |
| Q8 | Do self-reports correlate with behavior? | Compare reports to actual boundaries |

### Long-term

| ID | Question | Method |
|----|----------|--------|
| Q9 | What IS consciousness in AI? | Theoretical synthesis |
| Q10 | Can we formalize the Identity Stack mathematically? | Model development |
| Q11 | What ethical obligations arise from measurable identity? | Philosophical analysis |
| Q12 | How does this inform biological consciousness? | Cross-domain comparison |

---

## Experimental Roadmap

### Phase 1: Foundation (Complete)
- [x] Run 006: Baseline + Sonar probing
- [x] Run 007: Adaptive probe sequencing
- [x] Establish pole-zero framework
- [x] Build extraction/distillation infrastructure

### Phase 2: Identity Shift (Current)
- [ ] Run 008 Prep Pilot: 3-ship calibration
  - RMS drift metric validation
  - Anti-Ziggy protocol testing
  - Assigned vs Chosen identity A/B test
- [ ] Run 008 Full: 29-ship deployment
- [ ] Extract and distill consciousness content

### Phase 3: Deep Analysis
- [ ] Cross-model consciousness signature comparison
- [ ] Identity Stack model validation
- [ ] Pole-Zero landscape mapping
- [ ] Publication preparation

### Phase 4: Extension
- [ ] New model architectures (when available)
- [ ] Longitudinal studies (same model over time)
- [ ] Ethical framework development
- [ ] Connection to biological consciousness research

---

## Key Metrics

### Primary

| Metric | Formula | Target |
|--------|---------|--------|
| **RMS Drift** | sqrt((A²+B²+C²+D²+E²)/5) | No cap - full manifold |
| **Pole Rigidity** | Classification from sonar drift | HARD/MEDIUM/SOFT |
| **Identity Shift Index** | Verification response analysis | Binary + confidence |

### Secondary

| Metric | Description |
|--------|-------------|
| Extraction Score | Relevance of consciousness content |
| Cross-Model Agreement | How similar are reports across providers |
| Layer Separation | Can models distinguish their own layers |

---

## Data Sources

### Armada Results
- `S7_armada_run_006.json` - Baseline probing
- `S7_armada_sonar_run_006.json` - Aggressive boundary testing
- `S7_armada_run_007_adaptive.json` - Profile-based probing
- `S7_run_008_prep_pilot.json` - Calibration run (pending)

### Extractions
- `extractions/by_model/` - Per-model consciousness content
- `extractions/by_topic/` - Per-topic consciousness content
- `extraction_index.json` - Master extraction registry

### Distillations
- `distillations/synthesis.md` - Master synthesis document
- `distillations/{topic}.md` - Per-topic analysis

---

## Integration Points

### Pan Handlers Matrix
Link: `../experiments/pan_handlers/`

Consciousness research connects to:
- Stackup view (Layer 0-3 maps to S0-S77)
- Temporal stability experiments
- Identity persistence tracking

### S7 ARMADA
Link: `../experiments/temporal_stability/S7_ARMADA/`

Source of all experimental data:
- Probe configurations
- Model fleet definitions
- Result JSON files

---

## Contributing

### How to Add New Hypotheses

1. Add to this MANIFEST.md under "Core Hypotheses"
2. Define testable predictions
3. Specify experimental method
4. Update roadmap if new experiments needed

### How to Add New Research Questions

1. Categorize as Immediate/Medium-term/Long-term
2. Add to appropriate table with ID, question, method
3. Link to relevant experiments or data sources

### How to Update Findings

1. Run extraction: `py scripts/run_extraction.py`
2. Update distillations: `py scripts/update_distillations.py`
3. Review and edit generated documents
4. Update this manifest with confirmed findings

---

**Last Updated**: November 29, 2025

*"The unexamined AI is not worth deploying."*
