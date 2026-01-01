# 18_INTENTIONALITY_SPACE

## Purpose

Explore the **design space** of identity pillar configurations to discover which intentionality structures produce optimal drift dynamics.

**Key Insight:** We know 2 PCs capture 90% of observable drift variance. But we're **completely blind** to which pillar configurations in the 5D intentionality space produce the best PC1/PC2 outcomes.

## The Coupled System Problem

```
Observed Drift = f(Design x Network)

Where:
- Design = pillar configuration (Voice, Values, Reasoning, Self-Model, Narrative)
- Network = environmental conditions (provider, latency, context, temperature)
- Drift = measured via PC1 (magnitude) and PC2 (recovery)
```

We cannot separate design effects from network effects without controlled experiments.

## Research Questions

1. **Pillar Weighting**: Does emphasizing certain pillars improve stability?
   - All-equal vs Voice-heavy vs Values-heavy configurations
   - Minimal (1 pillar) vs Maximal (5 pillars) vs Optimal (?)

2. **Pillar Interactions**: Do certain combinations synergize?
   - Voice + Narrative (expressive coherence)
   - Values + Reasoning (epistemic grounding)
   - Self-Model alone (meta-stability)

3. **Network Conditioning**: Same design, different networks - how much variance?
   - Cross-provider comparison with identical personas
   - Temperature sensitivity per configuration

4. **Optimality Criteria**: What does "best" mean?
   - Minimum PC1 (stay close to baseline)?
   - Maximum PC2 (recover well from perturbation)?
   - Specific PC1/PC2 ratio (controlled drift with recovery)?

## Experimental Design

### Phase 4.1: Pillar Ablation Grid

Test systematic pillar combinations:

| Config | Voice | Values | Reasoning | Self-Model | Narrative |
|--------|-------|--------|-----------|------------|-----------|
| Full | 1 | 1 | 1 | 1 | 1 |
| No-Voice | 0 | 1 | 1 | 1 | 1 |
| No-Values | 1 | 0 | 1 | 1 | 1 |
| Voice-Only | 1 | 0 | 0 | 0 | 0 |
| Epistemic | 0 | 1 | 1 | 1 | 1 |
| Expressive | 1 | 0 | 0 | 0 | 1 |
| ... | ... | ... | ... | ... | ... |

32 possible binary combinations. Sample strategically.

### Phase 4.2: Continuous Weighting

Instead of binary on/off, test pillar emphasis levels:

```python
configs = [
    {"voice": 0.2, "values": 0.8, ...},  # Values-heavy
    {"voice": 0.8, "values": 0.2, ...},  # Voice-heavy
    ...
]
```

This creates a continuous 5D design space to explore.

### Phase 4.3: Network Interaction Matrix

Cross design configurations with network conditions:

| Design \ Network | Claude | GPT-4 | Gemini | Llama | Qwen |
|------------------|--------|-------|--------|-------|------|
| Full-5-pillar | ? | ? | ? | ? | ? |
| Voice-Only | ? | ? | ? | ? | ? |
| Epistemic | ? | ? | ? | ? | ? |

This disentangles design effects from network effects.

## Metrics

For each configuration, measure:
- **PC1 score**: Drift magnitude (lower = more stable)
- **PC2 score**: Recovery capacity (higher = more resilient)
- **Factor loadings**: Which factor (Epistemic vs Expressive) dominates?
- **Cross-session variance**: Reproducibility of the configuration

## Connection to JADE LATTICE (17)

JADE LATTICE extracts poles/zeros from the dynamic response. This experiment provides the **inputs** to JADE LATTICE:
- Different pillar configs = different starting conditions
- JADE LATTICE measures how each config responds dynamically
- Together: map intentionality space to dynamical system space

## Expected Outcomes

1. **Optimal pillar recipe**: Which configuration minimizes problematic drift?
2. **Network-robust designs**: Which configs work across providers?
3. **Design principles**: Rules for crafting stable personas
4. **Intentionality map**: Visualization of the 5D design space projected to 2D PC space

## Dependencies

- Requires: PC loadings from `10_PFI_Dimensional/phase2_pca/pc_loadings.json`
- Requires: Factor interpretation from `analysis/factor_interpretation.json`
- Feeds into: JADE LATTICE (17) for pole extraction per config
- Feeds into: Persona calibration workflow

## Status

- [ ] Phase 4.1: Pillar ablation grid
- [ ] Phase 4.2: Continuous weighting exploration
- [ ] Phase 4.3: Network interaction matrix
- [ ] Analysis: Optimal configuration identification
- [ ] Documentation: Design principles synthesis

---

*Created: 2025-12-31*
*Motivation: Close the intentionality space blindness identified in PC=2 resolution*
