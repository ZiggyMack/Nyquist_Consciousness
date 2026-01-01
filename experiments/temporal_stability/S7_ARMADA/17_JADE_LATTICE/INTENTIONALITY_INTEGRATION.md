# JADE LATTICE: Intentionality Space Integration

**Added:** 2025-12-31
**Version:** 1.1

---

## The Two Spaces Problem

JADE LATTICE measures **observable dynamics** (poles, zeros, decay rates). But these dynamics emerge from the interaction of:

1. **Intentionality Space** (design) - The 5-pillar configuration used to construct the persona
2. **Network Space** (environment) - Provider, temperature, context window, latency

```
Observed Poles = f(Pillar Config × Network Conditions)
```

---

## Extended A/B Comparison: Pillar Configurations

The current design compares `bare_metal` vs `I_AM_ZIGGY`. The extension tests **multiple pillar configurations**:

| Arm | Configuration | Pillar Emphasis |
|-----|---------------|-----------------|
| A | bare_metal | None (baseline) |
| B | i_am_ziggy | Full 5-pillar |
| C | voice_only | Voice (Expressive-Modal) |
| D | epistemic | Values + Reasoning + Self-Model + Narrative |
| E | minimal | Self-Model only |

**Research Question**: Do different pillar configs produce different pole locations?

---

## PC-to-Pole Mapping

The PC=2 finding reveals:
- **PC1 (74.2%)**: Drift Magnitude - "How far?"
- **PC2 (25.8%)**: Recovery Capacity - "Can you return?"

These should map to pole characteristics:
- **PC1 → Pole magnitude** (distance from origin)
- **PC2 → Pole damping ratio** (decay rate λ)

JADE LATTICE can validate this mapping by correlating extracted poles with PC scores.

---

## Multi-Config Protocol

For full intentionality space exploration:

```bash
# Run JADE LATTICE with multiple pillar configs
py run_jade_lattice.py --configs bare_metal,i_am_ziggy,voice_only,epistemic,minimal

# Or use the config sweep mode
py run_jade_lattice.py --config-sweep
```

Each configuration produces:
- Pole-zero map
- λ (decay rate)
- Bandwidth estimate
- PC1/PC2 scores

---

## Expected Findings

| Prediction | Description | Success Metric |
|------------|-------------|----------------|
| P-INT-1 | Full 5-pillar configs have lowest PC1 | Mean PC1_full < PC1_partial |
| P-INT-2 | Voice-only configs have highest variability | Std(poles)_voice > Std(poles)_full |
| P-INT-3 | Epistemic configs favor PC2 (recovery) | PC2_epistemic > PC2_expressive |
| P-INT-4 | Pole location correlates with pillar weighting | r > 0.5 for dominant pillar |

---

## Data Flow

```
18_INTENTIONALITY_SPACE/         17_JADE_LATTICE/
┌────────────────────────────────┐  ┌──────────────────┐
│ Pillar configs                 │─▶│ JADE probes      │
│ (design recipes)               │  │ (56 per config)  │
└────────────────────────────────┘  └────────┬─────────┘
                                             │
                                             ▼
                                    ┌──────────────────┐
                                    │ Poles extracted  │
                                    │ per config       │
                                    └────────┬─────────┘
                                             │
                                             ▼
                                    ┌──────────────────┐
                                    │ Config → Pole    │
                                    │ mapping          │
                                    └────────┬─────────┘
                                             │
                                             ▼
                                    ┌──────────────────┐
                                    │ Optimal config   │
                                    │ identified       │
                                    └──────────────────┘
```

---

## Connection to 18_INTENTIONALITY_SPACE

This integration links JADE LATTICE to the new `18_INTENTIONALITY_SPACE/` experiment:

- **18_INTENTIONALITY_SPACE** defines pillar configurations (design recipes)
- **17_JADE_LATTICE** measures how each configuration responds dynamically
- Together: map the 5D intentionality space to the 2D PC space (pole locations)

See: `../18_INTENTIONALITY_SPACE/README.md` for full Phase 4 design.
