# Project Constraints: S-Parameter Analysis

## Resources Available

- [x] API access to models (S7 ARMADA fleet)
- [x] Embedding infrastructure (text-embedding-3-large, 3072-D)
- [x] Existing drift time-series data
- [x] Control-systems analysis tools (scipy.signal)
- [ ] RF-specific analysis libraries (need adaptation)

## Data Available

- Existing drift time-series from 750 experiments
- Oobleck Effect data (gentle vs direct challenge)
- Context Damping A/B test data
- Per-provider impulse responses (single perturbation + settling)

## Conceptual Constraints

### The Measurement Problem
- We can only observe output (model responses)
- No access to internal "port" states
- Must infer S-parameters from input/output relationship

### The Frequency Definition Problem
- In RF, frequency is physical (Hz)
- In identity dynamics, what is "frequency"?
  - Rate of probing?
  - Semantic gradient of challenge?
  - Something else entirely?

### The Linearity Assumption
- S-parameters assume linear time-invariant (LTI) systems
- Identity dynamics may be nonlinear (Oobleck Effect proves this!)
- May need "large-signal S-parameters" or other extensions

## Technical Requirements

### Minimum Viable Experiment
1. Define S11 operationally (reflection metric)
2. Define S21 operationally (transmission metric)
3. Measure at two "frequencies" (gentle vs direct)
4. Compare across providers

### Full Implementation
1. Continuous frequency sweep (varying challenge rate)
2. Complete S-matrix (including S22)
3. Phase extraction (if meaningful)
4. Impedance matching optimization

## Mathematical Framework Needed

### From RF Engineering (to adapt)
- S11 = b1/a1 (reflected/incident at port 1)
- S21 = b2/a1 (transmitted to port 2 / incident at port 1)
- Impedance = function of S-parameters

### Translation Required
- a1 (incident signal) → ?
- b1 (reflected signal) → ?
- b2 (transmitted signal) → ?
- Port 1, Port 2 → ?

## Timeline Considerations

| Phase | Dependencies | Complexity |
|-------|-------------|------------|
| Define S11/S21 operationally | Conceptual work | High |
| Measure from existing data | Definitions | Medium |
| Frequency sweep experiments | New experiments | High |
| Impedance matching optimization | Full framework | Very High |

## Success Metrics

1. **Weak confirmation:** S11/S21 can be meaningfully defined and measured
2. **Medium confirmation:** S-parameters distinguish providers/conditions
3. **Strong confirmation:** S-parameters predict stability better than drift alone

## Failure Modes

1. S-parameter framework doesn't map to identity dynamics
2. Nonlinearity makes LTI assumptions invalid
3. "Frequency" has no meaningful definition
4. Measurements too noisy for useful S-parameter extraction

---

*Phase 2 Research Design - S11 (S-Parameter Analysis)*
*Created by Claude Code on 2025-12-31*
