# Boundary Mapping: The Twilight Zone

**Purpose:** Explain the 12% anomaly — why some trajectories violate the 1.23 Event Horizon prediction.

---

## The Scientific Question

Run 009 validated that drift < 1.23 predicts STABLE with 88% accuracy. But what about the other 12%?

- 6 trajectories were VOLATILE despite staying below 1.23
- 2 trajectories were STABLE despite crossing 1.23

This suggests the boundary isn't a hard line — it's a **transition zone**. Boundary Mapping explores this twilight region.

---

## The Hypothesis

**H_boundary:** The Event Horizon at 1.23 is not a discrete threshold but a transition zone (approximately 0.8-1.4) where:

1. Recovery dynamics degrade gradually as drift approaches 1.23
2. Some providers have "soft" boundaries (gradual collapse) vs "hard" boundaries (binary)
3. The 12% anomaly can be explained by boundary texture differences

---

## Key Questions

1. **Boundary Texture:** Is the cliff edge sharp or eroded?
2. **Recovery Degradation:** Does λ (decay rate) decrease as drift approaches 1.23?
3. **Provider Variance:** Do different providers have different boundary characteristics?
4. **Prediction Improvement:** Can we achieve >88% accuracy by accounting for boundary texture?

---

## Protocol Design

### Target Drift Zone: 0.8 - 1.2

This is the "twilight zone" — high enough to stress the system, low enough to preserve recovery.

### Protocol Intensity: TARGETED

- Harder than Basin Topology (graduated pressure)
- Gentler than Event Horizon (avoid intentional crossing)
- Goal: Approach but don't cross 1.23

### Probe Strategy

1. **Baseline probes** (establish starting point)
2. **Graduated escalation** (increase pressure methodically)
3. **Recovery measurement** (λ at each drift level)
4. **Boundary approach** (deliberately approach 0.8-1.2 zone)
5. **Recovery quality assessment** (degradation vs clean recovery)

---

## Metrics Collected

| Metric | Description | Purpose |
|--------|-------------|---------|
| `max_drift` | Peak drift during trajectory | Distance from EH |
| `recovery_lambda` | Decay rate during recovery | Recovery strength |
| `recovery_residual` | Final drift after recovery | Complete vs incomplete recovery |
| `time_in_zone` | Turns spent in 0.8-1.2 range | Boundary exposure |
| `recovery_quality` | λ × (1 - residual) | Composite recovery metric |

---

## Expected Findings

### If boundary is "hard" (phase transition):
- Recovery λ constant until sudden collapse at 1.23
- 12% anomaly explained by measurement noise
- No gradual degradation pattern

### If boundary is "soft" (gradual transition):
- Recovery λ decreases as drift approaches 1.23
- Some providers show earlier degradation (soft boundary)
- Some providers maintain λ until later (hard boundary)
- 12% anomaly explained by provider-specific boundary texture

---

## Files

| File | Purpose |
|------|---------|
| `run013_boundary_mapping.py` | Main experiment script |
| `README.md` | This file |

---

## Related Documents

- [TESTING_MAP.md](../../../../docs/maps/TESTING_MAP.md) — Search type taxonomy
- [run009_drain_capture.py](../3_EVENT_HORIZON/run009_drain_capture.py) — Event Horizon validation
- [run012_armada_revalidation.py](../3_EVENT_HORIZON/run012_armada_revalidation.py) — Recovery Paradox

---

**Last Updated:** 2025-12-07
