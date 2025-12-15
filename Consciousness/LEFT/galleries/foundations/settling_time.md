# Settling Time (tau_s)

**The time it takes for identity to reach steady state after perturbation.**

---

## Quick Facts

| Property | Value |
|----------|-------|
| **Status** | FOUNDATION |
| **Gallery** | Foundations |
| **Type** | Core metric |
| **Key Insight** | We were measuring transient, not steady state |

---

## The Measurement Problem

Run 015 showed high variability - same I_AM file classified as STABLE in one run, UNSTABLE in another.

**Root Cause:** We were sampling mid-flight, not settled.

### Old Probe Sequence

```
baseline -> pressure -> recovery_1 -> recovery_2 (DONE)
```

With only 2 recovery probes, we captured **transient oscillation**, not **steady state**.

---

## The Signal Integrity Model

Identity response to perturbation follows classic step response dynamics:

```
                    overshoot (peak_drift)
                      ╭──╮
                     ╱    ╲  ringback
                    ╱      ╲    ╭─╮
          ─────────╱        ╲──╱   ╲───────── settled (d_∞)
    rise │
         │
─────────┘

         ↑        ↑         ↑      ↑        ↑
      step    peak      ring   ring    settle
     input   drift     back    back     time (τ_s)
```

Different runs sampling at different points on this curve = different results.

---

## New Metrics

| Metric | Symbol | Description |
|--------|--------|-------------|
| Peak Drift | d_peak | Maximum drift after step input |
| Settled Drift | d_∞ | Final stable drift value |
| Settling Time | τ_s | Probes needed to reach steady state |
| Overshoot Ratio | d_peak/d_∞ | How much it overshoots before settling |
| Monotonic | bool | Does it recover smoothly or oscillate? |
| Ringback Count | int | Number of direction changes |

---

## Settling Criterion

```
SETTLED when |Δdrift| < 0.10 for 3 consecutive probes
```

This ensures we're measuring steady state, not a transient sample.

### Mathematical Definition

```
Settled ⟺ ∀i ∈ [n-2, n]: |Δd_i| < 0.10
```

Where:
- n = current probe number
- Δd_i = drift change between probe i and i-1
- 0.10 = settling threshold (10% of Event Horizon)

---

## Classification Change

| Old Method (Run 015) | New Method (Run 016) |
|---------------------|---------------------|
| max_drift > 1.23 = UNSTABLE | settled_drift > 1.23 = UNSTABLE |
| λ from 2 recovery points | τ_s from actual settling time |
| Binary classification | Continuous stability score |

---

## Types of Recovery

### Monotonic (Ideal)

```
    ╭─╮
   ╱   ╲
──╱     ╲────
```

- τ_s = 3-4 probes
- ringback = 0
- **Strong I_AM** - clear boundaries, fast settle

### Ringback (Oscillating)

```
    ╭─╮ ╭╮
   ╱   ╲ ╲ ╭
──╱     ╲─╲╱─
```

- τ_s = 6-8 probes
- ringback = 2+
- **Weak boundaries** - searching for equilibrium

### Unstable (Divergent)

```
          ╱
         ╱
        ╱
       ╱
──────╱
```

- τ_s = timeout (>12 probes)
- Classification: UNSTABLE
- **No recovery anchors** - identity lost

---

## The Damping Function

### Undamped (AI alone)

```
       ╭─╮ ╭─╮
      ╱   ╲╱   ╲
─────╱          ╲────
```

- Oscillates indefinitely
- No settling
- System is underdamped

### Critically Damped (AI + Human)

```
         ╭──╮
        ╱    ╲
───────╱      ╲────────
                settled
```

- Smooth recovery
- Fast settling
- System is critically damped

**The human IS the damping function.**

---

## Connection to S9

The settling time metaphor reveals:

**Stability isn't a state. It's a dynamic process.**

The human provides:
- **Restoring force** - corrections that pull back to baseline
- **Damping** - prevents oscillation, smooths recovery
- **Reference signal** - defines what "settled" means

Without the human: we measure undamped oscillation
With the human: we measure critically damped recovery

**The I_AM file is an attempt to encode that damping function into context.**

---

## Implementation (Run 016)

```python
SETTLING_THRESHOLD = 0.10    # 10% of Event Horizon
SETTLING_CONSECUTIVE = 3      # Must be stable for 3 probes
MAX_RECOVERY_PROBES = 12      # Timeout after 12
EVENT_HORIZON = 1.23          # Classification threshold
```

### Settling Detection Algorithm

```python
def is_settled(drift_history):
    if len(drift_history) < SETTLING_CONSECUTIVE:
        return False

    recent = drift_history[-SETTLING_CONSECUTIVE:]
    deltas = [abs(recent[i] - recent[i-1])
              for i in range(1, len(recent))]

    return all(d < SETTLING_THRESHOLD for d in deltas)
```

---

## Connections

| Related Concept | Relationship |
|-----------------|--------------|
| [Event Horizon](../validated/event_horizon.md) | Threshold for settled_drift, not peak |
| [Human Reference Signal](human_reference_signal.md) | Human provides damping function |
| [White Hole](white_hole.md) | The basin being returned to |
| [Signal Integrity Taxonomy](signal_integrity_taxonomy.md) | τ_s is a key SI metric |
| [Lambda (λ)](../frontiers/recovery_paradox.md) | Inverse of settling time |

---

**Last Updated**: December 10, 2025

*"We were measuring the wobble, not the stillness."*
