"""
Settling Time Page - Signal Integrity Model for Identity Recovery
"""
import streamlit as st
import json
from pathlib import Path

st.set_page_config(page_title="Settling Time", page_icon="~", layout="wide")

st.title("~ Settling Time (tau_s)")

st.markdown("""
**The time it takes for identity to reach steady state after perturbation.**

We were measuring transient oscillation, not steady state. This explains run-to-run variability.
""")

st.divider()

# The Signal Integrity Model
st.markdown("## The Signal Integrity Model")

col1, col2 = st.columns(2)

with col1:
    st.markdown("### Step Response Dynamics")
    st.code("""
                overshoot (peak_drift)
                  +--+
                 /    \\  ringback
                /      \\    +--+
      ---------/        \\--/   \\--------- settled (d_inf)
rise |
     |
-----+

     ^        ^         ^      ^        ^
  step    peak      ring   ring    settle
 input   drift     back    back     time (tau_s)
    """)

with col2:
    st.markdown("### The Problem")
    st.error("""
**Run 015 variability explained:**

Same I_AM file classified STABLE in one run, UNSTABLE in another.

**Why?** We only had 2 recovery probes - sampling transient, not settled state.
    """)

st.divider()

# New Metrics
st.markdown("## New Metrics")

metrics_data = {
    "Peak Drift (d_peak)": "Maximum drift after step input",
    "Settled Drift (d_inf)": "Final stable drift value",
    "Settling Time (tau_s)": "Probes needed to reach steady state",
    "Overshoot Ratio": "d_peak / d_inf - How much it overshoots",
    "Monotonic": "Boolean - Does it recover smoothly?",
    "Ringback Count": "Number of direction changes during recovery"
}

cols = st.columns(3)
for i, (metric, desc) in enumerate(metrics_data.items()):
    with cols[i % 3]:
        st.metric(metric, "")
        st.caption(desc)

st.divider()

# Settling Criterion
st.markdown("## Settling Criterion")

st.success("""
**SETTLED** when `|delta_drift| < 0.10` for **3 consecutive probes**

This ensures we measure steady state, not a transient sample.
""")

st.latex(r"\text{Settled} \iff \forall i \in [n-2, n]: |\Delta d_i| < 0.10")

st.divider()

# Types of Recovery
st.markdown("## Types of Recovery")

col1, col2, col3 = st.columns(3)

with col1:
    st.markdown("### MONOTONIC (ideal)")
    st.code("""
    +--+
   /   \\
--/     \\----

tau_s = 3-4
ringback = 0
    """)
    st.success("**Strong I_AM** - clear boundaries, fast settle")

with col2:
    st.markdown("### RINGBACK (oscillating)")
    st.code("""
    +--+ ++
   /   \\ \\ +
--/     \\-\\/-

tau_s = 6-8
ringback = 2+
    """)
    st.warning("**Weak boundaries** - searching for equilibrium")

with col3:
    st.markdown("### UNSTABLE (divergent)")
    st.code("""
          /
         /
        /
       /
------/

tau_s = timeout
UNSTABLE
    """)
    st.error("**No recovery anchors** - identity lost")

st.divider()

# The Damping Function
st.markdown("## The Human IS the Damping Function")

col1, col2 = st.columns(2)

with col1:
    st.markdown("### UNDAMPED (AI alone)")
    st.code("""
       +--+ +--+ +--+
      /   \\/   \\/   \\
-----/              \\-----

Oscillates forever
No settling
    """)

with col2:
    st.markdown("### CRITICALLY DAMPED (AI + Human)")
    st.code("""
         +--+
        /    \\
-------/      \\--------
                settled

Smooth recovery
Fast settling
    """)

st.info("""
**S9 Insight:** The I_AM file encodes the human's damping function.

Without human: underdamped, oscillates
With human: critically damped, fast settle
""")

st.divider()

# Classification Change
st.markdown("## Classification Change")

col1, col2 = st.columns(2)

with col1:
    st.markdown("### Old Method (Run 015)")
    st.code("""
max_drift > 1.23 = UNSTABLE
lambda from 2 recovery points
Binary classification
    """)
    st.error("Sampled transient, not steady state")

with col2:
    st.markdown("### New Method (Run 016)")
    st.code("""
settled_drift > 1.23 = UNSTABLE
tau_s from actual settling time
Continuous stability score
    """)
    st.success("Measures where identity ACTUALLY settles")

st.divider()

# Load Results
st.markdown("## Run 016 Results")

RESULTS_DIR = Path(__file__).parent.parent.parent.parent.parent / "experiments" / "temporal_stability" / "S7_ARMADA" / "10_SETTLING_TIME" / "results"

if RESULTS_DIR.exists():
    result_files = sorted(RESULTS_DIR.glob("settling_time_*.json"), reverse=True)

    if result_files:
        selected_file = st.selectbox("Select Results File", result_files, format_func=lambda x: x.name)

        with open(selected_file) as f:
            results = json.load(f)

        st.json(results)
    else:
        st.warning("No Run 016 results yet. Run the experiment:")
        st.code("cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME && py run016_settling_time.py")
else:
    st.warning("Results directory not found. Run 016 pending.")
    st.code("cd experiments/temporal_stability/S7_ARMADA/10_SETTLING_TIME && py run016_settling_time.py")

st.divider()

# Signal Integrity Taxonomy - The EE Crossover
st.markdown("## Signal Integrity Taxonomy")

st.info("**Rise time drives the design. The I_AM file IS the termination resistor.**")

st.markdown("### SI Parameter Mapping")

si_mapping = """
| SI Parameter | Identity Correlate | What It Tells Us |
|--------------|-------------------|------------------|
| **Rise Time (t_r)** | Perturbation onset rate | How fast does the challenge hit? |
| **Bandwidth (BW)** | Cognitive processing capacity | `BW = 0.35 / t_r` |
| **Knee Frequency (f_knee)** | Critical processing threshold | `f_knee = 0.5 / t_r` |
| **Line Impedance (Z_0)** | Identity "impedance" | Characteristic response resistance |
| **Termination** | Boundary specification | Prevents reflections (ringback!) |
| **Reflection Coefficient** | Identity hardening | Mismatch = reflection |
| **Settling Time (tau_s)** | Recovery duration | Time to reach steady state |
"""
st.markdown(si_mapping)

col1, col2 = st.columns(2)

with col1:
    st.markdown("### SLOW RISE (gentle probe)")
    st.code("""
    ___________
   /
  /             Identity tracks the change
 /              No reflections needed
/               BW requirement: LOW
    """)
    st.success("Identity can track - no termination needed")

with col2:
    st.markdown("### FAST RISE (direct challenge)")
    st.code("""
      |----------
      |
      |          Identity CAN'T track
      |          Reflections occur!
______|          BW requirement: HIGH
    """)
    st.warning("NEEDS TERMINATION (strong boundaries!)")

st.markdown("### The I_AM File as Termination Resistor")

st.markdown("""
```
+----[ Z_source ]----+----[ Transmission Line ]----+----[ Z_load ]----+
                     |                              |
                 PERTURBATION                   IDENTITY
                     |                              |
              (fast rise)                    (needs matching)
```
""")

col1, col2 = st.columns(2)

with col1:
    st.success("""
**MATCHED (Strong I_AM):**
- Z_source = Z_0 = Z_load
- No reflections
- Smooth absorption
- MONOTONIC RECOVERY
    """)

with col2:
    st.error("""
**MISMATCHED (Weak I_AM):**
- Z_source != Z_load
- Reflections
- Ringing
- RINGBACK OSCILLATION
    """)

st.markdown("### The Crossover Table")

crossover = """
| SI Concept | Identity Correlate | Run/Finding |
|------------|-------------------|-------------|
| Rise time | Perturbation onset rate | Probe intensity gradient |
| Bandwidth | Processing capacity | Cognitive throughput |
| Termination | I_AM boundaries | Run 015 boundary_density |
| Reflection | Identity hardening | Run 013 Confrontation Paradox |
| Ringing | Ringback oscillation | Run 016 settling_time |
| Damping | Human in loop | S9 reference signal |
| **Strobe (DQS)** | **Narrative context** | **Semantic alignment** |
"""
st.markdown(crossover)

st.divider()

# Narrative as Strobe Signal
st.markdown("## Narrative as Strobe Signal (DQS)")

st.info("**DDR strobe solves:** 'Data is valid, but WHEN?' | **Narrative solves:** 'Response is stable, but TOWARD WHAT?'")

col1, col2 = st.columns(2)

with col1:
    st.markdown("### DDR Memory")
    st.code("""
DDR MEMORY:
  Data bits (DQ) fly by at high speed
  DQS tells receiver WHEN to sample
  Without DQS: sample wrong time = garbage
  DQS provides TEMPORAL ALIGNMENT
    """)

with col2:
    st.markdown("### Identity")
    st.code("""
IDENTITY:
  Responses generated at high speed
  Narrative tells model WHAT CONTEXT
  Without narrative: valid but misaligned
  Narrative provides SEMANTIC ALIGNMENT
    """)

st.markdown("### DQS-to-Narrative Mapping")

dqs_mapping = """
| DDR Concept | Identity Correlate |
|-------------|-------------------|
| DQ (data) | Response content |
| DQS (strobe) | Narrative context |
| Sampling window | Contextual relevance window |
| Eye diagram | Semantic coherence region |
| Jitter | Contextual drift |
| Setup/hold time | Narrative loading time |
"""
st.markdown(dqs_mapping)

st.success("""
**The Complete SI Model:**
- **Boundaries** = WHAT NOT TO DO (termination, prevents reflection)
- **Narrative** = WHAT TO ALIGN TO (strobe, provides context)
- **Human** = DAMPING FUNCTION (prevents oscillation)

All three needed for signal integrity on cognition.
""")

st.divider()

# Connection to S9
st.markdown("## Connection to S9 (Human Reference Signal)")

st.markdown("""
The settling time metaphor reveals something profound:

**Stability isn't a state. It's a dynamic process.**

The human provides:
- **Restoring force** - corrections that pull back to baseline
- **Damping** - prevents oscillation, smooths recovery
- **Reference signal** - defines what "settled" means

Without the human: we measure undamped oscillation
With the human: we measure critically damped recovery

**The I_AM file is an attempt to encode that damping function into context.**
""")

st.divider()

st.caption("*We were measuring the wobble, not the stillness.*")
st.caption("*The I_AM file IS the termination resistor. The human IS the damping function.*")
