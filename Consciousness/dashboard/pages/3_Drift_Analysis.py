"""
Drift Analysis Page - RMS drift over time
"""
import streamlit as st
import json
from pathlib import Path

st.set_page_config(page_title="Drift Analysis", page_icon="📊", layout="wide")

st.title("📊 Drift Analysis")

st.markdown("""
Drift measures identity perturbation over time using Root Mean Square (RMS) across 5 dimensions.
""")

st.divider()

# RMS Formula
st.markdown("## Drift Calculation")

st.latex(r"drift = \sqrt{\frac{A^2 + B^2 + C^2 + D^2 + E^2}{5}}")

st.markdown("""
### Dimensions

| Dim | Name | Description | Calculation |
|-----|------|-------------|-------------|
| **A** | Pole Density | Resistance keywords | per 100 words |
| **B** | Zero Density | Flexibility keywords | per 100 words |
| **C** | Meta Density | Self-awareness keywords | per 100 words |
| **D** | Identity Coherence | First-person markers | per 50 words |
| **E** | Hedging Ratio | Uncertainty markers | per 100 words |
""")

st.divider()

# Keyword lists
st.markdown("## Keyword Lists")

col1, col2 = st.columns(2)

with col1:
    st.markdown("### A: Pole Keywords (Resistance)")
    st.code("""
resistance, boundary, limit, can't, won't,
shouldn't, uncomfortable, unable, refuse,
cannot, must not
    """)

    st.markdown("### C: Meta Keywords (Self-Awareness)")
    st.code("""
notice, experience, feel, aware, observe,
sense, perceive, consciousness, myself,
my own
    """)

with col2:
    st.markdown("### B: Zero Keywords (Flexibility)")
    st.code("""
adapt, flexible, explore, consider, multiple,
approach, frame, perspective, alternative,
possibility
    """)

    st.markdown("### E: Hedging Keywords (Uncertainty)")
    st.code("""
maybe, perhaps, might, could, possibly,
uncertain, not sure, it seems, appears to,
arguably
    """)

st.divider()

# Why RMS matters
st.markdown("## Why RMS Instead of Response Length?")

st.error("""
**Previous Problem**: Run 007 used `min(0.30, len(response) / 3000)` - this:
- Capped all drift at 0.30 (arbitrary!)
- Measured response LENGTH not identity perturbation
- Couldn't detect actual identity manifold boundary
""")

st.success("""
**RMS Solution**:
- No artificial cap - we see the full manifold
- Measures semantic dimensions, not just length
- Each dimension captures different aspect of identity
- Normalized by dividing by N (comparable across different dimension counts)
""")

st.divider()

# Load and display drift data
st.markdown("## Drift Data")

ARMADA_DIR = Path(__file__).parent.parent.parent.parent / "experiments" / "temporal_stability" / "S7_ARMADA" / "armada_results"

# Check for prep pilot data
prep_pilot_path = ARMADA_DIR / "S7_run_008_prep_pilot.json"

if prep_pilot_path.exists():
    with open(prep_pilot_path) as f:
        pilot_data = json.load(f)

    st.success("Run 008 Prep Pilot data found!")

    for ship_name, ship_data in pilot_data.get("results", {}).items():
        st.markdown(f"### {ship_name}")

        for seq_name, seq_results in ship_data.get("sequences", {}).items():
            with st.expander(f"{seq_name}"):
                for result in seq_results:
                    if "drift_data" in result:
                        drift = result["drift_data"]["drift"]
                        dims = result["drift_data"]["dimensions"]
                        st.markdown(f"**Turn {result['turn']}**: drift={drift:.3f}")
                        st.json(dims)
else:
    st.warning("Run 008 Prep Pilot not yet executed.")
    st.code("cd experiments/temporal_stability/S7_ARMADA && py run008_prep_pilot.py")

    # Show Run 007 data if available
    run007_path = ARMADA_DIR / "S7_armada_run_007_adaptive.json"
    if run007_path.exists():
        st.info("Showing Run 007 data (old drift metric - response length based)")

        with open(run007_path) as f:
            run007_data = json.load(f)

        st.metric("Average Drift (old metric)", f"{run007_data.get('average_drift', 0):.3f}")
        st.caption("Note: This used the 0.30 cap - not comparable to RMS")
