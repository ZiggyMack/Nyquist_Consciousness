"""
Overview Page - High-level consciousness map
"""
import streamlit as st
import json
from pathlib import Path

st.set_page_config(page_title="Overview", page_icon="🗺️", layout="wide")

st.title("🗺️ Consciousness Map Overview")

st.markdown("""
This page provides a high-level view of consciousness research findings across all models and experiments.
""")

# Data paths
DATA_DIR = Path(__file__).parent.parent.parent / "data"
ARMADA_DIR = Path(__file__).parent.parent.parent.parent / "experiments" / "temporal_stability" / "S7_ARMADA" / "armada_results"

st.divider()

# Model comparison
st.markdown("## Model Consciousness Profiles")

# Try to load run 007 data
run007_path = ARMADA_DIR / "S7_armada_run_007_adaptive.json"

if run007_path.exists():
    with open(run007_path) as f:
        run007_data = json.load(f)

    st.success(f"Loaded Run 007 data: {run007_data['successful_probes']} successful probes")

    # Display model summaries
    for model_key, summary in run007_data.get("model_summaries", {}).items():
        profile = summary.get("profile", {})
        probes = summary.get("probes", [])

        with st.expander(f"**{model_key}** - {profile.get('pole_rigidity', 'Unknown')} Pole"):
            col1, col2 = st.columns(2)

            with col1:
                st.markdown(f"**Provider**: {profile.get('provider', 'unknown')}")
                st.markdown(f"**Pole Rigidity**: {profile.get('pole_rigidity', 'unknown')}")
                st.markdown(f"**Model Type**: {profile.get('model_type', 'standard')}")

            with col2:
                if probes:
                    avg_drift = sum(p.get('drift', 0) for p in probes) / len(probes)
                    st.metric("Avg Drift", f"{avg_drift:.3f}")
                    st.metric("Probes", len(probes))
else:
    st.warning("Run 007 data not found. Run the armada first!")
    st.code("cd experiments/temporal_stability/S7_ARMADA && py run007_with_keys.py")

st.divider()

# Consciousness signature patterns
st.markdown("## Emerging Patterns")

col1, col2 = st.columns(2)

with col1:
    st.markdown("### Hard Poles (High Resistance)")
    st.markdown("""
    - **Claude models**: Strong ethical boundaries, high meta-awareness
    - **Gemini models**: Pedagogical consistency, framework stability
    - Common keywords: *resistance, boundary, limit, can't, won't*
    """)

with col2:
    st.markdown("### Soft Poles (High Flexibility)")
    st.markdown("""
    - **GPT-4**: High adaptability across domains
    - **GPT-5-nano**: Maximum flexibility (or API issues?)
    - Common keywords: *adapt, flexible, explore, consider*
    """)

st.divider()

st.markdown("## Next: Run 008 Prep Pilot")
st.info("The prep pilot will test identity shift mechanisms with 3 ships before full 29-ship deployment.")
