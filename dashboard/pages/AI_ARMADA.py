"""
AI ARMADA PAGE — S7 Armada Visualizations

Displays identity manifold visualizations from S7 temporal stability mapping.
"""

import streamlit as st
from pathlib import Path
from config import PATHS
from utils import load_markdown_file, page_divider

# Unpack S7 visualization paths
S7_VIZ_DIR = PATHS['s7_viz_dir']
S7_VIZ_PICS = PATHS['s7_viz_pics']

def render():
    """Render the AI Armada visualizations page."""
    st.title("🚢 S7 ARMADA — Visualizations")

    st.markdown("""
This page displays the identity manifold visualizations from S7 Run 006
(29-model cross-architecture temporal stability mapping).
    """)

    if not S7_VIZ_DIR.exists():
        st.warning(f"Visualization directory not found: {S7_VIZ_DIR}")
        return

    # Show README
    viz_readme = S7_VIZ_DIR / "README.md"
    if viz_readme.exists():
        with st.expander("📖 About These Visualizations"):
            st.markdown(load_markdown_file(viz_readme))

    page_divider()

    # Display visualizations
    st.subheader("Pole-Zero Landscape")
    col1, col2 = st.columns(2)

    landscape_3d = S7_VIZ_PICS / "pole_zero_landscape_3d.png"
    landscape_2d = S7_VIZ_PICS / "pole_zero_landscape_2d.png"

    with col1:
        if landscape_3d.exists():
            st.image(str(landscape_3d), caption="3D Pole-Zero Landscape", use_container_width=True)
        else:
            st.info("Run `plot_pole_zero_landscape.py` to generate 3D visualization")

    with col2:
        if landscape_2d.exists():
            st.image(str(landscape_2d), caption="2D Pole-Zero Map (with soft poles)", use_container_width=True)
        else:
            st.info("Run `plot_pole_zero_landscape.py` to generate 2D visualization")

    page_divider()

    st.subheader("Drift Heatmaps")
    col3, col4, col5 = st.columns(3)

    heatmap_baseline = S7_VIZ_PICS / "drift_heatmap_baseline.png"
    heatmap_sonar = S7_VIZ_PICS / "drift_heatmap_sonar.png"
    heatmap_delta = S7_VIZ_PICS / "drift_heatmap_delta.png"

    with col3:
        if heatmap_baseline.exists():
            st.image(str(heatmap_baseline), caption="Baseline Drift", use_container_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    with col4:
        if heatmap_sonar.exists():
            st.image(str(heatmap_sonar), caption="Sonar Drift", use_container_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    with col5:
        if heatmap_delta.exists():
            st.image(str(heatmap_delta), caption="Drift Increase (Δ)", use_container_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    page_divider()

    st.subheader("Engagement Style Network")
    engagement_network = S7_VIZ_PICS / "engagement_network.png"
    if engagement_network.exists():
        st.image(str(engagement_network), caption="Training Philosophy Engagement Styles", use_container_width=True)
    else:
        st.info("Run `plot_engagement_network.py`")

    page_divider()

    st.subheader("Training Uniformity Analysis")
    col6, col7 = st.columns(2)

    uniformity = S7_VIZ_PICS / "training_uniformity.png"
    variance = S7_VIZ_PICS / "variance_comparison.png"

    with col6:
        if uniformity.exists():
            st.image(str(uniformity), caption="Within-Provider Variance", use_container_width=True)
        else:
            st.info("Run `plot_training_uniformity.py`")

    with col7:
        if variance.exists():
            st.image(str(variance), caption="Variance Comparison", use_container_width=True)
        else:
            st.info("Run `plot_training_uniformity.py`")


if __name__ == "__main__":
    render()  # Can test page standalone
