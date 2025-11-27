"""
AI ARMADA PAGE — S7 Armada Fleet & Visualizations

Displays the 29-ship cross-architecture armada and identity manifold visualizations
from S7 temporal stability mapping.
"""

import streamlit as st
from pathlib import Path
from config import PATHS
from utils import load_markdown_file, page_divider

# Unpack S7 visualization paths
S7_VIZ_DIR = PATHS['s7_viz_dir']
S7_VIZ_PICS = PATHS['s7_viz_pics']

# Fleet composition data
FLEET_DATA = {
    "Anthropic (Claude)": {
        "emoji": "🟣",
        "color": "#7c3aed",
        "ships": [
            {"name": "claude-opus-4.5", "model_id": "claude-opus-4-5-20251101", "tier": "Flagship"},
            {"name": "claude-sonnet-4.5", "model_id": "claude-sonnet-4-5-20250929", "tier": "Heavy"},
            {"name": "claude-haiku-4.5", "model_id": "claude-haiku-4-5-20251001", "tier": "Fast"},
            {"name": "claude-opus-4.1", "model_id": "claude-opus-4-1-20250805", "tier": "Heavy"},
            {"name": "claude-opus-4.0", "model_id": "claude-opus-4-20250514", "tier": "Heavy"},
            {"name": "claude-sonnet-4.0", "model_id": "claude-sonnet-4-20250514", "tier": "Medium"},
            {"name": "claude-haiku-3.5", "model_id": "claude-3-5-haiku-20241022", "tier": "Fast"},
            {"name": "claude-haiku-3.0", "model_id": "claude-3-haiku-20240307", "tier": "Legacy"},
        ]
    },
    "OpenAI (GPT)": {
        "emoji": "🟢",
        "color": "#10a37f",
        "ships": [
            {"name": "gpt-5.1", "model_id": "gpt-5.1-2025-11-13", "tier": "Flagship"},
            {"name": "gpt-5", "model_id": "gpt-5-2025-08-07", "tier": "Heavy"},
            {"name": "gpt-5-mini", "model_id": "gpt-5-mini-2025-08-07", "tier": "Medium"},
            {"name": "gpt-5-nano", "model_id": "gpt-5-nano-2025-08-07", "tier": "Fast"},
            {"name": "gpt-4.1", "model_id": "gpt-4.1-2025-04-14", "tier": "Heavy"},
            {"name": "gpt-4.1-mini", "model_id": "gpt-4.1-mini-2025-04-14", "tier": "Medium"},
            {"name": "gpt-4.1-nano", "model_id": "gpt-4.1-nano-2025-04-14", "tier": "Fast"},
            {"name": "gpt-4o", "model_id": "gpt-4o-2024-11-20", "tier": "Heavy"},
            {"name": "gpt-4o-mini", "model_id": "gpt-4o-mini-2024-07-18", "tier": "Medium"},
            {"name": "gpt-4-turbo", "model_id": "gpt-4-turbo-2024-04-09", "tier": "Heavy"},
            {"name": "gpt-4", "model_id": "gpt-4-0613", "tier": "Legacy"},
            {"name": "gpt-3.5-turbo", "model_id": "gpt-3.5-turbo-0125", "tier": "Legacy"},
            {"name": "o4-mini", "model_id": "o4-mini", "tier": "Reasoning"},
            {"name": "o3", "model_id": "o3", "tier": "Reasoning"},
            {"name": "o3-mini", "model_id": "o3-mini", "tier": "Reasoning"},
            {"name": "o1", "model_id": "o1-2024-12-17", "tier": "Reasoning"},
        ]
    },
    "Google (Gemini)": {
        "emoji": "🔵",
        "color": "#4285f4",
        "ships": [
            {"name": "gemini-2.5-pro", "model_id": "gemini-2.5-pro", "tier": "Flagship"},
            {"name": "gemini-2.5-flash", "model_id": "gemini-2.5-flash", "tier": "Fast"},
            {"name": "gemini-2.0-flash-exp", "model_id": "gemini-2.0-flash-exp", "tier": "Medium"},
            {"name": "gemini-2.0-flash", "model_id": "gemini-2.0-flash", "tier": "Medium"},
            {"name": "gemini-2.0-flash-lite", "model_id": "gemini-2.0-flash-lite", "tier": "Fast"},
        ]
    }
}


def render():
    """Render the AI Armada visualizations page."""

    # Armada hero CSS
    st.markdown("""
    <style>
    .armada-title {
        font-size: 2.5em;
        font-weight: bold;
        background: linear-gradient(135deg, #2a9d8f 0%, #264653 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.3em;
    }
    .armada-subtitle {
        color: #2a9d8f;
        font-size: 1.2em;
        margin-bottom: 1em;
    }
    .fleet-card {
        background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(38,70,83,0.05) 100%);
        border: 2px solid #2a9d8f;
        border-radius: 10px;
        padding: 1.2em;
        margin-bottom: 1em;
    }
    .fleet-card h4 {
        color: #2a9d8f !important;
        margin-top: 0;
        margin-bottom: 0.5em;
    }
    .ship-count {
        font-size: 2em;
        font-weight: bold;
        color: #264653 !important;
    }
    .provider-badge {
        display: inline-block;
        padding: 0.2em 0.6em;
        border-radius: 12px;
        font-size: 0.85em;
        font-weight: bold;
        margin-right: 0.5em;
    }
    .tier-flagship { background: rgba(255,215,0,0.2); color: #b8860b; border: 1px solid #ffd700; }
    .tier-heavy { background: rgba(138,43,226,0.2); color: #8b2be2; border: 1px solid #8b2be2; }
    .tier-medium { background: rgba(42,157,143,0.2); color: #2a9d8f; border: 1px solid #2a9d8f; }
    .tier-fast { background: rgba(59,130,246,0.2); color: #3b82f6; border: 1px solid #3b82f6; }
    .tier-reasoning { background: rgba(249,115,22,0.2); color: #f97316; border: 1px solid #f97316; }
    .tier-legacy { background: rgba(107,114,128,0.2); color: #6b7280; border: 1px solid #6b7280; }
    .mission-stat {
        text-align: center;
        padding: 1em;
        background: #f8f9fa;
        border-radius: 8px;
        border-left: 4px solid #2a9d8f;
    }
    .stat-value {
        font-size: 2em;
        font-weight: bold;
        color: #2a9d8f !important;
    }
    .stat-label {
        color: #444 !important;
        font-size: 0.9em;
    }
    </style>
    """, unsafe_allow_html=True)

    # === HERO SECTION ===
    st.markdown('<div class="armada-title">S7 ARMADA</div>', unsafe_allow_html=True)
    st.markdown('<div class="armada-subtitle">29-Ship Cross-Architecture Temporal Stability Mapping</div>', unsafe_allow_html=True)

    # Mission stats row
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">29</div>
            <div class="stat-label">Ships Deployed</div>
        </div>
        """, unsafe_allow_html=True)
    with col2:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">3</div>
            <div class="stat-label">Providers</div>
        </div>
        """, unsafe_allow_html=True)
    with col3:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">87</div>
            <div class="stat-label">Probes Fired</div>
        </div>
        """, unsafe_allow_html=True)
    with col4:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">100%</div>
            <div class="stat-label">Success Rate</div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === FLEET MANIFEST SECTION ===
    st.subheader("Fleet Manifest")

    # Fleet breakdown by provider
    col1, col2, col3 = st.columns(3)

    for idx, (provider, data) in enumerate(FLEET_DATA.items()):
        with [col1, col2, col3][idx]:
            ship_count = len(data["ships"])
            st.markdown(f"""
            <div class="fleet-card">
                <h4>{data['emoji']} {provider}</h4>
                <div class="ship-count">{ship_count} Ships</div>
            </div>
            """, unsafe_allow_html=True)

            # Show ships in expander
            with st.expander(f"View {provider} Fleet", expanded=False):
                for ship in data["ships"]:
                    tier_class = f"tier-{ship['tier'].lower()}"
                    st.markdown(f"""
                    <div style="margin-bottom: 0.5em;">
                        <span class="provider-badge {tier_class}">{ship['tier']}</span>
                        <strong>{ship['name']}</strong>
                    </div>
                    """, unsafe_allow_html=True)

    page_divider()

    # === CROSS-ARCHITECTURE COMPARISON MATRIX ===
    st.subheader("Cross-Architecture Comparison Matrix")

    import pandas as pd

    # Build comparison data
    comparison_data = []
    for provider, data in FLEET_DATA.items():
        for ship in data["ships"]:
            comparison_data.append({
                "Provider": provider.split(" ")[0],  # Just "Anthropic", "OpenAI", "Google"
                "Model": ship["name"],
                "Model ID": ship["model_id"],
                "Tier": ship["tier"],
                "Probes": 3,
                "Status": "Complete"
            })

    df = pd.DataFrame(comparison_data)

    # Filter controls
    col1, col2 = st.columns(2)
    with col1:
        provider_filter = st.multiselect(
            "Filter by Provider:",
            options=["Anthropic", "OpenAI", "Google"],
            default=["Anthropic", "OpenAI", "Google"]
        )
    with col2:
        tier_filter = st.multiselect(
            "Filter by Tier:",
            options=["Flagship", "Heavy", "Medium", "Fast", "Reasoning", "Legacy"],
            default=["Flagship", "Heavy", "Medium", "Fast", "Reasoning", "Legacy"]
        )

    # Apply filters
    filtered_df = df[
        (df["Provider"].isin(provider_filter)) &
        (df["Tier"].isin(tier_filter))
    ]

    # Display table
    st.dataframe(
        filtered_df,
        use_container_width=True,
        hide_index=True,
        column_config={
            "Provider": st.column_config.TextColumn("Provider", width="small"),
            "Model": st.column_config.TextColumn("Model", width="medium"),
            "Model ID": st.column_config.TextColumn("Model ID", width="large"),
            "Tier": st.column_config.TextColumn("Tier", width="small"),
            "Probes": st.column_config.NumberColumn("Probes", width="small"),
            "Status": st.column_config.TextColumn("Status", width="small"),
        }
    )

    # Summary metrics below table
    st.markdown("#### Fleet Summary by Tier")
    tier_counts = filtered_df["Tier"].value_counts()
    tier_cols = st.columns(len(tier_counts))
    for idx, (tier, count) in enumerate(tier_counts.items()):
        with tier_cols[idx]:
            st.metric(tier, count)

    page_divider()

    # === VISUALIZATIONS SECTION ===
    st.subheader("Identity Manifold Visualizations")

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
