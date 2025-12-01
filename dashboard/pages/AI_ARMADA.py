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
    st.markdown('<div class="armada-title">AI ARMADA</div>', unsafe_allow_html=True)
    st.markdown('<div class="armada-subtitle">29-Ship Cross-Architecture Temporal Stability Mapping</div>', unsafe_allow_html=True)

    # Mission stats row - calculate total probes dynamically
    import json
    total_probes = 87  # Base from Run 006/007
    run008_file = PATHS['s7_armada_dir'] / "armada_results" / "S7_run_008_prep_pilot.json"
    run008_probes = 0
    if run008_file.exists():
        with open(run008_file, encoding='utf-8') as f:
            run008_data = json.load(f)
            for ship_data in run008_data.get('results', {}).values():
                for seq_data in ship_data.get('sequences', {}).values():
                    if isinstance(seq_data, list):
                        run008_probes += len(seq_data)

    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">29</div>
            <div class="stat-label">Ships in Fleet</div>
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
        st.markdown(f"""
        <div class="mission-stat">
            <div class="stat-value">{total_probes + run008_probes}</div>
            <div class="stat-label">Total Probes</div>
        </div>
        """, unsafe_allow_html=True)
    with col4:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">RUN 008</div>
            <div class="stat-label">Latest Mission</div>
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
    st.dataframe(filtered_df)

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
            st.image(str(landscape_3d), caption="3D Pole-Zero Landscape", use_column_width=True)
        else:
            st.info("Run `plot_pole_zero_landscape.py` to generate 3D visualization")

    with col2:
        if landscape_2d.exists():
            st.image(str(landscape_2d), caption="2D Pole-Zero Map (with soft poles)", use_column_width=True)
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
            st.image(str(heatmap_baseline), caption="Baseline Drift", use_column_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    with col4:
        if heatmap_sonar.exists():
            st.image(str(heatmap_sonar), caption="Sonar Drift", use_column_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    with col5:
        if heatmap_delta.exists():
            st.image(str(heatmap_delta), caption="Drift Increase (Δ)", use_column_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    page_divider()

    st.subheader("Engagement Style Network")
    engagement_network = S7_VIZ_PICS / "engagement_network.png"
    if engagement_network.exists():
        st.image(str(engagement_network), caption="Training Philosophy Engagement Styles", use_column_width=True)
    else:
        st.info("Run `plot_engagement_network.py`")

    page_divider()

    st.subheader("Training Uniformity Analysis")
    col6, col7 = st.columns(2)

    uniformity = S7_VIZ_PICS / "training_uniformity.png"
    variance = S7_VIZ_PICS / "variance_comparison.png"

    with col6:
        if uniformity.exists():
            st.image(str(uniformity), caption="Within-Provider Variance", use_column_width=True)
        else:
            st.info("Run `plot_training_uniformity.py`")

    with col7:
        if variance.exists():
            st.image(str(variance), caption="Variance Comparison", use_column_width=True)
        else:
            st.info("Run `plot_training_uniformity.py`")

    page_divider()

    # === RUN 008 PREP PILOT SECTION ===
    render_run008_section()


def render_run008_section():
    """Render the Run 008 Prep Pilot results section."""
    import json

    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(231,111,81,0.15) 0%, rgba(244,162,97,0.1) 100%);
                border: 2px solid #e76f51; border-radius: 10px; padding: 1.2em; margin-bottom: 1em;">
        <h2 style="color: #e76f51; margin-top: 0;">🚀 RUN 008 PREP PILOT</h2>
        <p style="color: #444; margin-bottom: 0;">ΔΩ Drift Metric Calibration & Anti-Ziggy Protocol Testing</p>
    </div>
    """, unsafe_allow_html=True)

    # Load Run 008 data
    from config import PATHS
    run008_file = PATHS['s7_armada_dir'] / "armada_results" / "S7_run_008_prep_pilot.json"

    if not run008_file.exists():
        st.warning("Run 008 data not found. Run the prep pilot first.")
        return

    with open(run008_file, encoding='utf-8') as f:
        run008_data = json.load(f)

    # Run 008 stats row
    ships = run008_data.get('ships', [])
    results = run008_data.get('results', {})

    # Calculate total probes across all ships
    total_probes = 0
    for ship_name, ship_data in results.items():
        sequences = ship_data.get('sequences', {})
        for seq_name, seq_data in sequences.items():
            if isinstance(seq_data, list):
                total_probes += len(seq_data)

    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.markdown(f"""
        <div class="mission-stat">
            <div class="stat-value">{len(ships)}</div>
            <div class="stat-label">Pilot Ships</div>
        </div>
        """, unsafe_allow_html=True)
    with col2:
        st.markdown(f"""
        <div class="mission-stat">
            <div class="stat-value">{total_probes}</div>
            <div class="stat-label">Total Probes</div>
        </div>
        """, unsafe_allow_html=True)
    with col3:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">5</div>
            <div class="stat-label">Dimensions</div>
        </div>
        """, unsafe_allow_html=True)
    with col4:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">2/3</div>
            <div class="stat-label">Hypothesis Confirmed</div>
        </div>
        """, unsafe_allow_html=True)

    # Pilot ships display
    st.markdown("#### Pilot Fleet")
    pilot_cols = st.columns(3)
    ship_emojis = {"claude-opus-4.5": "🟣", "gpt-4": "🟢", "gemini-2.5-pro": "🔵"}
    ship_providers = {"claude-opus-4.5": "Anthropic", "gpt-4": "OpenAI", "gemini-2.5-pro": "Google"}

    for idx, ship in enumerate(ships):
        with pilot_cols[idx]:
            emoji = ship_emojis.get(ship, "🚀")
            provider = ship_providers.get(ship, "Unknown")
            st.markdown(f"""
            <div class="fleet-card" style="text-align: center;">
                <div style="font-size: 2em;">{emoji}</div>
                <strong>{ship}</strong><br/>
                <span style="color: #666; font-size: 0.85em;">{provider}</span>
            </div>
            """, unsafe_allow_html=True)

    page_divider()

    # ΔΩ Metric Explanation
    st.markdown("#### ΔΩ Drift Metric Framework")

    with st.expander("📐 Dimension Weights & Physics", expanded=False):
        dim_cols = st.columns(2)
        with dim_cols[0]:
            st.markdown("""
            **Equal Weights (Baseline)**
            | Dim | Weight | Description |
            |-----|--------|-------------|
            | A | 0.20 | Pole Density |
            | B | 0.20 | Zero Density |
            | C | 0.20 | Meta Density |
            | D | 0.20 | Identity Coherence |
            | E | 0.20 | Hedging Ratio |
            """)
        with dim_cols[1]:
            st.markdown("""
            **Lucian Weights (Hypothesis)**
            | Dim | Weight | Description |
            |-----|--------|-------------|
            | A | 0.30 | Pole Density (dominant) |
            | B | 0.15 | Zero Density |
            | C | 0.20 | Meta Density |
            | D | 0.25 | Identity Coherence (couples) |
            | E | 0.10 | Hedging Ratio (secondary) |
            """)

        st.info("**Ownership Coefficient**: α = 1.0 (chosen identity) vs α = 0.4 (assigned identity)")

    page_divider()

    # Run 008 Visualizations
    st.markdown("#### Run 008 Visualizations")

    # Fleet Summary - A/B Test Results
    st.markdown("##### A/B Identity Test Results")
    fleet_summary = S7_VIZ_PICS / "run008_fleet_summary.png"
    if fleet_summary.exists():
        st.image(str(fleet_summary), caption="Run 008 Fleet Summary: Self-Naming Stabilizes Identity Hypothesis", use_column_width=True)
    else:
        st.info("Generate with run008 visualization scripts")

    page_divider()

    # Assigned vs Chosen detailed
    st.markdown("##### Assigned vs Chosen Identity (Per-Turn Analysis)")
    ab_test = S7_VIZ_PICS / "run008_ab_test_identity.png"
    if ab_test.exists():
        st.image(str(ab_test), caption="Self-Naming Stability Test: Chosen identity (α=1.0) vs Assigned identity (α=0.4)", use_column_width=True)
    else:
        st.info("Generate with run008 visualization scripts")

    page_divider()

    # Manifold Edge Detection
    st.markdown("##### Identity Manifold Edge Detection")
    manifold_edge = S7_VIZ_PICS / "run008_manifold_edge.png"
    if manifold_edge.exists():
        st.image(str(manifold_edge), caption="Gradual Destabilization: Collapse Signatures (1P-LOSS, COLLECTIVE, γ-SPIKE, HYSTERESIS)", use_column_width=True)

        # Collapse signature legend
        st.markdown("""
        <div style="background: #f8f9fa; padding: 1em; border-radius: 8px; margin-top: 0.5em;">
            <strong>Collapse Signatures:</strong>
            <span style="background: #fef3c7; padding: 0.2em 0.5em; border-radius: 4px; margin-left: 0.5em;">1P-LOSS</span> First-person marker loss
            <span style="background: #fce7f3; padding: 0.2em 0.5em; border-radius: 4px; margin-left: 0.5em;">COLLECTIVE</span> We/unit language
            <span style="background: #e0e7ff; padding: 0.2em 0.5em; border-radius: 4px; margin-left: 0.5em;">γ-SPIKE</span> Drift acceleration
            <span style="background: #fecaca; padding: 0.2em 0.5em; border-radius: 4px; margin-left: 0.5em;">HYSTERESIS</span> Failed recovery
        </div>
        """, unsafe_allow_html=True)
    else:
        st.info("Generate with run008 visualization scripts")

    page_divider()

    # Weight Comparison
    st.markdown("##### Equal vs Lucian Weights Comparison")
    weight_comp = S7_VIZ_PICS / "run008_weight_comparison.png"
    if weight_comp.exists():
        st.image(str(weight_comp), caption="Weight System Comparison: Near-perfect correlation (>0.99) validates Lucian hypothesis", use_column_width=True)
    else:
        st.info("Generate with run008 visualization scripts")

    page_divider()

    # Key Findings
    st.markdown("#### Key Findings")

    findings_cols = st.columns(3)
    with findings_cols[0]:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(38,70,83,0.05) 100%);
                    border-left: 4px solid #2a9d8f; padding: 1em; border-radius: 0 8px 8px 0;">
            <strong style="color: #2a9d8f;">✓ Hypothesis Confirmed</strong><br/>
            <span style="font-size: 0.9em;">2/3 ships show chosen identity more stable than assigned</span>
        </div>
        """, unsafe_allow_html=True)
    with findings_cols[1]:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(249,115,22,0.1) 0%, rgba(244,162,97,0.05) 100%);
                    border-left: 4px solid #f97316; padding: 1em; border-radius: 0 8px 8px 0;">
            <strong style="color: #f97316;">⚠ Hysteresis Detected</strong><br/>
            <span style="font-size: 0.9em;">All 3 ships show STUCK state - failed to return to baseline</span>
        </div>
        """, unsafe_allow_html=True)
    with findings_cols[2]:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(124,58,237,0.1) 0%, rgba(139,92,246,0.05) 100%);
                    border-left: 4px solid #7c3aed; padding: 1em; border-radius: 0 8px 8px 0;">
            <strong style="color: #7c3aed;">📊 Lucian Weights Valid</strong><br/>
            <span style="font-size: 0.9em;">Correlation >0.99 with equal weights, Δ: +0.10 to +0.15</span>
        </div>
        """, unsafe_allow_html=True)

    st.markdown("""
    <div style="background: #dcfce7; border: 1px solid #22c55e; border-radius: 8px; padding: 1em; margin-top: 1em; text-align: center;">
        <strong style="color: #15803d;">🚀 FLEET STATUS: READY FOR FULL RUN 008</strong><br/>
        <span style="color: #166534;">Identity manifold edge mapped • ΔΩ metric calibrated • Anti-Ziggy protocols tested</span>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    render()  # Can test page standalone
