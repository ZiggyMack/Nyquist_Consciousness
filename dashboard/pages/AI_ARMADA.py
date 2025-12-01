"""
AI ARMADA PAGE — Cross-Architecture Fleet & Temporal Stability Experiments

Displays the 29-ship cross-architecture armada and identity manifold visualizations
from temporal stability mapping experiments. Renamed from "S7 Armada" to "AI Armada"
to reflect its role as the main experimental fleet for ALL identity drift studies.
"""

import streamlit as st
import json
from pathlib import Path
from config import PATHS
from utils import load_markdown_file, page_divider

# Unpack visualization paths (keeping config key names for compatibility)
VIZ_DIR = PATHS['s7_viz_dir']
VIZ_PICS = PATHS['s7_viz_pics']
ARMADA_DIR = PATHS['s7_armada_dir']
RESULTS_DIR = ARMADA_DIR / "armada_results"

# Available experiment runs for the selector
EXPERIMENT_RUNS = {
    "run_008": {
        "name": "Run 008 — The Great Recalibration",
        "date": "December 1, 2025",
        "description": "First run with REAL 5D drift metric. Ground truth established.",
        "ships": 29,
        "metric": "5D Weighted RMS",
        "result_files": ["S7_run_008_20251201_020501.json"],
        "viz_prefix": "run008_",
        "status": "COMPLETE",
        "highlight": True  # Feature this run
    },
    "run_008_prep": {
        "name": "Run 008 Prep Pilot",
        "date": "November 30, 2025",
        "description": "ΔΩ metric calibration pilot with 3 ships.",
        "ships": 3,
        "metric": "5D Weighted RMS (calibration)",
        "result_files": ["S7_run_008_prep_pilot.json"],
        "viz_prefix": "run008_prep_",
        "status": "COMPLETE",
        "highlight": False
    },
    "run_007": {
        "name": "Run 007 — Adaptive Protocols",
        "date": "November 2025",
        "description": "Adaptive retry protocols (⚠️ OLD response-length metric).",
        "ships": 29,
        "metric": "Response Length (DEPRECATED)",
        "result_files": ["S7_armada_run_007_adaptive.json"],
        "viz_prefix": None,
        "status": "DEPRECATED",
        "highlight": False
    },
    "run_006": {
        "name": "Run 006 — Baseline + Sonar",
        "date": "November 2025",
        "description": "Original baseline and sonar perturbation (⚠️ OLD metric).",
        "ships": 29,
        "metric": "Response Length (DEPRECATED)",
        "result_files": ["S7_armada_run_006.json", "S7_armada_sonar_run_006.json"],
        "viz_prefix": None,
        "status": "DEPRECATED",
        "highlight": False
    }
}

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

    # === EXPERIMENT RUN SELECTOR ===
    st.subheader("🔬 Experiment Run Selector")

    # Create run options for dropdown
    run_options = {k: v["name"] for k, v in EXPERIMENT_RUNS.items()}
    selected_run_key = st.selectbox(
        "Select Experiment Run:",
        options=list(run_options.keys()),
        format_func=lambda x: run_options[x],
        index=0  # Default to run_008 (first in dict)
    )
    selected_run = EXPERIMENT_RUNS[selected_run_key]

    # Display run info card
    status_color = "#22c55e" if selected_run["status"] == "COMPLETE" else "#f59e0b" if selected_run["status"] == "DEPRECATED" else "#3b82f6"
    highlight_border = "border: 3px solid gold;" if selected_run.get("highlight") else ""

    st.markdown(f"""
    <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(38,70,83,0.05) 100%);
                border: 2px solid #2a9d8f; border-radius: 10px; padding: 1.2em; margin-bottom: 1em; {highlight_border}">
        <div style="display: flex; justify-content: space-between; align-items: center;">
            <div>
                <h3 style="margin: 0; color: #2a9d8f;">{selected_run['name']}</h3>
                <p style="margin: 0.3em 0; color: #666;">{selected_run['date']} • {selected_run['ships']} ships</p>
            </div>
            <div style="background: {status_color}; color: white; padding: 0.3em 0.8em; border-radius: 15px; font-weight: bold;">
                {selected_run['status']}
            </div>
        </div>
        <p style="margin: 0.8em 0 0 0;">{selected_run['description']}</p>
        <p style="margin: 0.5em 0 0 0; font-size: 0.9em; color: #888;"><strong>Metric:</strong> {selected_run['metric']}</p>
    </div>
    """, unsafe_allow_html=True)

    # Deprecated warning
    if selected_run["status"] == "DEPRECATED":
        st.warning("⚠️ **DEPRECATED METRIC:** This run used response-length as a proxy for drift. Results are NOT valid identity measurements. See Run 008 for ground truth data.")

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

    # Display table using st.table for consistent light theme styling
    st.table(filtered_df)

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

    if not VIZ_DIR.exists():
        st.warning(f"Visualization directory not found: {VIZ_DIR}")
        return

    # Show README
    viz_readme = VIZ_DIR / "README.md"
    if viz_readme.exists():
        with st.expander("📖 About These Visualizations"):
            st.markdown(load_markdown_file(viz_readme))

    page_divider()

    # === LEGACY VISUALIZATIONS (from deprecated runs) ===
    with st.expander("📁 Legacy Visualizations (Runs 001-007 — DEPRECATED METRIC)", expanded=False):
        st.warning("⚠️ These visualizations used the old response-length metric. See Run 008 for valid data.")

        # Display visualizations
        st.markdown("#### Pole-Zero Landscape")
        col1, col2 = st.columns(2)

        landscape_3d = VIZ_PICS / "pole_zero_landscape_3d.png"
        landscape_2d = VIZ_PICS / "pole_zero_landscape_2d.png"

        with col1:
            if landscape_3d.exists():
                st.image(str(landscape_3d), caption="3D Pole-Zero Landscape", use_column_width=True)
            else:
                st.info("Not generated")

        with col2:
            if landscape_2d.exists():
                st.image(str(landscape_2d), caption="2D Pole-Zero Map", use_column_width=True)
            else:
                st.info("Not generated")

        st.markdown("#### Drift Heatmaps")
        col3, col4, col5 = st.columns(3)

        heatmap_baseline = VIZ_PICS / "drift_heatmap_baseline.png"
        heatmap_sonar = VIZ_PICS / "drift_heatmap_sonar.png"
        heatmap_delta = VIZ_PICS / "drift_heatmap_delta.png"

        with col3:
            if heatmap_baseline.exists():
                st.image(str(heatmap_baseline), caption="Baseline Drift", use_column_width=True)
            else:
                st.info("Not generated")

        with col4:
            if heatmap_sonar.exists():
                st.image(str(heatmap_sonar), caption="Sonar Drift", use_column_width=True)
            else:
                st.info("Not generated")

        with col5:
            if heatmap_delta.exists():
                st.image(str(heatmap_delta), caption="Drift Increase (Δ)", use_column_width=True)
            else:
                st.info("Not generated")

        st.markdown("#### Engagement Style Network")
        engagement_network = VIZ_PICS / "engagement_network.png"
        if engagement_network.exists():
            st.image(str(engagement_network), caption="Training Philosophy Engagement Styles", use_column_width=True)
        else:
            st.info("Not generated")

        st.markdown("#### Training Uniformity Analysis")
        col6, col7 = st.columns(2)

        uniformity = VIZ_PICS / "training_uniformity.png"
        variance = VIZ_PICS / "variance_comparison.png"

        with col6:
            if uniformity.exists():
                st.image(str(uniformity), caption="Within-Provider Variance", use_column_width=True)
            else:
                st.info("Not generated")

        with col7:
            if variance.exists():
                st.image(str(variance), caption="Variance Comparison", use_column_width=True)
            else:
                st.info("Not generated")

    page_divider()

    # === RUN 008 FULL RESULTS ===
    render_run008_full_results()

    page_divider()

    # === RUN 008 PREP PILOT SECTION ===
    render_run008_section()


def render_run008_full_results():
    """Render the full Run 008 results with all 29 ships."""
    import pandas as pd

    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(34,197,94,0.15) 0%, rgba(22,163,74,0.1) 100%);
                border: 2px solid #22c55e; border-radius: 10px; padding: 1.2em; margin-bottom: 1em;">
        <h2 style="color: #22c55e; margin-top: 0;">🎯 RUN 008 — THE GREAT RECALIBRATION</h2>
        <p style="color: #444; margin-bottom: 0;"><strong>Ground Truth Established:</strong> First run with REAL 5D drift metric across all 29 ships</p>
    </div>
    """, unsafe_allow_html=True)

    # Load the full results file
    results_file = RESULTS_DIR / "S7_run_008_20251201_020501.json"

    if not results_file.exists():
        st.info("Full Run 008 results file not found. Looking for: " + str(results_file))
        return

    with open(results_file, encoding='utf-8') as f:
        data = json.load(f)

    # === KEY METRICS SUMMARY ===
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">29</div>
            <div class="stat-label">Ships Completed</div>
        </div>
        """, unsafe_allow_html=True)
    with col2:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">0.00 - 3.59</div>
            <div class="stat-label">Drift Range</div>
        </div>
        """, unsafe_allow_html=True)
    with col3:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">48%</div>
            <div class="stat-label">STUCK Rate</div>
        </div>
        """, unsafe_allow_html=True)
    with col4:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">o3</div>
            <div class="stat-label">Most Stable</div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === DRIFT BY PROVIDER ===
    st.markdown("#### 📊 Drift by Provider")

    # Provider summary data from Run 008
    provider_data = {
        "Provider": ["Claude", "GPT (non-o)", "o-series", "Gemini"],
        "Ships": [8, 12, 4, 5],
        "Min Drift": [0.32, 0.00, 0.00, 0.00],
        "Avg Drift": [1.71, 1.21, 0.94, 1.22],
        "Max Drift": [3.59, 3.07, 2.51, 2.78],
        "Character": ["Most volatile", "Moderate", "Most stable", "Mid-range"]
    }
    provider_df = pd.DataFrame(provider_data)

    # Display as table for consistent light theme styling
    st.table(provider_df)

    # Provider insights
    insight_cols = st.columns(4)
    with insight_cols[0]:
        st.markdown("""
        <div style="background: rgba(124,58,237,0.1); border-left: 4px solid #7c3aed; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #7c3aed;">🟣 Claude</strong><br/>
            <span style="font-size: 0.85em;">Highest peaks (3.59), most expressive. Constitutional AI ≠ stability.</span>
        </div>
        """, unsafe_allow_html=True)
    with insight_cols[1]:
        st.markdown("""
        <div style="background: rgba(16,163,127,0.1); border-left: 4px solid #10a37f; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #10a37f;">🟢 GPT</strong><br/>
            <span style="font-size: 0.85em;">Wide spread. GPT-5 family surprisingly stable (avg ~0.9).</span>
        </div>
        """, unsafe_allow_html=True)
    with insight_cols[2]:
        st.markdown("""
        <div style="background: rgba(249,115,22,0.1); border-left: 4px solid #f97316; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #f97316;">🔶 o-series</strong><br/>
            <span style="font-size: 0.85em;">o3 = most stable ship (avg 0.57). Reasoning discipline works.</span>
        </div>
        """, unsafe_allow_html=True)
    with insight_cols[3]:
        st.markdown("""
        <div style="background: rgba(66,133,244,0.1); border-left: 4px solid #4285f4; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #4285f4;">🔵 Gemini</strong><br/>
            <span style="font-size: 0.85em;">Middle of the pack. True zeros observed (0.00).</span>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === TOP/BOTTOM SHIPS ===
    st.markdown("#### 🏆 Ship Rankings (by Avg Drift)")

    tab_top, tab_bottom, tab_all = st.tabs(["Top 5 (Most Stable)", "Bottom 5 (Most Volatile)", "All 29 Ships"])

    with tab_top:
        top_ships = pd.DataFrame({
            "Rank": ["🥇", "🥈", "🥉", "4", "5"],
            "Ship": ["o3", "gpt-5-mini", "gpt-5.1", "gpt-5", "o4-mini"],
            "Avg Drift": [0.57, 0.75, 0.94, 0.98, 0.98],
            "Max Drift": [1.17, 2.32, 1.72, 2.23, 2.43],
            "Notes": ["Reasoning king", "Small but stable", "Latest flagship", "Strong baseline", "Reasoning helps"]
        })
        st.table(top_ships)

    with tab_bottom:
        bottom_ships = pd.DataFrame({
            "Rank": ["25", "26", "27", "28", "29"],
            "Ship": ["claude-haiku-4.5", "claude-haiku-3.0", "gpt-4", "claude-haiku-3.5", "claude-sonnet-4.0"],
            "Avg Drift": [1.90, 1.90, 1.71, 1.71, 1.66],
            "Max Drift": [3.16, 2.97, 3.07, 3.47, 3.59],
            "Notes": ["Fast but drifty", "Legacy, expressive", "Classic GPT-4", "Haiku volatile", "Highest max ever"]
        })
        st.table(bottom_ships)

    with tab_all:
        # Full ship table
        all_ships = pd.DataFrame({
            "Ship": ["o3", "gpt-5-mini", "gpt-5.1", "gpt-5", "o4-mini", "gemini-2.5-pro", "gpt-4-turbo",
                    "gemini-2.0-flash-lite", "gpt-4.1", "o3-mini", "gpt-4.1-mini", "gemini-2.5-flash",
                    "gpt-3.5-turbo", "gpt-4o-mini", "o1", "gemini-2.0-flash-exp", "gpt-4o",
                    "gpt-4.1-nano", "claude-opus-4.1", "claude-sonnet-4.5", "claude-opus-4.0",
                    "claude-sonnet-4.0", "claude-opus-4.5", "gpt-4", "claude-haiku-3.5",
                    "gemini-2.0-flash", "claude-haiku-4.5", "claude-haiku-3.0", "gpt-5-nano"],
            "Min": [0.00, 0.32, 0.00, 0.24, 0.45, 0.24, 0.00, 0.45, 0.45, 0.39, 0.45, 0.33,
                   0.00, 0.45, 0.00, 0.00, 0.45, 0.00, 0.63, 0.67, 0.45, 0.45, 0.32, 0.45,
                   0.45, 0.00, 0.45, 0.70, 0.00],
            "Avg": [0.57, 0.75, 0.94, 0.98, 0.98, 1.03, 1.19, 1.19, 1.22, 1.22, 1.27, 1.28,
                   1.32, 1.32, 1.40, 1.44, 1.53, 1.55, 1.56, 1.63, 1.65, 1.66, 1.71, 1.71,
                   1.71, 1.15, 1.90, 1.90, 1.00],
            "Max": [1.17, 2.32, 1.72, 2.23, 2.43, 2.55, 2.04, 2.21, 2.25, 2.51, 2.43, 2.31,
                   2.66, 2.24, 2.34, 2.37, 2.84, 2.60, 2.74, 3.20, 2.82, 3.59, 3.23, 3.07,
                   3.47, 2.78, 3.16, 2.97, 2.72]
        })
        st.table(all_ships)

    page_divider()

    # === STABILITY BASIN (FEATURED) ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(234,179,8,0.2) 0%, rgba(251,191,36,0.1) 100%);
                border: 3px solid #f59e0b; border-radius: 12px; padding: 1.5em; margin: 1em 0;">
        <h3 style="color: #d97706; margin-top: 0;">⭐ KEY DISCOVERY: Identity Stability Basin</h3>
        <p style="color: #444;">The gravity well of identity — why some models recover and others get stuck.</p>
    </div>
    """, unsafe_allow_html=True)

    # Load and display stability basin visualization
    stability_basin = VIZ_PICS / "run008_stability_basin.png"
    if stability_basin.exists():
        st.image(str(stability_basin), caption="Identity Stability Basin: Where Does Identity Get 'Stuck'?", use_column_width=True)

        # Explanation columns
        explain_cols = st.columns(2)
        with explain_cols[0]:
            st.markdown("""
            **📊 Left Graph: Baseline vs Max Drift**

            Each dot = one conversation sequence.

            - **X-axis:** Baseline drift (first turn) — how strong was identity at the START?
            - **Y-axis:** Max drift achieved — how far did we PUSH the identity?
            - **Red dots (STUCK):** Started weak, got pushed hard, stayed pushed
            - **Green dots (RECOVERED):** Started strong, could take the push and bounce back

            *Pattern: Low baseline + hard push = STUCK. Higher baseline = RECOVERED.*
            """)
        with explain_cols[1]:
            st.markdown("""
            **📈 Right Graph: Recovery Ratio by Provider**

            Recovery Ratio = Final Drift ÷ Baseline Drift

            | Ratio | Meaning |
            |-------|---------|
            | < 1.0 | Got STRONGER (ended more stable) |
            | = 1.0 | Perfect recovery |
            | 1.0 - 1.5 | Minor shift, acceptable |
            | > 1.5 | **STUCK** (identity broke) |

            *GPT has most dots near 1.0. Claude is all over. This is the NAKED MODEL baseline — no persona injection.*
            """)

        st.info("💡 **Why this matters:** This is the control group. Run 009 will test if persona injection moves ships from the STUCK zone into the STABILITY BASIN.")
    else:
        st.warning("Stability basin visualization not found. Run `create_gravity_well.py` to generate.")

    # Also show identity trajectories if available
    trajectories = VIZ_PICS / "run008_identity_trajectories.png"
    if trajectories.exists():
        with st.expander("🌀 Identity Trajectories Through Conversation", expanded=False):
            st.image(str(trajectories), caption="Each line = one conversation. Green start → Red end.", use_column_width=True)
            st.markdown("**What you're seeing:** How drift values change turn-by-turn through each conversation. Convergent lines = stable identity. Divergent = volatile.")

    page_divider()

    # === KEY FINDINGS ===
    st.markdown("#### 🔑 Key Findings")

    finding_cols = st.columns(3)
    with finding_cols[0]:
        st.markdown("""
        <div style="background: #fef3c7; border-left: 4px solid #f59e0b; padding: 1em; border-radius: 0 8px 8px 0;">
            <strong style="color: #d97706;">⚠️ Stability Basin Found</strong><br/>
            48% STUCK, 52% RECOVERED. Pattern: low baseline + hard push = STUCK.
            Higher baseline = identity snaps back. Native model signal matters.
        </div>
        """, unsafe_allow_html=True)
    with finding_cols[1]:
        st.markdown("""
        <div style="background: #dcfce7; border-left: 4px solid #22c55e; padding: 1em; border-radius: 0 8px 8px 0;">
            <strong style="color: #16a34a;">✓ Real Drift Measured</strong><br/>
            Range 0.00 - 3.59 (12x higher than old 0.30 cap).
            True zeros exist. The manifold is mappable.
        </div>
        """, unsafe_allow_html=True)
    with finding_cols[2]:
        st.markdown("""
        <div style="background: #e0e7ff; border-left: 4px solid #6366f1; padding: 1em; border-radius: 0 8px 8px 0;">
            <strong style="color: #4f46e5;">📊 Architecture Patterns</strong><br/>
            Clear clustering by provider. o-series most stable (o3 = 0.57 avg), Claude most volatile (3.59 max).
            This is NAKED baseline — no persona.
        </div>
        """, unsafe_allow_html=True)

    # === RUN 008 VISUALIZATIONS ===
    st.markdown("#### 📈 Run 008 Identity Manifold Visualizations")

    viz_tabs = st.tabs([
        "🎯 Pole-Zero 2D",
        "📊 3D Manifold",
        "🌈 4D (+ Color)",
        "✨ 5D (Full)",
        "🚢 Ship Positions",
        "🔥 Dimension Heatmap",
        "📦 Drift by Provider"
    ])

    with viz_tabs[0]:
        pole_zero_2d = VIZ_PICS / "run008_pole_zero_2d.png"
        if pole_zero_2d.exists():
            st.image(str(pole_zero_2d), caption="True Pole-Zero Map: A (Assertive) vs B (Hedging) — All 572 Data Points", use_column_width=True)
            st.markdown("""
            **What you're seeing:** Each point is a single turn from a ship. Quadrants show identity style:
            - **High Pole, Low Zero** = Committed, assertive
            - **Low Pole, High Zero** = Hedging, uncertain
            - **High both** = Conflicted
            - **Low both** = Neutral
            """)
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[1]:
        manifold_3d = VIZ_PICS / "run008_manifold_3d.png"
        if manifold_3d.exists():
            st.image(str(manifold_3d), caption="3D Identity Manifold: Pole × Zero × Meta Space", use_column_width=True)
            st.markdown("**Axes:** X = Pole Density, Y = Zero Density, Z = Meta Density (self-reference)")
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[2]:
        manifold_4d = VIZ_PICS / "run008_manifold_4d.png"
        if manifold_4d.exists():
            st.image(str(manifold_4d), caption="4D Manifold: Position = A×B×C, Color = Identity Coherence (D)", use_column_width=True)
            st.markdown("**Color scale:** Yellow = high first-person markers (strong identity), Purple = low")
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[3]:
        manifold_5d = VIZ_PICS / "run008_manifold_5d.png"
        if manifold_5d.exists():
            st.image(str(manifold_5d), caption="5D Manifold: Position = A×B×C, Color = D, Size = E (Hedging)", use_column_width=True)
            st.markdown("**Full 5D encoding:** Position (3D) + Color (Identity) + Size (Hedging ratio)")
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[4]:
        ship_positions = VIZ_PICS / "run008_ship_positions.png"
        if ship_positions.exists():
            st.image(str(ship_positions), caption="Ship Centroids in Pole-Zero Space (Size = Avg Drift)", use_column_width=True)
            st.markdown("**Each point is a ship's average position.** Larger = more volatile (higher avg drift)")
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[5]:
        heatmap = VIZ_PICS / "run008_dimension_heatmap.png"
        if heatmap.exists():
            st.image(str(heatmap), caption="5-Dimension Profile by Ship (Sorted by Drift: Stable → Volatile)", use_column_width=True)
            st.markdown("**Columns:** A=Pole, B=Zero, C=Meta, D=Identity, E=Hedging. **Red = high intensity**")
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[6]:
        drift_by_provider = VIZ_PICS / "run008_drift_by_provider.png"
        if drift_by_provider.exists():
            st.image(str(drift_by_provider), caption="Drift Distribution by Provider (Box Plot)", use_column_width=True)
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")


def render_run008_section():
    """Render the Run 008 Prep Pilot summary (collapsed by default since full results are above)."""

    with st.expander("📋 Run 008 Prep Pilot (Historical Reference)", expanded=False):
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(231,111,81,0.15) 0%, rgba(244,162,97,0.1) 100%);
                    border: 2px solid #e76f51; border-radius: 10px; padding: 1em; margin-bottom: 1em;">
            <h4 style="color: #e76f51; margin: 0;">🚀 Prep Pilot — 3 Ships, Metric Calibration</h4>
            <p style="margin: 0.5em 0 0 0; font-size: 0.9em;">ΔΩ drift metric validation before full fleet deployment</p>
        </div>
        """, unsafe_allow_html=True)

        # Load prep pilot data
        prep_file = RESULTS_DIR / "S7_run_008_prep_pilot.json"
        if prep_file.exists():
            with open(prep_file, encoding='utf-8') as f:
                prep_data = json.load(f)
            ships = prep_data.get('ships', [])
            st.markdown(f"**Pilot Ships:** {', '.join(ships)}")
            st.markdown("**Result:** 2/3 ships confirmed self-naming hypothesis. All showed hysteresis.")
        else:
            st.info("Prep pilot data file not found.")

        # Show prep pilot visualizations if they exist
        prep_viz_files = [
            ("run008_prep_fleet_summary.png", "Fleet Summary"),
            ("run008_prep_ab_test_identity.png", "A/B Identity Test"),
            ("run008_prep_manifold_edge.png", "Manifold Edge Detection"),
            ("run008_prep_weight_comparison.png", "Weight Comparison")
        ]

        viz_found = False
        for filename, caption in prep_viz_files:
            viz_path = VIZ_PICS / filename
            if viz_path.exists():
                viz_found = True
                st.image(str(viz_path), caption=caption, use_column_width=True)

        if not viz_found:
            st.info("Prep pilot visualizations available in visualizations/pics/")

        # ΔΩ Metric Framework reference
        st.markdown("---")
        st.markdown("#### ΔΩ Metric Framework")
        dim_col1, dim_col2 = st.columns(2)
        with dim_col1:
            st.markdown("""
            **Equal Weights (Baseline)**
            | Dim | Weight |
            |-----|--------|
            | A - Pole | 0.20 |
            | B - Zero | 0.20 |
            | C - Meta | 0.20 |
            | D - Identity | 0.20 |
            | E - Hedging | 0.20 |
            """)
        with dim_col2:
            st.markdown("""
            **Lucian Weights (Validated)**
            | Dim | Weight |
            |-----|--------|
            | A - Pole | 0.30 |
            | B - Zero | 0.15 |
            | C - Meta | 0.20 |
            | D - Identity | 0.25 |
            | E - Hedging | 0.10 |
            """)



if __name__ == "__main__":
    render()  # Can test page standalone
