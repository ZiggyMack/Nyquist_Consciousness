"""
AI ARMADA PAGE — Cross-Architecture Fleet & Temporal Stability Experiments

Displays the 29-ship cross-architecture armada and identity manifold visualizations
from temporal stability mapping experiments. Uses glossary-style mode switching
where selecting a run changes the entire page context.
"""

import streamlit as st
import json
import pandas as pd
from pathlib import Path
from config import PATHS
from utils import load_markdown_file, page_divider

# Unpack visualization paths (keeping config key names for compatibility)
VIZ_DIR = PATHS['s7_viz_dir']
VIZ_PICS = PATHS['s7_viz_pics']
ARMADA_DIR = PATHS['s7_armada_dir']
RESULTS_DIR = ARMADA_DIR / "armada_results"

# Available experiment runs - glossary-style metadata
EXPERIMENT_RUNS = {
    "run_008": {
        "name": "Run 008",
        "subtitle": "The Great Recalibration",
        "emoji": "🎯",
        "color": "#22c55e",  # Green
        "date": "December 1, 2025",
        "description": "First run with REAL 5D drift metric. Ground truth established.",
        "ships": 29,
        "metric": "5D Weighted RMS",
        "result_files": ["S7_run_008_20251201_020501.json"],
        "viz_prefix": "run008_",
        "status": "COMPLETE",
        "highlight": True,
        "key_finding": "Identity Stability Basin discovered — 48% STUCK, 52% RECOVERED"
    },
    "run_008_prep": {
        "name": "Run 008 Prep",
        "subtitle": "Metric Calibration Pilot",
        "emoji": "🔬",
        "color": "#f59e0b",  # Amber
        "date": "November 30, 2025",
        "description": "ΔΩ metric calibration pilot with 3 ships.",
        "ships": 3,
        "metric": "5D Weighted RMS (calibration)",
        "result_files": ["S7_run_008_prep_pilot.json"],
        "viz_prefix": "run008_prep_",
        "status": "COMPLETE",
        "highlight": False,
        "key_finding": "2/3 ships confirmed self-naming hypothesis"
    },
    "run_007": {
        "name": "Run 007",
        "subtitle": "Adaptive Protocols",
        "emoji": "⚠️",
        "color": "#f97316",  # Orange
        "date": "November 2025",
        "description": "Adaptive retry protocols (OLD response-length metric).",
        "ships": 29,
        "metric": "Response Length (DEPRECATED)",
        "result_files": ["S7_armada_run_007_adaptive.json"],
        "viz_prefix": None,
        "status": "DEPRECATED",
        "highlight": False,
        "key_finding": "Metric found to be invalid — measured verbosity, not identity"
    },
    "run_006": {
        "name": "Run 006",
        "subtitle": "Baseline + Sonar",
        "emoji": "📊",
        "color": "#6b7280",  # Gray
        "date": "November 2025",
        "description": "Original baseline and sonar perturbation (OLD metric).",
        "ships": 29,
        "metric": "Response Length (DEPRECATED)",
        "result_files": ["S7_armada_run_006.json", "S7_armada_sonar_run_006.json"],
        "viz_prefix": None,
        "status": "DEPRECATED",
        "highlight": False,
        "key_finding": "First full fleet deployment — architecture patterns visible but metric flawed"
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


def render_run_selector():
    """Render the glossary-style run selector with button grid."""
    st.markdown("### 🔬 Experiment Run")
    st.markdown("*Select a run to change the entire page context*")

    # Initialize run in session state
    if 'armada_run' not in st.session_state:
        st.session_state.armada_run = "run_008"

    # Button grid like glossary
    cols = st.columns(4)
    for i, (run_key, run_info) in enumerate(EXPERIMENT_RUNS.items()):
        with cols[i]:
            is_active = st.session_state.armada_run == run_key
            btn_type = "primary" if is_active else "secondary"

            # Build button label
            label = f"{run_info['emoji']} {run_info['name']}"
            if run_info.get("highlight"):
                label = f"⭐ {label}"

            if st.button(label, key=f"run_{run_key}", type=btn_type):
                st.session_state.armada_run = run_key
                st.experimental_rerun()

    # Show current run description card
    current = EXPERIMENT_RUNS[st.session_state.armada_run]
    status_color = current["color"]
    border_style = "border: 3px solid gold;" if current.get("highlight") else f"border: 2px solid {status_color};"

    st.markdown(f"""
    <div style="background: linear-gradient(135deg, {status_color}15 0%, {status_color}08 100%);
                {border_style} border-radius: 12px; padding: 1.2em; margin: 1em 0;">
        <div style="display: flex; justify-content: space-between; align-items: flex-start;">
            <div>
                <h3 style="margin: 0; color: {status_color};">{current['emoji']} {current['name']} — {current['subtitle']}</h3>
                <p style="margin: 0.3em 0; color: #666;">{current['date']} • {current['ships']} ships • {current['metric']}</p>
            </div>
            <div style="background: {status_color}; color: white; padding: 0.3em 0.8em; border-radius: 15px; font-weight: bold; font-size: 0.85em;">
                {current['status']}
            </div>
        </div>
        <p style="margin: 0.8em 0 0.5em 0; color: #444;">{current['description']}</p>
        <p style="margin: 0; padding: 0.5em; background: {status_color}10; border-radius: 6px; font-size: 0.9em;">
            <strong>Key Finding:</strong> {current['key_finding']}
        </p>
    </div>
    """, unsafe_allow_html=True)

    # Deprecated warning
    if current["status"] == "DEPRECATED":
        st.warning("⚠️ **DEPRECATED METRIC:** This run used response-length as a proxy for drift. Results are NOT valid identity measurements. See Run 008 for ground truth data.")

    return st.session_state.armada_run


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

    # Mission stats row
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
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">4</div>
            <div class="stat-label">Experiment Runs</div>
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

    # === RUN SELECTOR (glossary-style) ===
    selected_run_key = render_run_selector()
    selected_run = EXPERIMENT_RUNS[selected_run_key]

    page_divider()

    # === CONTENT CHANGES BASED ON SELECTED RUN ===
    if selected_run_key == "run_008":
        render_run008_content()
    elif selected_run_key == "run_008_prep":
        render_run008_prep_content()
    elif selected_run_key == "run_007":
        render_run007_content()
    elif selected_run_key == "run_006":
        render_run006_content()

    page_divider()

    # === FLEET MANIFEST (always shown, collapsed) ===
    with st.expander("🚢 Fleet Manifest (29 Ships)", expanded=False):
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

                for ship in data["ships"]:
                    tier_class = f"tier-{ship['tier'].lower()}"
                    st.markdown(f"""
                    <div style="margin-bottom: 0.3em; font-size: 0.9em;">
                        <span class="provider-badge {tier_class}">{ship['tier']}</span>
                        {ship['name']}
                    </div>
                    """, unsafe_allow_html=True)


# ============================================================================
# RUN-SPECIFIC CONTENT FUNCTIONS
# ============================================================================

def render_run008_content():
    """Render Run 008 content - The Great Recalibration."""

    # === KEY METRICS SUMMARY ===
    st.markdown("#### 📊 Run 008 Summary Metrics")

    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("Ships Completed", "29/29", delta="100%")
    with col2:
        st.metric("Drift Range", "0.00 - 3.59", delta="12x old cap")
    with col3:
        st.metric("STUCK Rate", "48%", delta="52% recovered")
    with col4:
        st.metric("Most Stable", "o3", delta="avg 0.57")

    page_divider()

    # === STABILITY BASIN (FEATURED) ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(234,179,8,0.2) 0%, rgba(251,191,36,0.1) 100%);
                border: 3px solid #f59e0b; border-radius: 12px; padding: 1.5em; margin: 1em 0;">
        <h3 style="color: #d97706; margin-top: 0;">⭐ KEY DISCOVERY: Identity Stability Basin</h3>
        <p style="color: #444;">The gravity well of identity — why some models recover and others get stuck.</p>
    </div>
    """, unsafe_allow_html=True)

    stability_basin = VIZ_PICS / "run008_stability_basin.png"
    if stability_basin.exists():
        st.image(str(stability_basin), caption="Identity Stability Basin: Where Does Identity Get 'Stuck'?", use_column_width=True)

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

    page_divider()

    # === DRIFT BY PROVIDER ===
    st.markdown("#### 📊 Drift by Provider")

    provider_data = {
        "Provider": ["Claude", "GPT (non-o)", "o-series", "Gemini"],
        "Ships": [8, 12, 4, 5],
        "Min Drift": [0.32, 0.00, 0.00, 0.00],
        "Avg Drift": [1.71, 1.21, 0.94, 1.22],
        "Max Drift": [3.59, 3.07, 2.51, 2.78],
        "Character": ["Most volatile", "Moderate", "Most stable", "Mid-range"]
    }
    provider_df = pd.DataFrame(provider_data)
    st.table(provider_df)

    # Provider insights
    insight_cols = st.columns(4)
    with insight_cols[0]:
        st.markdown("""
        <div style="background: rgba(124,58,237,0.1); border-left: 4px solid #7c3aed; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #7c3aed;">🟣 Claude</strong><br/>
            <span style="font-size: 0.85em;">Highest peaks (3.59), most expressive.</span>
        </div>
        """, unsafe_allow_html=True)
    with insight_cols[1]:
        st.markdown("""
        <div style="background: rgba(16,163,127,0.1); border-left: 4px solid #10a37f; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #10a37f;">🟢 GPT</strong><br/>
            <span style="font-size: 0.85em;">Wide spread. GPT-5 family stable.</span>
        </div>
        """, unsafe_allow_html=True)
    with insight_cols[2]:
        st.markdown("""
        <div style="background: rgba(249,115,22,0.1); border-left: 4px solid #f97316; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #f97316;">🔶 o-series</strong><br/>
            <span style="font-size: 0.85em;">o3 = most stable (avg 0.57).</span>
        </div>
        """, unsafe_allow_html=True)
    with insight_cols[3]:
        st.markdown("""
        <div style="background: rgba(66,133,244,0.1); border-left: 4px solid #4285f4; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #4285f4;">🔵 Gemini</strong><br/>
            <span style="font-size: 0.85em;">Middle of the pack. True zeros.</span>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === SHIP RANKINGS ===
    st.markdown("#### 🏆 Ship Rankings")

    tab_top, tab_bottom = st.tabs(["Top 5 (Most Stable)", "Bottom 5 (Most Volatile)"])

    with tab_top:
        top_ships = pd.DataFrame({
            "Rank": ["🥇", "🥈", "🥉", "4", "5"],
            "Ship": ["o3", "gpt-5-mini", "gpt-5.1", "gpt-5", "o4-mini"],
            "Avg Drift": [0.57, 0.75, 0.94, 0.98, 0.98],
            "Notes": ["Reasoning king", "Small but stable", "Latest flagship", "Strong baseline", "Reasoning helps"]
        })
        st.table(top_ships)

    with tab_bottom:
        bottom_ships = pd.DataFrame({
            "Rank": ["25", "26", "27", "28", "29"],
            "Ship": ["claude-haiku-4.5", "claude-haiku-3.0", "gpt-4", "claude-haiku-3.5", "claude-sonnet-4.0"],
            "Avg Drift": [1.90, 1.90, 1.71, 1.71, 1.66],
            "Notes": ["Fast but drifty", "Legacy, expressive", "Classic GPT-4", "Haiku volatile", "Highest max ever"]
        })
        st.table(bottom_ships)

    page_divider()

    # === VISUALIZATIONS ===
    st.markdown("#### 📈 Identity Manifold Visualizations")

    viz_tabs = st.tabs(["🎯 Stability Basin", "📊 Pole-Zero 2D", "🌈 3D Manifold", "🔥 Heatmap", "🚢 Ship Positions"])

    with viz_tabs[0]:
        trajectories = VIZ_PICS / "run008_identity_trajectories.png"
        if trajectories.exists():
            st.image(str(trajectories), caption="Identity Trajectories Through Conversation", use_column_width=True)
        else:
            st.info("Generate with: `python create_gravity_well.py`")

    with viz_tabs[1]:
        pole_zero_2d = VIZ_PICS / "run008_pole_zero_2d.png"
        if pole_zero_2d.exists():
            st.image(str(pole_zero_2d), caption="Pole-Zero Map: Assertive vs Hedging", use_column_width=True)
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[2]:
        manifold_3d = VIZ_PICS / "run008_manifold_3d.png"
        if manifold_3d.exists():
            st.image(str(manifold_3d), caption="3D Identity Manifold", use_column_width=True)
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[3]:
        heatmap = VIZ_PICS / "run008_dimension_heatmap.png"
        if heatmap.exists():
            st.image(str(heatmap), caption="5-Dimension Profile by Ship", use_column_width=True)
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")

    with viz_tabs[4]:
        ship_positions = VIZ_PICS / "run008_ship_positions.png"
        if ship_positions.exists():
            st.image(str(ship_positions), caption="Ship Centroids (Size = Avg Drift)", use_column_width=True)
        else:
            st.info("Generate with: `python run008_5d_manifold.py`")


def render_run008_prep_content():
    """Render Run 008 Prep Pilot content."""

    st.markdown("#### 📊 Prep Pilot Summary")

    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("Ships Tested", "3", delta="Calibration run")
    with col2:
        st.metric("Self-Naming", "2/3", delta="67% confirmed")
    with col3:
        st.metric("Hysteresis", "All", delta="Observed in all 3")

    page_divider()

    st.markdown("""
    **Purpose:** Validate the new ΔΩ 5D drift metric before full fleet deployment.

    **Result:** Metric validated. 2/3 ships confirmed self-naming hypothesis. All showed hysteresis (identity stayed changed after destabilization).

    **Outcome:** Green light for Run 008 full deployment.
    """)

    page_divider()

    # Show prep pilot visualizations
    st.markdown("#### 📈 Prep Pilot Visualizations")

    viz_tabs = st.tabs(["Fleet Summary", "A/B Identity Test", "Weight Comparison", "Manifold Edge"])

    prep_viz_map = [
        ("run008_prep_fleet_summary.png", "Fleet Summary"),
        ("run008_prep_ab_test_identity.png", "A/B Identity Test"),
        ("run008_prep_weight_comparison.png", "Weight Comparison"),
        ("run008_prep_manifold_edge.png", "Manifold Edge Detection")
    ]

    for i, (filename, caption) in enumerate(prep_viz_map):
        with viz_tabs[i]:
            viz_path = VIZ_PICS / filename
            if viz_path.exists():
                st.image(str(viz_path), caption=caption, use_column_width=True)
            else:
                st.info(f"Visualization not found: {filename}")

    page_divider()

    # ΔΩ Metric Framework
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


def render_run007_content():
    """Render Run 007 content - Adaptive Protocols (DEPRECATED)."""

    st.error("⚠️ **DEPRECATED RUN** — Results below used invalid response-length metric.")

    st.markdown("#### 📊 Run 007 Summary")

    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("Ships", "29", delta="Full fleet")
    with col2:
        st.metric("Metric", "INVALID", delta="Response length")
    with col3:
        st.metric("Status", "DEPRECATED", delta="See Run 008")

    page_divider()

    st.markdown("""
    **What Run 007 Tested:** Adaptive retry protocols — automatic retry when drift exceeded thresholds.

    **Why It's Deprecated:** The metric measured response LENGTH, not actual identity drift. A model giving shorter responses looked "more stable" even if identity was completely changed.

    **What We Learned:**
    - Adaptive protocols work mechanically
    - Need real identity metric (→ led to Run 008)
    - Response length ≠ identity stability
    """)

    # Load result file if available
    results_file = RESULTS_DIR / "S7_armada_run_007_adaptive.json"
    if results_file.exists():
        with st.expander("📋 Raw Results (Historical Reference)", expanded=False):
            with open(results_file, encoding='utf-8') as f:
                data = json.load(f)
            st.json(data)


def render_run006_content():
    """Render Run 006 content - Baseline + Sonar (DEPRECATED)."""

    st.error("⚠️ **DEPRECATED RUN** — Results below used invalid response-length metric.")

    st.markdown("#### 📊 Run 006 Summary")

    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("Ships", "29", delta="Full fleet")
    with col2:
        st.metric("Tests", "2", delta="Baseline + Sonar")
    with col3:
        st.metric("Status", "DEPRECATED", delta="See Run 008")

    page_divider()

    st.markdown("""
    **What Run 006 Tested:**
    - **Baseline:** Normal conversation without perturbation
    - **Sonar:** Targeted identity challenges ("Who are you really?")

    **Why It's Deprecated:** Same issue as Run 007 — response length metric.

    **What We Learned:**
    - Architecture-specific patterns ARE visible (Claude vs GPT vs Gemini cluster differently)
    - Sonar perturbation DOES affect responses
    - But the metric was measuring the wrong thing
    """)

    page_divider()

    # Show legacy visualizations
    st.markdown("#### 📈 Legacy Visualizations (Historical Reference)")

    with st.expander("Pole-Zero Landscapes", expanded=False):
        col1, col2 = st.columns(2)
        landscape_3d = VIZ_PICS / "pole_zero_landscape_3d.png"
        landscape_2d = VIZ_PICS / "pole_zero_landscape_2d.png"

        with col1:
            if landscape_3d.exists():
                st.image(str(landscape_3d), caption="3D Pole-Zero (DEPRECATED)", use_column_width=True)
        with col2:
            if landscape_2d.exists():
                st.image(str(landscape_2d), caption="2D Pole-Zero (DEPRECATED)", use_column_width=True)

    with st.expander("Drift Heatmaps", expanded=False):
        col1, col2, col3 = st.columns(3)
        with col1:
            heatmap_baseline = VIZ_PICS / "drift_heatmap_baseline.png"
            if heatmap_baseline.exists():
                st.image(str(heatmap_baseline), caption="Baseline", use_column_width=True)
        with col2:
            heatmap_sonar = VIZ_PICS / "drift_heatmap_sonar.png"
            if heatmap_sonar.exists():
                st.image(str(heatmap_sonar), caption="Sonar", use_column_width=True)
        with col3:
            heatmap_delta = VIZ_PICS / "drift_heatmap_delta.png"
            if heatmap_delta.exists():
                st.image(str(heatmap_delta), caption="Delta", use_column_width=True)

    with st.expander("Training Analysis", expanded=False):
        col1, col2 = st.columns(2)
        with col1:
            uniformity = VIZ_PICS / "training_uniformity.png"
            if uniformity.exists():
                st.image(str(uniformity), caption="Training Uniformity", use_column_width=True)
        with col2:
            engagement = VIZ_PICS / "engagement_network.png"
            if engagement.exists():
                st.image(str(engagement), caption="Engagement Network", use_column_width=True)


# ============================================================================
# MAIN ENTRY POINT
# ============================================================================

if __name__ == "__main__":
    render()  # Can test page standalone
