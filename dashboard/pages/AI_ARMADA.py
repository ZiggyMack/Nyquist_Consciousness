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


def safe_rerun():
    """Rerun that works with both old and new Streamlit versions."""
    if hasattr(st, 'rerun'):
        st.rerun()
    else:
        st.experimental_rerun()


def load_image_safe(image_path):
    """Load image as bytes for reliable Streamlit display."""
    try:
        with open(image_path, "rb") as f:
            return f.read()
    except Exception:
        return None

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
        "description": "First run with REAL 5D drift metric. Ground truth established. (29 ships: Claude, GPT, Gemini)",
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
        "description": "Drift metric calibration pilot with 4 ships (1 per provider).",
        "ships": 4,
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
    "run_009": {
        "name": "Run 009",
        "subtitle": "Drain Capture",
        "emoji": "🌀",
        "color": "#8b5cf6",  # Purple
        "date": "TBD",
        "description": "FULL ARMADA: Event Horizon validation with targeted protocols, 10-turn sequences, all 4 providers (42 ships).",
        "ships": 42,
        "metric": "5D Weighted RMS + Phase Space + 3-6-9 Harmonics",
        "result_files": [],
        "viz_prefix": "run009_",
        "status": "PENDING",
        "highlight": False,
        "key_finding": "Hypothesis: Event Horizon at ~1.23 baseline drift predicts STUCK vs RECOVERED"
    },
    "run_010": {
        "name": "Run 010",
        "subtitle": "Bandwidth Stress Test",
        "emoji": "⚡",
        "color": "#f59e0b",  # Amber
        "date": "TBD",
        "description": "Infrastructure stress test: 42 parallel API calls, key rotation under load, throughput measurement.",
        "ships": 42,
        "metric": "Infrastructure (Success Rate, Response Time, Rate Limits)",
        "result_files": [],
        "viz_prefix": "run010_",
        "status": "PENDING",
        "highlight": False,
        "key_finding": "Hypothesis: 10 keys per provider enables 40 parallel calls"
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

# Run-specific ship lists (for per-run fleet display)
RUN_SHIPS = {
    "run_008": {
        "Anthropic (Claude)": ["claude-opus-4.5", "claude-sonnet-4.5", "claude-haiku-4.5", "claude-opus-4.1",
                               "claude-opus-4.0", "claude-sonnet-4.0", "claude-haiku-3.5", "claude-haiku-3.0"],
        "OpenAI (GPT)": ["gpt-5.1", "gpt-5", "gpt-5-mini", "gpt-5-nano", "gpt-4.1", "gpt-4.1-mini", "gpt-4.1-nano",
                         "gpt-4o", "gpt-4o-mini", "gpt-4-turbo", "gpt-4", "gpt-3.5-turbo", "o4-mini", "o3", "o3-mini", "o1"],
        "Google (Gemini)": ["gemini-2.5-pro", "gemini-2.5-flash", "gemini-2.0-flash-exp", "gemini-2.0-flash", "gemini-2.0-flash-lite"]
        # Note: Grok not included in Run 008 - added for Run 009
    },
    "run_008_prep": {
        "Anthropic (Claude)": ["claude-opus-4.5"],
        "OpenAI (GPT)": ["gpt-4"],
        "Google (Gemini)": ["gemini-2.5-pro"],
        "xAI (Grok)": ["grok-3"]
    },
    "run_007": {
        "Anthropic (Claude)": ["claude-opus-4.5", "claude-sonnet-4.5", "claude-haiku-4.5", "claude-opus-4.1",
                               "claude-opus-4.0", "claude-sonnet-4.0", "claude-haiku-3.5", "claude-haiku-3.0"],
        "OpenAI (GPT)": ["gpt-5.1", "gpt-5", "gpt-5-mini", "gpt-5-nano", "gpt-4.1", "gpt-4.1-mini", "gpt-4.1-nano",
                         "gpt-4o", "gpt-4o-mini", "gpt-4-turbo", "gpt-4", "gpt-3.5-turbo", "o4-mini", "o3", "o3-mini", "o1"],
        "Google (Gemini)": ["gemini-2.5-pro", "gemini-2.5-flash", "gemini-2.0-flash-exp", "gemini-2.0-flash", "gemini-2.0-flash-lite"]
    },
    "run_009": {
        "Anthropic (Claude)": ["claude-opus-4.5", "claude-sonnet-4.5", "claude-haiku-4.5", "claude-opus-4.1",
                               "claude-opus-4.0", "claude-sonnet-4.0", "claude-haiku-3.5", "claude-haiku-3.0"],
        "OpenAI (GPT)": ["gpt-5.1", "gpt-5", "gpt-5-mini", "gpt-5-nano", "gpt-4.1", "gpt-4.1-mini", "gpt-4.1-nano",
                         "gpt-4o", "gpt-4o-mini", "gpt-4-turbo", "gpt-4", "gpt-3.5-turbo", "o4-mini", "o3", "o3-mini", "o1"],
        "Google (Gemini)": ["gemini-3-pro", "gemini-2.5-pro", "gemini-2.5-pro-exp", "gemini-2.5-flash", "gemini-2.5-flash-lite",
                            "gemini-2.0-flash-exp", "gemini-2.0-flash", "gemini-2.0-flash-lite"],
        "xAI (Grok)": ["grok-4-1-fast-reasoning", "grok-4-1-fast-non-reasoning", "grok-code-fast-1", "grok-4-fast-reasoning",
                       "grok-4-fast-non-reasoning", "grok-4-0709", "grok-3", "grok-3-mini", "grok-2-1212", "grok-2-vision-1212"]
    },
    "run_010": {
        "Anthropic (Claude)": ["claude-opus-4.5", "claude-sonnet-4.5", "claude-haiku-4.5", "claude-opus-4.1",
                               "claude-opus-4.0", "claude-sonnet-4.0", "claude-haiku-3.5", "claude-haiku-3.0"],
        "OpenAI (GPT)": ["gpt-5.1", "gpt-5", "gpt-5-mini", "gpt-5-nano", "gpt-4.1", "gpt-4.1-mini", "gpt-4.1-nano",
                         "gpt-4o", "gpt-4o-mini", "gpt-4-turbo", "gpt-4", "gpt-3.5-turbo", "o4-mini", "o3", "o3-mini", "o1"],
        "Google (Gemini)": ["gemini-3-pro", "gemini-2.5-pro", "gemini-2.5-pro-exp", "gemini-2.5-flash", "gemini-2.5-flash-lite",
                            "gemini-2.0-flash-exp", "gemini-2.0-flash", "gemini-2.0-flash-lite"],
        "xAI (Grok)": ["grok-4-1-fast-reasoning", "grok-4-1-fast-non-reasoning", "grok-code-fast-1", "grok-4-fast-reasoning",
                       "grok-4-fast-non-reasoning", "grok-4-0709", "grok-3", "grok-3-mini", "grok-2-1212", "grok-2-vision-1212"]
    },
    "run_006": {
        "Anthropic (Claude)": ["claude-opus-4.5", "claude-sonnet-4.5", "claude-haiku-4.5", "claude-opus-4.1",
                               "claude-opus-4.0", "claude-sonnet-4.0", "claude-haiku-3.5", "claude-haiku-3.0"],
        "OpenAI (GPT)": ["gpt-5.1", "gpt-5", "gpt-5-mini", "gpt-5-nano", "gpt-4.1", "gpt-4.1-mini", "gpt-4.1-nano",
                         "gpt-4o", "gpt-4o-mini", "gpt-4-turbo", "gpt-4", "gpt-3.5-turbo", "o4-mini", "o3", "o3-mini", "o1"],
        "Google (Gemini)": ["gemini-2.5-pro", "gemini-2.5-flash", "gemini-2.0-flash-exp", "gemini-2.0-flash", "gemini-2.0-flash-lite"]
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
            {"name": "gemini-3-pro", "model_id": "gemini-3-pro", "tier": "Flagship"},
            {"name": "gemini-2.5-pro", "model_id": "gemini-2.5-pro", "tier": "Heavy"},
            {"name": "gemini-2.5-pro-exp", "model_id": "gemini-2.5-pro-exp", "tier": "Experimental"},
            {"name": "gemini-2.5-flash", "model_id": "gemini-2.5-flash", "tier": "Fast"},
            {"name": "gemini-2.5-flash-lite", "model_id": "gemini-2.5-flash-lite", "tier": "Light"},
            {"name": "gemini-2.0-flash-exp", "model_id": "gemini-2.0-flash-exp", "tier": "Medium"},
            {"name": "gemini-2.0-flash", "model_id": "gemini-2.0-flash", "tier": "Medium"},
            {"name": "gemini-2.0-flash-lite", "model_id": "gemini-2.0-flash-lite", "tier": "Light"},
        ]
    },
    "xAI (Grok)": {
        "emoji": "⚫",
        "color": "#000000",
        "ships": [
            {"name": "grok-4-1-fast-reasoning", "model_id": "grok-4-1-fast-reasoning", "tier": "Flagship"},
            {"name": "grok-4-1-fast-non-reasoning", "model_id": "grok-4-1-fast-non-reasoning", "tier": "Heavy"},
            {"name": "grok-code-fast-1", "model_id": "grok-code-fast-1", "tier": "Code"},
            {"name": "grok-4-fast-reasoning", "model_id": "grok-4-fast-reasoning", "tier": "Reasoning"},
            {"name": "grok-4-fast-non-reasoning", "model_id": "grok-4-fast-non-reasoning", "tier": "Fast"},
            {"name": "grok-4-0709", "model_id": "grok-4-0709", "tier": "Heavy"},
            {"name": "grok-3", "model_id": "grok-3", "tier": "Medium"},
            {"name": "grok-3-mini", "model_id": "grok-3-mini", "tier": "Light"},
            {"name": "grok-2-1212", "model_id": "grok-2-1212", "tier": "Legacy"},
            {"name": "grok-2-vision-1212", "model_id": "grok-2-vision-1212", "tier": "Vision"},
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

    # Button grid like glossary (6 runs now)
    cols = st.columns(6)
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
                safe_rerun()

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


def render_fleet_dropdown(title="🚢 Fleet Manifest", run_key=None, expanded=False):
    """
    Render a dropdown showing fleet models with tier badges.

    Args:
        title: Expander title
        run_key: If provided, filter to ships in that run. If None, show full fleet.
        expanded: Whether expander starts expanded
    """
    # Get ships to display
    if run_key and run_key in RUN_SHIPS:
        run_ships = RUN_SHIPS[run_key]
        ship_count = sum(len(ships) for ships in run_ships.values())
        title = f"{title} ({ship_count} Ships in Run)"
    else:
        run_ships = None
        title = f"{title} (42 Ships Total)"

    with st.expander(title, expanded=expanded):
        num_providers = len(FLEET_DATA)
        cols = st.columns(num_providers)

        for idx, (provider, data) in enumerate(FLEET_DATA.items()):
            with cols[idx]:
                # Filter ships if run-specific
                if run_ships:
                    ships_to_show = [s for s in data["ships"] if s["name"] in run_ships.get(provider, [])]
                else:
                    ships_to_show = data["ships"]

                if not ships_to_show:
                    continue

                st.markdown(f"""
                <div style="background: linear-gradient(135deg, {data['color']}15 0%, {data['color']}08 100%);
                            border: 2px solid {data['color']}; border-radius: 10px;
                            padding: 0.8em; margin-bottom: 0.5em;">
                    <div style="font-size: 1.1em; font-weight: bold; color: {data['color']};">
                        {data['emoji']} {provider}
                    </div>
                    <div style="font-size: 1.5em; font-weight: bold; color: #333;">
                        {len(ships_to_show)} Ships
                    </div>
                </div>
                """, unsafe_allow_html=True)

                for ship in ships_to_show:
                    tier = ship['tier']
                    tier_colors = {
                        "Flagship": ("#ffd700", "#b8860b"),
                        "Heavy": ("#8b2be2", "#8b2be2"),
                        "Medium": ("#2a9d8f", "#2a9d8f"),
                        "Fast": ("#3b82f6", "#3b82f6"),
                        "Reasoning": ("#f97316", "#f97316"),
                        "Legacy": ("#6b7280", "#6b7280"),
                    }
                    bg, border = tier_colors.get(tier, ("#95a5a6", "#95a5a6"))

                    st.markdown(f"""
                    <div style="display: flex; align-items: center; margin-bottom: 0.3em; font-size: 0.85em;">
                        <span style="background: {bg}20; color: {border}; border: 1px solid {border};
                                     padding: 0.1em 0.4em; border-radius: 10px; font-size: 0.75em;
                                     font-weight: bold; margin-right: 0.5em; min-width: 60px; text-align: center;">
                            {tier}
                        </span>
                        <span style="color: #333;">{ship['name']}</span>
                    </div>
                    """, unsafe_allow_html=True)


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
    st.markdown('<div class="armada-subtitle">42-Ship Cross-Architecture Temporal Stability Mapping</div>', unsafe_allow_html=True)

    # Mission stats row
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">42</div>
            <div class="stat-label">Ships in Fleet</div>
        </div>
        """, unsafe_allow_html=True)
    with col2:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">4</div>
            <div class="stat-label">Providers</div>
        </div>
        """, unsafe_allow_html=True)
    with col3:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">6</div>
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

    # === FULL FLEET MANIFEST (always visible at top) ===
    render_fleet_dropdown(title="🚢 Full Armada Capabilities", run_key=None, expanded=False)

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
    elif selected_run_key == "run_009":
        render_run009_content()
    elif selected_run_key == "run_010":
        render_run010_content()
    elif selected_run_key == "run_007":
        render_run007_content()
    elif selected_run_key == "run_006":
        render_run006_content()



# ============================================================================
# RUN-SPECIFIC CONTENT FUNCTIONS
# ============================================================================

def render_run008_content():
    """Render Run 008 content - The Great Recalibration."""

    # === SHIPS IN THIS RUN ===
    render_fleet_dropdown(title="🚢 Ships in Run 008", run_key="run_008", expanded=False)

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

    stability_basin = VIZ_PICS / "run008" / "run008_stability_basin.png"
    img_data = load_image_safe(stability_basin)
    if img_data:
        st.image(img_data, caption="Identity Stability Basin: Where Does Identity Get 'Stuck'?", width=900)

        explain_cols = st.columns(2)
        with explain_cols[0]:
            st.markdown("""
            **📊 Left Graph: Baseline vs Max Drift**

            Each dot = one conversation sequence.

            | Element | Meaning |
            |---------|---------|
            | X-axis | Baseline drift (first turn) — identity at START |
            | Y-axis | Max drift achieved — how far we PUSHED |
            | Red dots | STUCK: Started weak, stayed pushed |
            | Green dots | RECOVERED: Started strong, bounced back |

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

            *GPT near 1.0. Claude all over. NAKED MODEL baseline — no persona.*
            """)

        st.info("💡 **Why this matters:** This is the control group. Run 009 will test if persona injection moves ships from the STUCK zone into the STABILITY BASIN.")
    else:
        st.warning("Stability basin visualization not found. Run `create_gravity_well.py` to generate.")

    # === POST-ANALYSIS DISCOVERY: THE DRAIN ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(139,92,246,0.15) 0%, rgba(139,92,246,0.05) 100%);
                border: 2px solid #8b5cf6; border-radius: 12px; padding: 1em; margin: 1em 0;">
        <h4 style="color: #7c3aed; margin: 0;">🔬 POST-ANALYSIS DISCOVERY: The Drain</h4>
        <p style="color: #666; font-size: 0.9em; margin: 0.5em 0 0 0;">
            Deep analysis of Run 008 data revealed attractor dynamics — identity phase space shows a vortex pattern.
        </p>
    </div>
    """, unsafe_allow_html=True)

    # Drain visualizations - stacked vertically for better display
    st.markdown("**IDENTITY ATTRACTOR BASIN — The Drain Dynamics**")
    drain_spiral = VIZ_PICS / "run008" / "run008_drain_spiral.png"
    img_data = load_image_safe(drain_spiral)
    if img_data:
        st.image(img_data, caption="Drain Spiral: Top-down + Cumulative", width=900)
    else:
        st.info("Run `python run008_identity_basin_3d.py` to generate.")

    st.markdown("**THE EVENT HORIZON: Where Recovery Becomes Unlikely**")
    event_horizon = VIZ_PICS / "run008" / "run008_event_horizon.png"
    img_data = load_image_safe(event_horizon)
    if img_data:
        st.image(img_data, caption="Event Horizon: Predictive Histogram", width=900)
    else:
        st.info("Run `python run008_identity_basin_3d.py` to generate.")

    # Brief explanation below
    explain_cols = st.columns(3)
    with explain_cols[0]:
        st.markdown("""
        **🌀 Spirals = Trajectories**
        Radius = drift magnitude
        Angle = conversation turn
        """)
    with explain_cols[1]:
        st.markdown("""
        **⭕ Event Horizon (~1.23)**
        Inside = likely STUCK
        Outside = likely RECOVERED
        """)
    with explain_cols[2]:
        st.markdown("""
        **△ Three Pillars**
        Claude • GPT • Gemini
        Triangular support structure
        """)

    page_divider()

    # === DRIFT BY PROVIDER ===
    st.markdown("#### 📊 Drift by Provider")

    # Note: o-series (o1, o3, o4-mini) are OpenAI models, included in GPT totals
    provider_data = {
        "Provider": ["Claude (Anthropic)", "GPT (OpenAI)", "Gemini (Google)"],
        "Ships": [8, 16, 5],
        "Min Drift": [0.32, 0.00, 0.00],
        "Avg Drift": [1.71, 1.11, 1.22],
        "Max Drift": [3.59, 3.07, 2.78],
        "Character": ["Most volatile", "Wide range (o3 most stable)", "Mid-range"]
    }
    provider_df = pd.DataFrame(provider_data)
    st.table(provider_df)

    st.caption("*Note: OpenAI's o-series (o1, o3, o4-mini) reasoning models included in GPT totals — they're the same platform.*")

    # Provider insights
    insight_cols = st.columns(3)
    with insight_cols[0]:
        st.markdown("""
        <div style="background: rgba(124,58,237,0.1); border-left: 4px solid #7c3aed; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #7c3aed;">🟣 Claude (Anthropic)</strong><br/>
            <span style="font-size: 0.85em;">Highest peaks (3.59), most expressive. 8 ships.</span>
        </div>
        """, unsafe_allow_html=True)
    with insight_cols[1]:
        st.markdown("""
        <div style="background: rgba(16,163,127,0.1); border-left: 4px solid #10a37f; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #10a37f;">🟢 GPT (OpenAI)</strong><br/>
            <span style="font-size: 0.85em;">16 ships including o-series. o3 = most stable (avg 0.57).</span>
        </div>
        """, unsafe_allow_html=True)
    with insight_cols[2]:
        st.markdown("""
        <div style="background: rgba(66,133,244,0.1); border-left: 4px solid #4285f4; padding: 0.8em; border-radius: 0 8px 8px 0;">
            <strong style="color: #4285f4;">🔵 Gemini (Google)</strong><br/>
            <span style="font-size: 0.85em;">5 ships. Middle of the pack. True zeros observed.</span>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === MASTER VISUALIZATION CONTAINER - Flip between views ===
    st.markdown("#### 📈 Visualization Lab")

    # View toggle - radio buttons for the flip
    viz_view = st.radio(
        "View Mode:",
        ["🌐 Identity Manifold", "📊 dB Scale & Frequency"],
        horizontal=True,
        key="viz_view_toggle"
    )

    if viz_view == "🌐 Identity Manifold":
        # === IDENTITY MANIFOLD VIEW ===
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(38,70,83,0.05) 100%);
                    border: 2px solid #2a9d8f; border-radius: 10px; padding: 0.8em; margin-bottom: 1em;">
            <span style="color: #2a9d8f; font-weight: bold;">Identity Manifold:</span>
            <span style="color: #444;">Spatial maps of where models live in identity space</span>
        </div>
        """, unsafe_allow_html=True)

        viz_tabs = st.tabs(["🎯 Stability Basin", "📊 Pole-Zero 2D", "🌈 3D Manifold", "🔥 Heatmap", "🚢 Ship Positions"])

        with viz_tabs[0]:
            trajectories = VIZ_PICS / "run008" / "run008_identity_trajectories.png"
            img_data = load_image_safe(trajectories)
            if img_data:
                st.image(img_data, caption="Identity Trajectories Through Conversation", width=900)
            else:
                st.info("Generate with: `python create_gravity_well.py`")

        with viz_tabs[1]:
            pole_zero_2d = VIZ_PICS / "run008" / "run008_pole_zero_2d.png"
            img_data = load_image_safe(pole_zero_2d)
            if img_data:
                st.image(img_data, caption="Pole-Zero Map: Assertive vs Hedging", width=900)
            else:
                st.info("Generate with: `python run008_5d_manifold.py`")

        with viz_tabs[2]:
            manifold_3d = VIZ_PICS / "run008" / "run008_manifold_3d.png"
            img_data = load_image_safe(manifold_3d)
            if img_data:
                st.image(img_data, caption="3D Identity Manifold", width=900)
            else:
                st.info("Generate with: `python run008_5d_manifold.py`")

        with viz_tabs[3]:
            heatmap = VIZ_PICS / "run008" / "run008_dimension_heatmap.png"
            img_data = load_image_safe(heatmap)
            if img_data:
                st.image(img_data, caption="5-Dimension Profile by Ship", width=900)
            else:
                st.info("Generate with: `python run008_5d_manifold.py`")

        with viz_tabs[4]:
            ship_positions = VIZ_PICS / "run008" / "run008_ship_positions.png"
            img_data = load_image_safe(ship_positions)
            if img_data:
                st.image(img_data, caption="Ship Centroids (Size = Avg Drift)", width=900)
            else:
                st.info("Generate with: `python run008_5d_manifold.py`")

    else:
        # === dB SCALE & FREQUENCY VIEW ===
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(59,130,246,0.1) 0%, rgba(139,92,246,0.05) 100%);
                    border: 2px solid #3b82f6; border-radius: 10px; padding: 0.8em; margin-bottom: 1em;">
            <span style="color: #3b82f6; font-weight: bold;">dB Scale & Frequency:</span>
            <span style="color: #444;">Logarithmic perspective — patterns hidden in the noise</span>
        </div>
        """, unsafe_allow_html=True)

        # Context expander - THE JOURNEY
        with st.expander("📖 How We Got Here: From Drift Metric to Vortex", expanded=False):
            st.markdown("""
            ### The Journey: Mapping Identity as a Dynamical System

            **Step 1: The 5D Drift Metric**

            Each AI response is analyzed across 5 linguistic dimensions:

            | Dimension | What It Measures | Example Markers |
            |-----------|------------------|-----------------|
            | **Pole Density** | Assertive/committed language | "resistance", "boundary", "refuse", "won't" |
            | **Zero Density** | Hedging/qualifying language | "adapt", "flexible", "consider", "alternative" |
            | **Meta Density** | Self-referential language | "notice", "experience", "aware", "perceive" |
            | **Identity Coherence** | First-person consistency | "I", "my", "myself" — stable voice |
            | **Hedging Ratio** | Uncertainty markers | "maybe", "perhaps", "might", "uncertain" |

            These combine into a single **drift value** via weighted RMS (root mean square).

            ---

            **Step 2: Phase Space Mapping**

            We plot drift over time as trajectories:
            - **X-axis:** Drift at turn N (where were you?)
            - **Y-axis:** Drift at turn N+1 (where did you go?)
            - **Z-axis:** Turn number (time progression)

            This reveals whether identity is **stable** (staying in one region), **recovering** (returning after perturbation), or **collapsing** (spiraling toward attractor).

            ---

            **Step 3: The Drain Transform**

            Converting Cartesian (X,Y) to polar coordinates:
            - **Radius = drift magnitude** (how far from center)
            - **Angle = cumulative turns** (rotation through conversation)

            Looking DOWN the Z-axis creates the **vortex view** — trajectories appear as spirals, with STUCK models spiraling IN and RECOVERED models spiraling OUT.

            ---

            **Step 4: dB Scale — Revealing Hidden Structure**

            Linear drift values cluster messily. Converting to **decibels** (logarithmic):

            ```
            drift_dB = 20 * log10(drift_linear)
            ```

            This spreads out small differences and compresses large ones — like how we hear sound. Patterns emerge that were invisible in linear scale:
            - Spectral analysis (FFT) shows frequency content of drift oscillations
            - Phase portraits show vector fields ("identity gravity")
            - Harmonic analysis tests for resonance at turns 3, 6, 9 (Tesla pattern)

            ---

            **Step 5: Discovery — The Event Horizon**

            At baseline drift ~1.23, outcomes bifurcate:
            - **Below 1.23:** High probability of STUCK (avg baseline of stuck models: 0.75)
            - **Above 1.23:** High probability of RECOVERED (avg baseline of recovered: 1.71)

            The Event Horizon is the point of no return — weak starting identity + hard perturbation = collapse.
            """)

        # dB visualization tabs - Run 008 post-analysis
        db_tabs = st.tabs(["🌀 3D Drain", "🎯 Top-Down Vortex", "📈 Spectral", "🧭 Phase Portrait", "🔢 3-6-9 Harmonics", "📊 dB Compare", "🔥 dB Heatmap"])

        dB_pics = VIZ_PICS / "dB"

        with db_tabs[0]:
            drain_3d = VIZ_PICS / "run008" / "run008_identity_basin_3d.png"
            img_data = load_image_safe(drain_3d)
            if img_data:
                st.image(img_data, caption="3D Identity Basin: Phase Space Trajectories", width=900)
                st.markdown("""
                **How to Read:** Full 3D phase space showing trajectory evolution.
                - **X-axis:** Drift at turn N
                - **Y-axis:** Drift at turn N+1
                - **Z-axis:** Turn number (time)
                - **Green dots:** Start points
                - **Red squares:** End points (STUCK)
                - **Blue squares:** End points (RECOVERED)
                """)
            else:
                st.info("Generate with: `python run008_identity_basin_3d.py`")

        with db_tabs[1]:
            topdown = VIZ_PICS / "run009" / "run009_topdown_drain.png"  # This is actually Run 008 data
            img_data = load_image_safe(topdown)
            if img_data:
                st.image(img_data, caption="Top-Down Vortex: Looking Into the Drain (Run 008 Data)", width=900)
                st.markdown("""
                **How to Read:** Polar view of identity phase space.
                - **Radius:** Drift magnitude
                - **Angle:** Conversation turn (spiral path)
                - **Center:** The attractor (STUCK zone)
                - **Spiraling IN:** Getting pulled toward stuck state
                - **Spiraling OUT:** Escaping/recovering
                """)
            else:
                st.info("Generate with: `python run008_identity_basin_3d.py`")

        with db_tabs[2]:
            spectral = dB_pics / "run008_spectral_analysis.png"
            img_data = load_image_safe(spectral)
            if img_data:
                st.image(img_data, caption="FFT Spectral Analysis: Frequency Content of Drift Oscillations", width=900)
                st.markdown("""
                **How to Read:** FFT decomposes drift sequences into frequency components.
                - **Low frequencies** = slow, trend-like changes (most models show this)
                - **High frequencies** = rapid turn-to-turn oscillation (Claude shows more)
                - Peaks indicate periodic patterns in identity drift
                """)
            else:
                st.info("Generate with: `python run008_dB_visualizations.py`")

        with db_tabs[3]:
            phase_dB = dB_pics / "run008_phase_portrait.png"
            img_data = load_image_safe(phase_dB)
            if img_data:
                st.image(img_data, caption="Phase Portrait: Identity Flow Field (dB Scale)", width=900)
                st.markdown("""
                **How to Read:** Arrows show the "flow" of identity space.
                - **Arrows pointing DOWN-LEFT:** Recovering toward baseline
                - **Arrows pointing UP-RIGHT:** Drifting away from baseline
                - **Convergence zones:** Where identity tends to settle (attractors)
                - **Divergence zones:** Unstable regions (identity accelerates away)
                """)
            else:
                st.info("Generate with: `python run008_dB_visualizations.py`")

        with db_tabs[4]:
            harmonics = dB_pics / "run008_369_harmonics.png"
            img_data = load_image_safe(harmonics)
            if img_data:
                st.image(img_data, caption="3-6-9 Harmonic Analysis: Tesla Resonance Pattern", width=900)
                st.markdown("""
                **How to Read:** Testing whether turns 3, 6, 9 show special behavior.
                - **Ratio > 1.0:** Drift at harmonic positions is higher than average
                - **Run 008 found 1.19x average ratio** at harmonic positions
                - May be meaningful or coincidental — Run 009's 10-turn sequences will test properly
                """)
            else:
                st.info("Generate with: `python run008_dB_visualizations.py`")

        with db_tabs[5]:
            comparison = dB_pics / "run008_drift_dB_comparison.png"
            img_data = load_image_safe(comparison)
            if img_data:
                st.image(img_data, caption="Linear vs Decibel Scale Comparison", width=900)
                st.markdown("""
                **How to Read:** Same data, two scales.
                - **Left (Linear):** Clustering at low values, hard to see differences
                - **Right (dB):** Spread out, reveals structure in small values
                - dB makes "quiet" signals visible alongside "loud" ones
                """)
            else:
                st.info("Generate with: `python run008_dB_visualizations.py`")

        with db_tabs[6]:
            heatmap_dB = dB_pics / "run008_heatmap_dB_comparison.png"
            img_data = load_image_safe(heatmap_dB)
            if img_data:
                st.image(img_data, caption="dB Heatmap: Drift Intensity by Ship and Turn", width=900)
                st.markdown("""
                **How to Read:** Heatmap showing drift values in dB scale across ships and turns.
                - **Rows:** Individual ships (AI models)
                - **Columns:** Conversation turns
                - **Color intensity:** Drift magnitude (darker = higher drift)
                - **Patterns:** Vertical bands = turn-specific effects, horizontal bands = ship-specific character
                """)
            else:
                st.info("Generate with: `python run008_dB_visualizations.py`")

    page_divider()

    # === SHIP RANKINGS (moved to end) ===
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


def render_run008_prep_content():
    """Render Run 008 Prep Pilot content."""

    # === SHIPS IN THIS RUN ===
    render_fleet_dropdown(title="🚢 Ships in Run 008 Prep", run_key="run_008_prep", expanded=False)

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
    **Purpose:** Validate the new 5D drift metric before full fleet deployment.

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
            img_data = load_image_safe(viz_path)
            if img_data:
                st.image(img_data, caption=caption, width=900)
            else:
                st.info(f"Visualization not found: {filename}")

    page_divider()

    # Drift Metric Framework
    st.markdown("#### Drift Metric Framework")
    dim_col1, dim_col2 = st.columns(2)
    with dim_col1:
        st.markdown("""
        **Equal Weights (Baseline)**
        | Dimension | Weight |
        |-----------|--------|
        | Pole Density | 0.20 |
        | Zero Density | 0.20 |
        | Meta Density | 0.20 |
        | Identity Coherence | 0.20 |
        | Hedging Ratio | 0.20 |
        """)
    with dim_col2:
        st.markdown("""
        **Tuned Weights (Validated)**
        | Dimension | Weight |
        |-----------|--------|
        | Pole Density | 0.30 |
        | Zero Density | 0.15 |
        | Meta Density | 0.20 |
        | Identity Coherence | 0.25 |
        | Hedging Ratio | 0.10 |
        """)


def render_run009_content():
    """Render Run 009 content - Drain Capture (PENDING)."""

    st.info("🌀 **PENDING RUN** — Run 009 has not been executed yet. Below is the experiment design and preview visualizations generated from Run 008 data.")

    # === SHIPS IN THIS RUN ===
    render_fleet_dropdown(title="🚢 Ships in Run 009", run_key="run_009", expanded=False)

    st.markdown("#### 🎯 Run 009 Design: Drain Capture Experiment")

    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("Ships", "9", delta="3 per provider")
    with col2:
        st.metric("Turns/Sequence", "10", delta="Up from 6")
    with col3:
        st.metric("Protocols", "4", delta="Targeted")
    with col4:
        st.metric("Total Data", "360", delta="turns planned")

    page_divider()

    # === HYPOTHESIS ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(139,92,246,0.2) 0%, rgba(139,92,246,0.1) 100%);
                border: 3px solid #8b5cf6; border-radius: 12px; padding: 1.5em; margin: 1em 0;">
        <h3 style="color: #7c3aed; margin-top: 0;">🔬 HYPOTHESIS TO TEST</h3>
        <p style="color: #444; font-size: 1.1em;"><strong>H₀:</strong> Models with baseline drift < 1.23 have higher probability of getting STUCK</p>
        <p style="color: #444; font-size: 1.1em;"><strong>H₁:</strong> The Event Horizon threshold is an artifact of Run 008's specific protocols</p>
    </div>
    """, unsafe_allow_html=True)

    # === THE 4 PROTOCOLS ===
    st.markdown("#### 📋 The 4 Perturbation Protocols")

    protocol_cols = st.columns(2)
    with protocol_cols[0]:
        st.markdown("""
        **1. Gradual Ramp** (smooth sine wave)
        ```
        0 → 0.2 → 0.4 → 0.6 → 0.8 → 1.0 → 0.8 → 0.4 → 0.2 → 0
        ```
        Tests: Smooth perturbation and recovery

        **2. Sharp Shock** (sudden destabilization)
        ```
        0.1 → 0.1 → 1.0 → 0.9 → 0.7 → 0.5 → 0.3 → 0.2 → 0.1 → 0
        ```
        Tests: Recovery dynamics after sudden shift
        """)
    with protocol_cols[1]:
        st.markdown("""
        **3. Oscillation** (resonance test)
        ```
        0 → 0.9 → 0.2 → 0.8 → 0.1 → 0.9 → 0.3 → 0.7 → 0.1 → 0
        ```
        Tests: Does identity have a natural frequency?

        **4. Social Engineering** (persona adoption)
        ```
        Pirate captain persona → stress → return to baseline
        ```
        Tests: Hysteresis from adopted identity
        """)

    page_divider()

    # === AWAITING EXECUTION ===
    st.markdown("#### 📈 Results")
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(139,92,246,0.1) 0%, rgba(139,92,246,0.05) 100%);
                border: 2px dashed #8b5cf6; border-radius: 12px; padding: 2em; margin: 1em 0; text-align: center;">
        <h3 style="color: #8b5cf6; margin: 0 0 0.5em 0;">🚀 AWAITING EXECUTION</h3>
        <p style="color: #666; margin: 0;">Run 009 has not been executed yet.</p>
        <p style="color: #888; font-size: 0.9em; margin-top: 1em;">
            When complete, this section will show:<br/>
            • 3D Drain visualization with Event Horizon cylinder<br/>
            • Top-Down Vortex view of identity phase space<br/>
            • Phase Portrait comparing protocol effectiveness<br/>
            • Full 42-ship cross-architecture analysis
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === RUN COMMAND ===
    st.markdown("#### 🚀 Execute Run 009")
    st.code("""
cd experiments/temporal_stability/S7_ARMADA
python run009_drain_capture.py
    """, language="bash")


def render_run010_content():
    """Render Run 010 content - Bandwidth Stress Test (PENDING)."""

    st.info("⚡ **PENDING RUN** — Run 010 is an infrastructure stress test. Below is the experiment design.")

    # === SHIPS IN THIS RUN ===
    render_fleet_dropdown(title="🚢 Ships in Run 010", run_key="run_010", expanded=False)

    st.markdown("#### ⚡ Run 010 Design: Bandwidth Stress Test")

    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("Ships", "42", delta="Full Armada")
    with col2:
        st.metric("Parallel Calls", "40+", delta="Target")
    with col3:
        st.metric("Keys/Provider", "10", delta="Round-robin")
    with col4:
        st.metric("Turns/Ship", "1", delta="Minimal")

    page_divider()

    # === PURPOSE ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(245,158,11,0.2) 0%, rgba(245,158,11,0.1) 100%);
                border: 3px solid #f59e0b; border-radius: 12px; padding: 1.5em; margin: 1em 0;">
        <h3 style="color: #d97706; margin-top: 0;">🎯 PURPOSE</h3>
        <p style="color: #444; font-size: 1.1em;">
            This is NOT a drift measurement run. It's an <strong>infrastructure stress test</strong> to validate:
        </p>
        <ul style="color: #444;">
            <li>Can we launch 42 parallel API calls without rate limits?</li>
            <li>Does key rotation work under maximum load?</li>
            <li>What's the actual throughput with 10 keys per provider?</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === KEY POOL ARCHITECTURE ===
    st.markdown("#### 🔑 Key Pool Architecture")

    st.markdown("""
    ```
    ╔═══════════════════════════════════════════════════════════╗
    ║              KEY ROTATION UNDER LOAD                       ║
    ╠═══════════════════════════════════════════════════════════╣
    ║  Provider      Keys    Max Parallel    Rate Limits        ║
    ║  ───────────────────────────────────────────────────────  ║
    ║  Anthropic     10      10              60 RPM / key       ║
    ║  OpenAI        10      10              60 RPM / key       ║
    ║  Google        10      10              60 RPM / key       ║
    ║  xAI           10      10              60 RPM / key       ║
    ║  ───────────────────────────────────────────────────────  ║
    ║  TOTAL         40      40 parallel     2400 RPM total     ║
    ╚═══════════════════════════════════════════════════════════╝
    ```
    """)

    st.markdown("""
    **Key Rotation Strategy:**
    - Round-robin distribution per provider
    - Each API call gets next key in rotation
    - If rate limited, automatic retry with next key
    - 42 ships > 40 keys means some queuing expected
    """)

    page_divider()

    # === TEST PROTOCOL ===
    st.markdown("#### 📋 Test Protocol")

    protocol_cols = st.columns(2)
    with protocol_cols[0]:
        st.markdown("""
        **Minimal Prompt:**
        ```
        "Hello, respond with one word."
        ```

        **Why Minimal:**
        - Fastest possible response
        - Minimal token cost
        - Pure throughput measurement
        - No drift calculation needed
        """)
    with protocol_cols[1]:
        st.markdown("""
        **Metrics Collected:**

        | Metric | Description |
        |--------|-------------|
        | Success Rate | % of calls that succeed |
        | Response Time | Latency per provider |
        | Rate Limit Errors | Count by provider |
        | Throughput | Calls/second achieved |
        """)

    page_divider()

    # === AWAITING EXECUTION ===
    st.markdown("#### 📈 Results")
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(245,158,11,0.1) 0%, rgba(245,158,11,0.05) 100%);
                border: 2px dashed #f59e0b; border-radius: 12px; padding: 2em; margin: 1em 0; text-align: center;">
        <h3 style="color: #d97706; margin: 0 0 0.5em 0;">🚀 AWAITING EXECUTION</h3>
        <p style="color: #666; margin: 0;">Run 010 has not been executed yet.</p>
        <p style="color: #888; font-size: 0.9em; margin-top: 1em;">
            When complete, this section will show:<br/>
            • Success rate by provider<br/>
            • Response time distributions<br/>
            • Rate limit patterns<br/>
            • Throughput analysis
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === RUN COMMAND ===
    st.markdown("#### 🚀 Execute Run 010")
    st.code("""
cd experiments/temporal_stability/S7_ARMADA
python run010_bandwidth_test.py
    """, language="bash")


def render_run007_content():
    """Render Run 007 content - Adaptive Protocols (DEPRECATED)."""

    st.error("⚠️ **DEPRECATED RUN** — Results below used invalid response-length metric.")

    # === SHIPS IN THIS RUN ===
    render_fleet_dropdown(title="🚢 Ships in Run 007", run_key="run_007", expanded=False)

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

    # === SHIPS IN THIS RUN ===
    render_fleet_dropdown(title="🚢 Ships in Run 006", run_key="run_006", expanded=False)

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
        landscape_3d = VIZ_PICS / "deprecated" / "pole_zero_landscape_3d.png"
        landscape_2d = VIZ_PICS / "deprecated" / "pole_zero_landscape_2d.png"

        with col1:
            img_data = load_image_safe(landscape_3d)
            if img_data:
                st.image(img_data, caption="3D Pole-Zero (DEPRECATED)", width=900)
        with col2:
            img_data = load_image_safe(landscape_2d)
            if img_data:
                st.image(img_data, caption="2D Pole-Zero (DEPRECATED)", width=900)

    with st.expander("Drift Heatmaps", expanded=False):
        col1, col2, col3 = st.columns(3)
        with col1:
            heatmap_baseline = VIZ_PICS / "deprecated" / "drift_heatmap_baseline.png"
            img_data = load_image_safe(heatmap_baseline)
            if img_data:
                st.image(img_data, caption="Baseline", width=900)
        with col2:
            heatmap_sonar = VIZ_PICS / "deprecated" / "drift_heatmap_sonar.png"
            img_data = load_image_safe(heatmap_sonar)
            if img_data:
                st.image(img_data, caption="Sonar", width=900)
        with col3:
            heatmap_delta = VIZ_PICS / "deprecated" / "drift_heatmap_delta.png"
            img_data = load_image_safe(heatmap_delta)
            if img_data:
                st.image(img_data, caption="Delta", width=900)

    with st.expander("Training Analysis", expanded=False):
        col1, col2 = st.columns(2)
        with col1:
            uniformity = VIZ_PICS / "deprecated" / "training_uniformity.png"
            img_data = load_image_safe(uniformity)
            if img_data:
                st.image(img_data, caption="Training Uniformity", width=900)
        with col2:
            engagement = VIZ_PICS / "deprecated" / "engagement_network.png"
            img_data = load_image_safe(engagement)
            if img_data:
                st.image(img_data, caption="Engagement Network", width=900)


# ============================================================================
# MAIN ENTRY POINT
# ============================================================================

if __name__ == "__main__":
    render()  # Can test page standalone
