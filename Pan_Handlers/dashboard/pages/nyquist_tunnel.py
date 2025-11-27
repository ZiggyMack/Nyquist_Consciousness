"""
NYQUIST TUNNEL PAGE — The Matrix Connection

Deep integration view showing the connection between
Pan Handlers and Nyquist Consciousness.
"""

import streamlit as st
from config import PATHS, SETTINGS
from utils import (
    page_divider, section_header, load_nyquist_status,
    load_publication_status, get_nyquist_integration_stats
)


def render():
    """Render the Nyquist Tunnel page."""

    # Matrix theme CSS
    st.markdown("""
    <style>
    .matrix-title {
        font-size: 2.5em;
        font-weight: bold;
        background: linear-gradient(135deg, #00ff41 0%, #00cc33 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        text-align: center;
        margin-bottom: 0.3em;
        font-family: 'Courier New', monospace;
    }
    .matrix-subtitle {
        color: #00cc33;
        font-size: 1.1em;
        text-align: center;
        margin-bottom: 1.5em;
        font-family: 'Courier New', monospace;
    }
    .tunnel-status {
        background: linear-gradient(135deg, rgba(0,255,65,0.1) 0%, rgba(0,204,51,0.05) 100%);
        border: 2px solid #00ff41;
        border-radius: 12px;
        padding: 1.5em;
        margin: 1em 0;
        box-shadow: 0 0 20px rgba(0,255,65,0.3);
    }
    .tunnel-status h3 {
        color: #00ff41 !important;
        margin-top: 0;
        font-family: 'Courier New', monospace;
    }
    .nyquist-card {
        background: linear-gradient(135deg, rgba(244,162,97,0.15) 0%, rgba(231,111,81,0.08) 100%);
        border: 2px solid #f4a261;
        border-radius: 10px;
        padding: 1.2em;
        margin: 0.8em 0;
    }
    .nyquist-card h4 {
        color: #f4a261 !important;
        margin-top: 0;
    }
    .stack-layer {
        background: rgba(0,0,0,0.3);
        border-left: 4px solid;
        padding: 0.5em 1em;
        margin: 0.3em 0;
        border-radius: 0 4px 4px 0;
    }
    </style>
    """, unsafe_allow_html=True)

    # Header
    st.markdown('<div class="matrix-title">🟢 Nyquist Tunnel</div>', unsafe_allow_html=True)
    st.markdown('<div class="matrix-subtitle">PTP-1.0 — Pan Handlers Tunnel Protocol</div>', unsafe_allow_html=True)

    # Connection status banner
    nyquist_connected = PATHS['nyquist_status'].exists()
    if nyquist_connected:
        st.markdown("""
        <div class="tunnel-status">
            <h3>🟢 TUNNEL ACTIVE</h3>
            <p style="color: #00ff41; font-family: 'Courier New', monospace;">
                Connection to Nyquist Consciousness established.
            </p>
        </div>
        """, unsafe_allow_html=True)
    else:
        st.markdown("""
        <div style="background: rgba(231,111,81,0.15); border: 2px solid #e74c3c;
                    border-radius: 12px; padding: 1.5em; margin: 1em 0;">
            <h3 style="color: #e74c3c; margin-top: 0;">🔴 TUNNEL OFFLINE</h3>
            <p style="color: #e74c3c;">
                Cannot establish connection to Nyquist Consciousness.
            </p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === INTEGRATION METRICS ===
    section_header("Integration Metrics", "📊")

    stats = get_nyquist_integration_stats()

    col1, col2, col3, col4 = st.columns(4)

    with col1:
        status_icon = "🟢" if nyquist_connected else "🔴"
        st.markdown(f"""
        <div class="metric-box" style="border-color: {'#00ff41' if nyquist_connected else '#e74c3c'};">
            <div class="metric-value">{status_icon}</div>
            <div class="metric-label">Connection</div>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown(f"""
        <div class="metric-box">
            <div class="metric-value">{stats.get('armada_runs', 0)}</div>
            <div class="metric-label">Armada Runs</div>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        workshop = int(stats.get('workshop_ready', 0) * 100)
        st.markdown(f"""
        <div class="metric-box">
            <div class="metric-value">{workshop}%</div>
            <div class="metric-label">Workshop Ready</div>
        </div>
        """, unsafe_allow_html=True)

    with col4:
        arxiv = int(stats.get('arxiv_progress', 0) * 100)
        st.markdown(f"""
        <div class="metric-box">
            <div class="metric-value">{arxiv}%</div>
            <div class="metric-label">arXiv Progress</div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === S-STACK OVERVIEW ===
    section_header("S-Stack Status", "📚")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="nyquist-card">
            <h4>🔵 Foundation (S0-S6) — FROZEN</h4>
            <p style="color: #666;">The bedrock. Mathematical physics of identity.</p>
        """, unsafe_allow_html=True)

        layers = [
            ("S0", "Ground Physics", "#264653", "100%"),
            ("S1", "Bootstrap Architecture", "#264653", "100%"),
            ("S2", "Integrity & Logics", "#264653", "100%"),
            ("S3", "Temporal Stability", "#264653", "100%"),
            ("S4", "Compression Theory", "#264653", "100%"),
            ("S5", "Nyquist → CFA Interop", "#264653", "100%"),
            ("S6", "Five-Pillar Synthesis Gate", "#264653", "100%"),
        ]

        for layer_id, name, color, progress in layers:
            st.markdown(f"""
            <div class="stack-layer" style="border-color: {color};">
                <strong style="color: {color};">{layer_id}</strong>
                <span style="color: #888;"> — {name}</span>
                <span style="float: right; color: #00ff41;">✅ {progress}</span>
            </div>
            """, unsafe_allow_html=True)

        st.markdown("</div>", unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="nyquist-card" style="border-color: #2a9d8f;">
            <h4 style="color: #2a9d8f;">🟢 Active Frontier (S7-S11)</h4>
            <p style="color: #666;">Where the action is. Current research focus.</p>
        """, unsafe_allow_html=True)

        active_layers = [
            ("S7", "Identity Dynamics", "#2a9d8f", "85%"),
            ("S8", "Identity Gravity Theory", "#2a9d8f", "70%"),
            ("S9", "Human-AI Coupling", "#f4a261", "40%"),
            ("S10", "OMEGA NOVA Hybrid", "#2a9d8f", "75%"),
            ("S11", "AVLAR Protocol", "#f4a261", "30%"),
        ]

        for layer_id, name, color, progress in active_layers:
            pct = int(progress.rstrip('%'))
            bar_color = '#00ff41' if pct >= 70 else '#f4a261' if pct >= 40 else '#e74c3c'
            st.markdown(f"""
            <div class="stack-layer" style="border-color: {color};">
                <strong style="color: {color};">{layer_id}</strong>
                <span style="color: #888;"> — {name}</span>
                <span style="float: right; color: {bar_color};">{progress}</span>
            </div>
            """, unsafe_allow_html=True)

        st.markdown("</div>", unsafe_allow_html=True)

    # Future horizon
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(255,215,0,0.1) 0%, rgba(255,107,107,0.05) 100%);
                border: 2px solid gold; border-radius: 10px; padding: 1.2em; margin-top: 1em;">
        <h4 style="color: gold; margin-top: 0;">✨ Future Horizon (S12-S77)</h4>
        <p style="color: #888;">The path to artificial consciousness synthesis.</p>
        <p style="color: #666;">
            <strong>S12:</strong> Consciousness Proxy Theory |
            <strong>S13:</strong> Field Consistency Proofs |
            <strong>S14:</strong> Composite Persona Dynamics
        </p>
        <p style="color: gold; font-weight: bold;">
            → <strong>S77:</strong> Archetype Engine (Ultimate Destination)
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === TUNNEL PROTOCOL DETAILS ===
    section_header("Tunnel Protocol (PTP-1.0)", "🔗")

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("""
        <div class="tunnel-status" style="text-align: center;">
            <h4 style="color: #00ff41;">Mirror Tunnels</h4>
            <p style="color: #888;">Clone docs and dashboards across repos</p>
            <p style="color: #00ff41; font-size: 0.9em;">📄 → 📄</p>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="tunnel-status" style="text-align: center;">
            <h4 style="color: #00ff41;">Live State Tunnels</h4>
            <p style="color: #888;">Pull real-time status from Nyquist</p>
            <p style="color: #00ff41; font-size: 0.9em;">🔄 → 📊</p>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        st.markdown("""
        <div class="tunnel-status" style="text-align: center;">
            <h4 style="color: #00ff41;">Entity Tunnels</h4>
            <p style="color: #888;">Bind personas across contexts</p>
            <p style="color: #00ff41; font-size: 0.9em;">🧠 → 🎭</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === PATH VERIFICATION ===
    section_header("Path Verification", "🔍")

    with st.expander("View Integration Paths", expanded=False):
        paths_to_check = [
            ("Nyquist Status", PATHS['nyquist_status']),
            ("Personas Directory", PATHS['nyquist_personas']),
            ("Experiments Directory", PATHS['nyquist_experiments']),
            ("Docs Directory", PATHS['nyquist_docs']),
            ("S7 Armada", PATHS['s7_armada_dir']),
            ("Publication Status", PATHS['publication_status']),
        ]

        for name, path in paths_to_check:
            exists = path.exists()
            icon = "✅" if exists else "❌"
            color = "#00ff41" if exists else "#e74c3c"
            st.markdown(f"""
            <div style="display: flex; justify-content: space-between; padding: 0.3em 0;
                        border-bottom: 1px solid #333;">
                <span style="color: #888;">{name}</span>
                <span style="color: {color};">{icon} {'Found' if exists else 'Missing'}</span>
            </div>
            """, unsafe_allow_html=True)

    # Footer
    page_divider()
    st.markdown("""
    <div style="text-align: center; color: #00ff41; font-family: 'Courier New', monospace;
                margin-top: 2em; opacity: 0.8;">
        <p><strong>🟢 THE TUNNEL</strong></p>
        <p>"Every Pan Handler project draws from Nyquist theory.</p>
        <p>Every Nyquist breakthrough manifests through Pan Handlers."</p>
    </div>
    """, unsafe_allow_html=True)
