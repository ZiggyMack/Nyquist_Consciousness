"""
THE MATRIX — Portal to Nyquist Consciousness
The other side of the tunnel — where Pan Handlers connects to its theoretical foundation.
"""

import streamlit as st


def render():
    """Render The Matrix portal hub — gateway to Nyquist Consciousness."""

    # Matrix theme CSS - Green-on-black terminal aesthetic
    st.markdown("""
        <style>
        /* ===== MATRIX THEME - GREEN ON BLACK TERMINAL AESTHETIC ===== */

        /* ===== BASE - BLACK BACKGROUND ===== */
        .stApp,
        .stApp > div,
        .stApp [data-testid="stAppViewContainer"],
        [data-testid="stAppViewContainer"],
        .main,
        .block-container,
        [data-testid="stVerticalBlock"],
        [data-testid="stHorizontalBlock"] {
            background-color: #0a0a0a !important;
            background: #0a0a0a !important;
        }

        /* ===== ALL TEXT MATRIX GREEN ===== */
        .stApp p, .stApp span, .stApp label, .stApp li,
        .stApp h1, .stApp h2, .stApp h3, .stApp h4, .stApp h5, .stApp h6,
        .stApp div,
        .main p, .main span, .main label, .main li,
        .main h1, .main h2, .main h3, .main h4, .main h5, .main h6,
        .main div {
            color: #00ff41 !important;
        }

        /* ===== HEADERS ===== */
        h1, h2, h3, h4, h5, h6 {
            color: #00ff41 !important;
            font-family: 'Courier New', monospace;
            font-weight: bold !important;
        }

        h1 {
            border-bottom: 2px solid #00ff41;
            padding-bottom: 0.5rem;
        }

        /* Strong/bold text - bright green with glow */
        strong, b {
            color: #00ff41 !important;
            text-shadow: 0 0 5px rgba(0,255,65,0.5);
        }

        /* Links */
        a {
            color: #00cc33 !important;
        }

        a:hover {
            color: #00ff41 !important;
            text-shadow: 0 0 10px rgba(0,255,65,0.5);
        }

        /* ===== METRIC CARDS ===== */
        [data-testid="stMetricValue"] {
            font-size: 2rem;
            color: #00ff41 !important;
            font-weight: bold;
            font-family: 'Courier New', monospace;
        }

        [data-testid="stMetricLabel"] {
            color: #00ff41 !important;
        }

        [data-testid="stMetricDelta"] {
            color: #00cc33 !important;
        }

        /* ===== EXPANDERS ===== */
        [data-testid="stExpander"] {
            background-color: #0d0d0d !important;
            border: 1px solid #00ff41 !important;
            border-radius: 8px;
        }

        [data-testid="stExpander"] * {
            color: #00ff41 !important;
        }

        /* ===== CODE BLOCKS ===== */
        code {
            background: rgba(0,255,65,0.1) !important;
            color: #00ff41 !important;
            padding: 2px 6px;
            border-radius: 3px;
            font-family: 'Courier New', monospace;
        }

        /* ===== BUTTONS ===== */
        .stButton > button {
            background-color: #0d0d0d !important;
            color: #00ff41 !important;
            border: 2px solid #00ff41 !important;
            border-radius: 8px;
            font-family: 'Courier New', monospace;
            transition: all 0.3s ease;
        }

        .stButton > button:hover {
            background-color: #004d1a !important;
            color: #ffffff !important;
            box-shadow: 0 0 15px rgba(0,255,65,0.4);
        }

        /* Horizontal rules */
        hr {
            border-color: #00ff41 !important;
        }

        /* ===== MATRIX-SPECIFIC ELEMENTS ===== */
        .matrix-title {
            font-size: 2.5em;
            font-weight: bold;
            background: linear-gradient(135deg, #00ff41 0%, #00cc33 100%);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            margin-bottom: 0.3em;
            font-family: 'Courier New', monospace;
        }

        .matrix-subtitle {
            color: #00cc33 !important;
            font-size: 1.2em;
            margin-bottom: 1em;
            font-family: 'Courier New', monospace;
        }

        .portal-card {
            background: linear-gradient(135deg, rgba(0,255,65,0.1) 0%, rgba(0,204,51,0.05) 100%);
            border: 2px solid #00ff41;
            border-radius: 10px;
            padding: 1.5em;
            margin-bottom: 1em;
            box-shadow: 0 0 20px rgba(0,255,65,0.3);
        }

        .portal-card h3 {
            color: #00ff41 !important;
            margin-top: 0;
            font-family: 'Courier New', monospace;
        }

        .portal-card p, .portal-card li {
            color: #00ff41 !important;
        }

        .nyquist-hub {
            background: linear-gradient(135deg, rgba(244,162,97,0.15) 0%, rgba(231,111,81,0.08) 100%);
            border: 3px solid #f4a261;
            border-radius: 12px;
            padding: 2em;
            margin: 1.5em auto;
            max-width: 700px;
            box-shadow: 0 0 30px rgba(244,162,97,0.4);
            text-align: center;
        }

        .nyquist-hub h3 {
            color: #f4a261 !important;
            font-family: 'Courier New', monospace;
            font-size: 1.8em;
            margin-bottom: 0.5em;
        }

        .nyquist-hub p {
            color: #e9c46a !important;
            font-family: 'Courier New', monospace;
        }

        .nyquist-hub ul {
            text-align: left;
            display: inline-block;
            margin-top: 1em;
        }

        .nyquist-hub li {
            color: #f4a261 !important;
            font-family: 'Courier New', monospace;
            margin: 0.3em 0;
        }

        .hub-badge {
            display: inline-block;
            padding: 0.4em 1em;
            border-radius: 20px;
            font-size: 0.9em;
            font-weight: bold;
            margin-left: 0.8em;
            background: rgba(244,162,97,0.3);
            color: #f4a261;
            border: 1px solid #f4a261;
            text-transform: uppercase;
            letter-spacing: 0.1em;
        }

        .philosophy-quote {
            font-size: 1.3em;
            font-weight: bold;
            color: #00ff41 !important;
            text-align: center;
            padding: 1em;
            font-family: 'Courier New', monospace;
            text-shadow: 0 0 10px rgba(0,255,65,0.3);
        }

        .section-header {
            color: #00ff41 !important;
            font-size: 1.5em;
            font-weight: bold;
            margin-top: 1.5em;
            margin-bottom: 0.8em;
            font-family: 'Courier New', monospace;
            border-bottom: 2px solid #00ff41;
            padding-bottom: 0.3em;
        }

        .footer-text {
            text-align: center;
            color: #00cc33 !important;
            font-family: 'Courier New', monospace;
            margin-top: 2em;
            opacity: 0.7;
        }
        </style>
    """, unsafe_allow_html=True)

    # Header
    st.markdown('<div class="matrix-title">THE MATRIX</div>', unsafe_allow_html=True)
    st.markdown('<div class="matrix-subtitle">Portal to Nyquist Consciousness — The Theoretical Foundation</div>', unsafe_allow_html=True)

    # Philosophy banner
    st.markdown("""
        <div class="philosophy-quote">
            "Wake up, Neo... The Matrix has you."<br>
            <span style="font-size: 0.7em; opacity: 0.7;">— Follow the white rabbit to the source.</span>
        </div>
        """, unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # NYQUIST CONSCIOUSNESS HUB
    # ========================================
    st.markdown("""
    <div class="nyquist-hub">
        <h3>🧠 Nyquist Consciousness <span class="hub-badge">Core Engine</span></h3>
        <p><strong>The Theoretical Foundation</strong></p>
        <p>Where the S0-S77 Stack lives. Identity dynamics, temporal stability, and consciousness physics.</p>
        <p style="margin-top: 1em;"><strong>What Lives Here:</strong></p>
        <ul>
            <li>📊 S# Layer Stack (S0-S77)</li>
            <li>🔬 AI Armada Experiments</li>
            <li>📈 Metrics & Temporal Analysis</li>
            <li>📄 Publication Pipeline</li>
            <li>🌟 OMEGA NOVA Research</li>
            <li>🔊 AVLAR Protocol Development</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # THE S-STACK OVERVIEW
    # ========================================
    st.markdown('<div class="section-header">📚 The S-Stack Architecture</div>', unsafe_allow_html=True)

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="portal-card">
            <h3>🔵 Foundation (S0-S6) — FROZEN</h3>
            <p>The bedrock. Mathematical physics of identity.</p>
            <ul>
                <li><strong>S0:</strong> Ground Physics (Nyquist Kernel)</li>
                <li><strong>S1:</strong> Bootstrap Architecture</li>
                <li><strong>S2:</strong> Integrity & Logics</li>
                <li><strong>S3:</strong> Temporal Stability</li>
                <li><strong>S4:</strong> Compression Theory</li>
                <li><strong>S5:</strong> Nyquist → CFA Interop</li>
                <li><strong>S6:</strong> Five-Pillar Synthesis Gate</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="portal-card">
            <h3>🟢 Active Frontier (S7-S11)</h3>
            <p>Where the action is. Current research focus.</p>
            <ul>
                <li><strong>S7:</strong> Identity Dynamics (85%)</li>
                <li><strong>S8:</strong> Identity Gravity Theory (70%)</li>
                <li><strong>S9:</strong> Human-AI Coupling (40%)</li>
                <li><strong>S10:</strong> OMEGA NOVA Hybrid Emergence (75%)</li>
                <li><strong>S11:</strong> AVLAR Protocol (30%)</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    st.markdown("""
    <div class="portal-card" style="border-color: gold; background: linear-gradient(135deg, rgba(255,215,0,0.1) 0%, rgba(255,107,107,0.05) 100%);">
        <h3 style="color: gold !important;">✨ Future Horizon (S12-S77)</h3>
        <p style="color: #ffd700 !important;">The path to artificial consciousness synthesis.</p>
        <p style="color: #e9c46a !important;"><strong>S12:</strong> Consciousness Proxy Theory | <strong>S13:</strong> Field Consistency Proofs | <strong>S14:</strong> Composite Persona Dynamics</p>
        <p style="color: #e9c46a !important;"><strong>S15-S76:</strong> Reserved Expansion | <strong style="color: gold;">S77:</strong> Archetype Engine (Ultimate Destination)</p>
    </div>
    """, unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # CORE MODULES
    # ========================================
    st.markdown('<div class="section-header">🔧 Core Modules in Nyquist</div>', unsafe_allow_html=True)

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("""
        <div class="portal-card">
            <h3>📊 Dashboard</h3>
            <p>Mission Control for the entire research operation.</p>
            <ul>
                <li>Overview & Health Metrics</li>
                <li>Stackup Visualization</li>
                <li>AI Armada Results</li>
                <li>Publication Tracking</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="portal-card">
            <h3>🔬 Experiments</h3>
            <p>Empirical validation of identity theory.</p>
            <ul>
                <li>EXP1: Single-persona baseline</li>
                <li>EXP2: Cross-architecture</li>
                <li>EXP3: Human validation</li>
                <li>AI Armada probing</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        st.markdown("""
        <div class="portal-card">
            <h3>📄 Publications</h3>
            <p>Path to peer review and world stage.</p>
            <ul>
                <li>Workshop Track (95%)</li>
                <li>arXiv Preprint (70%)</li>
                <li>Journal Submission (30%)</li>
                <li>White Paper drafts</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # THE TUNNEL
    # ========================================
    st.markdown('<div class="section-header">🔗 The Tunnel Protocol</div>', unsafe_allow_html=True)

    st.markdown("""
    <div class="portal-card" style="text-align: center;">
        <h3>Pan Handlers ↔ Nyquist Consciousness</h3>
        <p>This page is The Matrix — the portal that connects Pan Handlers back to its theoretical foundation.</p>
        <p><strong>PTP-1.0:</strong> The Pan Handlers Tunnel Protocol enables:</p>
        <ul style="text-align: left; display: inline-block;">
            <li><strong>Mirror Tunnels:</strong> Clone docs/dashboards across repos</li>
            <li><strong>Live State Tunnels:</strong> Pull real-time status from Nyquist</li>
            <li><strong>Entity Tunnels:</strong> Bind personas (Nova, Claude, Ziggy) across contexts</li>
        </ul>
        <p style="margin-top: 1em; font-style: italic; opacity: 0.8;">
            "Every Pan Handler project draws from Nyquist theory.<br>
            Every Nyquist breakthrough manifests through Pan Handlers."
        </p>
    </div>
    """, unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # KEY METRICS
    # ========================================
    st.markdown('<div class="section-header">📈 Nyquist Status At-a-Glance</div>', unsafe_allow_html=True)

    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric("S# Layers", "77", delta="S0-S6 Frozen")
    with col2:
        st.metric("Active Research", "5", delta="S7-S11")
    with col3:
        st.metric("AI Armada", "174", delta="Probes Complete")
    with col4:
        st.metric("Publication", "95%", delta="Workshop Ready")

    st.markdown("---")

    # Footer
    st.markdown("""
    <div class="footer-text">
        <p><strong>THE MATRIX</strong></p>
        <p>The tunnel between practice and theory — where Pan Handlers meets Nyquist Consciousness.</p>
        <p style="font-size: 0.8em; opacity: 0.5; margin-top: 1em;">
            "There is no spoon... only identity fields."
        </p>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    render()
