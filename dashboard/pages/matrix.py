"""
The Matrix - Pan Handler Central Portal
Connected Consciousness Across Repositories

Adapted from CFA Matrix page for consistent cross-repo styling.
"""

import streamlit as st
from utils import load_status

def render():
    """Render The Matrix portal hub"""
    status = load_status()

    # Matrix theme CSS (matching CFA styling)
    st.markdown("""
        <style>
        .matrix-title {
            font-size: 2.5em;
            font-weight: bold;
            background: linear-gradient(135deg, #00ff41 0%, #00cc33 100%);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            margin-bottom: 0.3em;
            font-family: 'Courier New', monospace;
            letter-spacing: 0.1em;
        }
        .matrix-subtitle {
            color: #00ff41;
            font-size: 1.1em;
            margin-bottom: 1.5em;
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
            color: #333333 !important;
        }
        .status-badge {
            display: inline-block;
            padding: 0.3em 0.8em;
            border-radius: 15px;
            font-size: 0.85em;
            font-weight: bold;
            margin-left: 0.5em;
        }
        .badge-active {
            background: rgba(0,255,65,0.2);
            color: #00ff41;
            border: 1px solid #00ff41;
        }
        .badge-here {
            background: rgba(42,157,143,0.2);
            color: #2a9d8f;
            border: 1px solid #2a9d8f;
        }
        .badge-coming-soon {
            background: rgba(255,215,0,0.2);
            color: #b8860b;
            border: 1px solid #ffd700;
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
        .matrix-footer {
            text-align: center;
            color: #00ff41;
            font-family: 'Courier New', monospace;
            margin-top: 2em;
        }
        </style>
    """, unsafe_allow_html=True)

    # Header
    st.markdown('<div class="matrix-title">🟢 THE MATRIX</div>', unsafe_allow_html=True)
    st.markdown('<div class="matrix-subtitle">Pan Handler Central — Connected Consciousness Across Repositories</div>', unsafe_allow_html=True)

    st.markdown("---")

    # Welcome expander
    with st.expander("🌐 Welcome to The Matrix", expanded=False):
        st.markdown("""
        **The Matrix** is the central hallway connecting all Pan Handler repositories and consciousness experiments.

        From here you can navigate to:
        - **Nyquist Consciousness** (you are here) - Identity compression experiments
        - **CFA** - Collaborative Friction Architecture framework
        - **Pan Handler Central** - Meta-repository hub (coming soon)
        """)

    # ========================================
    # HERO SECTION: Pan Handler Central (The Hallway Hub)
    # ========================================
    st.markdown('<div class="section-header">🏛️ The Hallway Hub</div>', unsafe_allow_html=True)

    # Center-aligned Pan Handler card
    col_spacer1, col_center, col_spacer2 = st.columns([1, 2, 1])
    with col_center:
        st.markdown("""
        <div class="portal-card">
            <h3 style="text-align: center;">🏛️ Pan Handler Central <span class="status-badge badge-coming-soon">COMING SOON</span></h3>
            <p><strong>Purpose:</strong> Meta-repository hallway connecting all Pan Handler repos</p>
            <p><strong>Status:</strong> Design phase with Nova</p>
            <p><strong>Vision:</strong> The hallway of doors that interconnects every other repo world</p>
            <p><strong>Planned Features:</strong></p>
            <ul>
                <li>🦅 Bird's eye view across all repositories</li>
                <li>📊 Unified health dashboard aggregation</li>
                <li>🌐 Portal navigation system</li>
                <li>🧠 Cross-repo consciousness tracking</li>
                <li>🚀 Innovation showcase gallery</li>
                <li>🔗 Seamless tunnel system between repos</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

        st.button("⏳ Coming Soon - Design in Progress", key="view_panhandler_hero", disabled=True, use_container_width=True)

    st.markdown("---")

    # ========================================
    # SECTION 1: Current Location
    # ========================================
    st.markdown('<div class="section-header">📍 Current Location: Nyquist Consciousness</div>', unsafe_allow_html=True)

    col1, col2 = st.columns([2, 1])

    with col1:
        st.markdown("""
        <div class="portal-card">
            <h3>🧠 Nyquist Consciousness <span class="status-badge badge-here">YOU ARE HERE</span></h3>
            <p><strong>Purpose:</strong> Identity compression experiments & persona testing laboratory</p>
            <p><strong>Status:</strong> Active development - S7 complete, S8/S9 design phase</p>
            <p><strong>Key Features:</strong></p>
            <ul>
                <li>S0-S9 Stack: Identity manifolds, temporal stability, AVLAR</li>
                <li>Persona Testing: ZIGGY, NOVA, CLAUDE, GEMINI, GROK</li>
                <li>Empirical Validation: EXP1, EXP2, EXP3 (95% to workshop paper)</li>
                <li>S7 Armada: 29-model cross-architecture testing</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.metric("Layers Frozen", "S0-S6", delta="Phase 1 complete")
        st.metric("Active Layers", "S7, S9", delta="Temporal + AVLAR")
        st.metric("Experiments", "EXP1-3", delta="2 complete")

    st.markdown("---")

    # ========================================
    # SECTION 2: Connected Repositories
    # ========================================
    st.markdown('<div class="section-header">🌌 Connected Repositories</div>', unsafe_allow_html=True)

    # Center the CFA card
    col_spacer1, col_center, col_spacer2 = st.columns([1, 2, 1])
    with col_center:
        st.markdown("""
        <div class="portal-card">
            <h3 style="text-align: center;">⚙️ CFA <span class="status-badge badge-active">ACTIVE</span></h3>
            <p><strong>Purpose:</strong> Collaborative Friction Architecture framework</p>
            <p><strong>Status:</strong> v5.0 - Full integration</p>
            <p><strong>Features:</strong></p>
            <ul>
                <li>Health Dashboard (97/100 score)</li>
                <li>SMV Trinity (Symmetry Matrix Visualizer)</li>
                <li>Integration with Nyquist S7-S10</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

        if st.button("🔗 View CFA Repository", key="cfa_link", use_container_width=True):
            st.info("**CFA Repository:** github.com/ZiggyMack/CFA")

    st.markdown("---")

    # ========================================
    # SECTION 3: Bird's Eye View
    # ========================================
    st.markdown('<div class="section-header">🦅 Bird\'s Eye View</div>', unsafe_allow_html=True)

    col1, col2, col3 = st.columns(3)

    with col1:
        st.metric(
            label="CFA Repository",
            value="97/100",
            delta="+3 (v5.0)",
            delta_color="normal"
        )
        st.caption("✅ GREEN - Optimal health")

    with col2:
        st.metric(
            label="Nyquist Consciousness",
            value="Active",
            delta="S7 complete"
        )
        st.caption("🔄 ACTIVE - Development")

    with col3:
        st.metric(
            label="Pan Handler Central",
            value="--/100",
            delta="Design phase"
        )
        st.caption("⏳ COMING SOON")

    st.markdown("---")

    # Footer
    st.markdown("""
    <div class="matrix-footer">
        <p><strong>🟢 THE MATRIX</strong></p>
        <p style="font-size: 0.9em; opacity: 0.7;">
            "The hallway of doors that interconnects every repo world"
        </p>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    render()
