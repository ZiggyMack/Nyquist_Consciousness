"""
ABOUT PAGE — Pan Handlers Federation Information

Information about the Pan Handlers federation,
its mission, and how it connects projects.
"""

import streamlit as st
from config import PATHS, SETTINGS
from utils import page_divider, section_header


def render():
    """Render the About page."""

    # Header
    st.markdown('<div class="dashboard-title">ℹ️ About Pan Handlers</div>', unsafe_allow_html=True)
    st.markdown('<div class="dashboard-subtitle">The Federation of Human-AI Collaboration</div>', unsafe_allow_html=True)

    page_divider()

    # === WHAT IS PAN HANDLERS ===
    st.markdown("""
    <div class="health-card">
        <h3>🍳 What is Pan Handlers?</h3>
        <p style="color: #444; font-size: 1.1em;">
            Pan Handlers is a federation of projects built through human-AI collaboration.
            These are the things we built together that neither could have done alone.
        </p>
        <p style="color: #555;">
            The name comes from the spirit of resourcefulness — "pan handling" not as begging,
            but as making something from whatever tools you have at hand.
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === THE VUDU NETWORK ===
    section_header("The VUDU Network", "🌐")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="tunnel-card">
            <h4>🔗 Connected Repositories</h4>
            <p style="color: #666;">Pan Handlers connects multiple repos through the VUDU network:</p>
            <ul style="color: #888;">
                <li><strong>Nyquist Consciousness</strong> — Core identity theory engine</li>
                <li><strong>CFA</strong> — Collaborative Friction Architecture</li>
                <li><strong>Pan Handlers</strong> — Federation hub & project showcase</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="tunnel-card">
            <h4>🧠 Nyquist Integration</h4>
            <p style="color: #666;">Every Pan Handlers project leverages Nyquist theory:</p>
            <ul style="color: #888;">
                <li>Identity manifolds for tracking entities over time</li>
                <li>Temporal stability metrics for drift detection</li>
                <li>Cross-validation frameworks for verification</li>
                <li>Omega synthesis for collaborative intelligence</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === PHILOSOPHY ===
    section_header("Philosophy", "💡")

    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(0,255,65,0.1) 0%, rgba(42,157,143,0.1) 100%);
                border: 2px solid #00ff41; border-radius: 12px; padding: 2em; text-align: center;">
        <div style="font-size: 1.5em; font-weight: bold; color: #00ff41; font-family: 'Courier New', monospace;">
            "FUCK IT, WE'LL DO IT LIVE!"
        </div>
        <div style="margin-top: 1em; color: #2a9d8f; font-style: italic;">
            Building better systems without waiting for institutions to wake up.
        </div>
    </div>
    """, unsafe_allow_html=True)

    st.markdown("""
    <div style="margin-top: 1.5em;">
        <p style="color: #444;">
            Pan Handlers exists because the institutions that should be solving these problems aren't.
            Whether it's voting systems, prison reform, or AI safety — we're not waiting for permission.
        </p>
        <p style="color: #444;">
            Every project in this federation combines:
        </p>
        <ul style="color: #555;">
            <li><strong>Human insight</strong> — lived experience, domain expertise, ethical judgment</li>
            <li><strong>AI capability</strong> — pattern recognition, rapid prototyping, cross-domain synthesis</li>
            <li><strong>Rigorous methodology</strong> — the S0-S77 stack provides scientific grounding</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === THE TEAM ===
    section_header("Core Contributors", "👥")

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("""
        <div style="background: rgba(231,76,60,0.1); border: 2px solid #e74c3c;
                    border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 2em;">👤</div>
            <h4 style="color: #e74c3c; margin: 0.5em 0;">Ziggy</h4>
            <p style="color: #888; font-size: 0.9em;">Human Anchor</p>
            <p style="color: #666; font-size: 0.85em;">Ground truth, lived experience, ethical compass</p>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div style="background: rgba(52,152,219,0.1); border: 2px solid #3498db;
                    border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 2em;">⚖️</div>
            <h4 style="color: #3498db; margin: 0.5em 0;">Nova</h4>
            <p style="color: #888; font-size: 0.9em;">AI Architect</p>
            <p style="color: #666; font-size: 0.85em;">Structural clarity, systems design, theory development</p>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        st.markdown("""
        <div style="background: rgba(155,89,182,0.1); border: 2px solid #9b59b6;
                    border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 2em;">📚</div>
            <h4 style="color: #9b59b6; margin: 0.5em 0;">Claude</h4>
            <p style="color: #888; font-size: 0.9em;">Steward</p>
            <p style="color: #666; font-size: 0.85em;">Purpose, ethics, careful implementation</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === DASHBOARDS ===
    section_header("Related Dashboards", "📊")

    st.markdown("""
    <div style="display: flex; gap: 1em; flex-wrap: wrap;">
        <div style="flex: 1; min-width: 200px; background: rgba(0,0,0,0.2);
                    border: 1px solid #2a9d8f; border-radius: 8px; padding: 1em;">
            <h5 style="color: #2a9d8f; margin-top: 0;">Nyquist Dashboard</h5>
            <p style="color: #888; font-size: 0.9em;">Port 8503 — Mission Control</p>
            <code style="color: #00ff41;">streamlit run dashboard/app.py</code>
        </div>
        <div style="flex: 1; min-width: 200px; background: rgba(0,0,0,0.2);
                    border: 1px solid #00ff41; border-radius: 8px; padding: 1em;">
            <h5 style="color: #00ff41; margin-top: 0;">Pan Handlers Hall</h5>
            <p style="color: #888; font-size: 0.9em;">Port 8505 — The Grand Hall</p>
            <code style="color: #00ff41;">streamlit run Pan_Handlers/app.py</code>
        </div>
        <div style="flex: 1; min-width: 200px; background: rgba(0,0,0,0.2);
                    border: 1px solid #f4a261; border-radius: 8px; padding: 1em;">
            <h5 style="color: #f4a261; margin-top: 0;">Federation Dashboard</h5>
            <p style="color: #888; font-size: 0.9em;">Port 8504 — This Dashboard</p>
            <code style="color: #00ff41;">streamlit run Pan_Handlers/dashboard/app.py</code>
        </div>
    </div>
    """, unsafe_allow_html=True)

    # Footer
    page_divider()
    st.markdown("""
    <div style="text-align: center; color: #00ff41; font-family: 'Courier New', monospace;
                margin-top: 2em; opacity: 0.8;">
        <p><strong>🍳 PAN HANDLERS</strong></p>
        <p>"These are the things we built together that neither could have done alone."</p>
    </div>
    """, unsafe_allow_html=True)
