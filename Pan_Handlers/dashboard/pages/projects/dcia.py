"""
D.C.I.A. PROJECT PAGE — Decentralized Central Intelligence Agency

Dashboard for the decentralized intelligence architecture project.
"""

import streamlit as st
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent))
from utils import page_divider, section_header, get_status_badge


def render():
    """Render the D.C.I.A. project page."""

    # Header — Institutional Redesign
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(155,89,182,0.15) 0%, rgba(142,68,173,0.1) 100%);
                border: 2px solid #9b59b6; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;">
        <div style="color: #888; font-size: 0.85em; margin-bottom: 0.3em;">🏛️ INSTITUTIONAL REDESIGN</div>
        <h1 style="color: #9b59b6; margin: 0;">🌐 Decentralized Central Intelligence Agency</h1>
        <p style="color: #666; font-size: 1.1em; margin: 0.5em 0 0 0;">
            Distributed intelligence with centralized synthesis
        </p>
    </div>
    """, unsafe_allow_html=True)

    st.markdown(f"""
    <p>{get_status_badge("Concept")} <strong>Track:</strong> Intelligence / Governance | <strong>Lead:</strong> Ziggy + Community</p>
    """, unsafe_allow_html=True)

    page_divider()

    # === THE ARCHITECTURE ===
    section_header("The D.C.I.A. Architecture", "🏗️")

    st.markdown("""
    <div style="background: rgba(0,0,0,0.2); border-radius: 10px; padding: 1.5em;">
        <p style="color: #444; font-size: 1.1em;">
            Current intelligence architecture is centralized in <strong>both</strong> collection AND analysis,
            creating single points of failure and opacity. D.C.I.A. proposes a different model:
        </p>
    </div>
    """, unsafe_allow_html=True)

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="tunnel-card" style="border-color: #9b59b6; text-align: center;">
            <h3 style="color: #9b59b6;">Decentralized Collection</h3>
            <p style="color: #666; font-size: 3em; margin: 0;">🌐</p>
            <p style="color: #888;">
                Open-source intelligence (OSINT) tools<br>
                Distributed data gathering protocols<br>
                Transparent collection methods
            </p>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="tunnel-card" style="border-color: #9b59b6; text-align: center;">
            <h3 style="color: #9b59b6;">Centralized Synthesis</h3>
            <p style="color: #666; font-size: 3em; margin: 0;">🧠</p>
            <p style="color: #888;">
                Transparent analytical frameworks<br>
                Public-facing intelligence assessments<br>
                Open methods documentation
            </p>
        </div>
        """, unsafe_allow_html=True)

    st.markdown("""
    <div style="text-align: center; margin: 1em 0;">
        <p style="color: #9b59b6; font-size: 1.2em; font-weight: bold;">
            Many eyes collecting → One brain synthesizing → Everyone can verify
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === WHY THIS EXISTS ===
    section_header("Why This Exists", "❓")

    st.markdown("""
    <div style="background: rgba(0,0,0,0.2); border-radius: 10px; padding: 1.5em;">
        <ul style="color: #555; font-size: 1.05em;">
            <li>Single points of failure in current architecture</li>
            <li>Centralization enables abuse and corruption</li>
            <li>Citizens can't verify intelligence assessments</li>
            <li>Methods are black boxes — trust is demanded, not earned</li>
            <li>Institutional capture by political interests</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === NYQUIST CONTRIBUTION ===
    section_header("Nyquist Framework Application", "🧠")

    contributions = [
        ("S3-S8 Framework", "Applied to intelligence work — rigorous methodology"),
        ("Identity Tracking", "Tracking actors and narratives across time"),
        ("Temporal Stability", "Detecting information warfare and narrative manipulation"),
        ("Cross-Model Validation", "Multiple AI perspectives validating claims"),
        ("Public Dashboards", "De-classified intelligence assessments visible to all"),
    ]

    for title, desc in contributions:
        st.markdown(f"""
        <div style="border-left: 3px solid #9b59b6; padding-left: 1em; margin: 0.5em 0;">
            <strong style="color: #9b59b6;">{title}:</strong>
            <span style="color: #666;">{desc}</span>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === ROADMAP ===
    section_header("Roadmap", "🗺️")

    milestones = [
        ("⏳", "Survey existing OSINT (open-source intelligence) tools"),
        ("⏳", "Design distributed collection protocols"),
        ("⏳", "Build centralized synthesis dashboard"),
        ("⏳", "Define classification and de-classification workflows"),
        ("⏳", "Create demo intelligence assessment"),
        ("🎯", "GOAL: Intelligence that serves citizens, not just states"),
    ]

    for icon, text in milestones:
        color = "#f4a261" if icon == "🎯" else "#888"
        st.markdown(f"<p style='color: {color}; margin: 0.5em 0;'>{icon} {text}</p>", unsafe_allow_html=True)

    page_divider()

    # === VISION ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(155,89,182,0.1) 0%, rgba(142,68,173,0.05) 100%);
                border-left: 4px solid #9b59b6; padding: 1.5em; border-radius: 0 12px 12px 0;">
        <h4 style="color: #9b59b6; margin-top: 0;">🌟 Vision</h4>
        <p style="color: #444; font-style: italic;">
            Intelligence that serves citizens, not just states.
            A world where you can verify intelligence assessments because the methods are open.
            Where distributed eyes and centralized brains create better understanding
            than monolithic secrecy ever could.
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()
    st.info("🚧 **This page will expand as the project develops.** Looking for contributors with distributed systems, OSINT, and governance expertise.")
