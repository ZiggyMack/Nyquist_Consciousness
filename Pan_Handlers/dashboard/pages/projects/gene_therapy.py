"""
GENE THERAPY PROJECT PAGE — Biomedical Research Support

Dashboard for the gene therapy research tools project.
"""

import streamlit as st
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent))
from utils import page_divider, section_header, get_status_badge


def render():
    """Render the Gene Therapy project page."""

    # Header — Wicked Problems: Healthcare
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(39,174,96,0.15) 0%, rgba(46,204,113,0.1) 100%);
                border: 2px solid #27ae60; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;">
        <div style="color: #888; font-size: 0.85em; margin-bottom: 0.3em;">🔥 WICKED PROBLEMS: HEALTHCARE</div>
        <h1 style="color: #27ae60; margin: 0;">🧬 Gene Therapy Research Support</h1>
        <p style="color: #666; font-size: 1.1em; margin: 0.5em 0 0 0;">
            Collaborative tools for tracking genetic intervention outcomes
        </p>
    </div>
    """, unsafe_allow_html=True)

    st.markdown(f"""
    <p>{get_status_badge("Concept")} <strong>Track:</strong> Biomedical Research | <strong>Lead:</strong> Caelum + Ziggy + Nova</p>
    """, unsafe_allow_html=True)

    page_divider()

    # === WHY THIS EXISTS ===
    section_header("Why This Exists", "❓")

    st.markdown("""
    <div style="background: rgba(0,0,0,0.2); border-radius: 10px; padding: 1.5em;">
        <p style="color: #444; font-size: 1.1em;">
            Gene therapy research involves complex longitudinal data across patients, interventions,
            and outcomes. Current tools don't adequately track identity-level changes or enable
            cross-study synthesis.
        </p>
        <ul style="color: #555;">
            <li>Patient trajectories are hard to visualize over time</li>
            <li>Cross-study patterns remain hidden in siloed data</li>
            <li>Research teams lack collaborative dashboards</li>
            <li>No unified framework for tracking intervention effects</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === NYQUIST CONTRIBUTION ===
    section_header("Nyquist Framework Application", "🧠")

    contributions = [
        ("Identity Manifolds", "Adapted to patient health trajectories over intervention cycles"),
        ("Temporal Stability", "Frameworks for tracking intervention effects over time"),
        ("Cross-Study Detection", "S3-style empirical methods for pattern detection"),
        ("Collaborative Dashboards", "Real-time tools for research team coordination"),
    ]

    col1, col2 = st.columns(2)
    for i, (title, desc) in enumerate(contributions):
        col = col1 if i % 2 == 0 else col2
        with col:
            st.markdown(f"""
            <div class="tunnel-card" style="border-color: #27ae60;">
                <h4 style="color: #27ae60;">{title}</h4>
                <p style="color: #666;">{desc}</p>
            </div>
            """, unsafe_allow_html=True)

    page_divider()

    # === ROADMAP ===
    section_header("Roadmap", "🗺️")

    milestones = [
        ("⏳", "Onboard Caelum as project lead"),
        ("⏳", "Define initial research questions and data requirements"),
        ("⏳", "Design patient trajectory tracking system"),
        ("⏳", "Build pilot dashboard for single gene therapy study"),
        ("🎯", "GOAL: Cross-study pattern discovery platform"),
    ]

    for icon, text in milestones:
        color = "#f4a261" if icon == "🎯" else "#888"
        st.markdown(f"<p style='color: {color}; margin: 0.5em 0;'>{icon} {text}</p>", unsafe_allow_html=True)

    page_divider()

    # === VISION ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(39,174,96,0.1) 0%, rgba(46,204,113,0.05) 100%);
                border-left: 4px solid #27ae60; padding: 1.5em; border-radius: 0 12px 12px 0;">
        <h4 style="color: #27ae60; margin-top: 0;">🌟 Vision</h4>
        <p style="color: #444; font-style: italic;">
            Gene therapy research accelerated by intelligent collaborative tools.
            Patterns discovered across studies that no single lab could see alone.
            Faster, safer paths from lab to patient.
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()
    st.info("🚧 **This page will expand as the project develops.** Awaiting Caelum onboarding to define research priorities.")
