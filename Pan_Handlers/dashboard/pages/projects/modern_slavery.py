"""
MODERN SLAVERY PROJECT PAGE — Prison System Redesign

Dashboard for the prison reform / justice system redesign project.
"""

import streamlit as st
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent))
from utils import page_divider, section_header, get_status_badge


def render():
    """Render the Modern Slavery project page."""

    # Header — Wicked Problems: Justice
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(244,162,97,0.15) 0%, rgba(230,126,34,0.1) 100%);
                border: 2px solid #f4a261; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;">
        <div style="color: #888; font-size: 0.85em; margin-bottom: 0.3em;">🔥 WICKED PROBLEMS: JUSTICE</div>
        <h1 style="color: #f4a261; margin: 0;">⛓️ Modern Slavery Package</h1>
        <p style="color: #666; font-size: 1.1em; margin: 0.5em 0 0 0;">
            From warehousing to transformation: redesigning the carceral state
        </p>
    </div>
    """, unsafe_allow_html=True)

    st.markdown(f"""
    <p>{get_status_badge("Concept")} <strong>Track:</strong> Justice / Social Systems | <strong>Lead:</strong> Daniel + Nova + Ziggy</p>
    """, unsafe_allow_html=True)

    page_divider()

    # === THE STORY ===
    section_header("The Story", "📖")

    st.markdown("""
    <div style="background: rgba(0,0,0,0.2); border-radius: 10px; padding: 1.5em; border-left: 4px solid #f4a261;">
        <p style="color: #444; font-size: 1.1em; font-style: italic;">
            "Led by Daniel — 20 years incarcerated — paired with Nova for systems design.
            Combines lived experience with rigorous system architecture."
        </p>
        <p style="color: #555;">
            This project doesn't just theorize about prison reform. It's being built by someone
            who lived inside the system, who knows exactly where it fails, and who has the
            vision to redesign it from first principles.
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === WHY THIS EXISTS ===
    section_header("Why This Exists", "❓")

    st.markdown("""
    <div style="background: rgba(0,0,0,0.2); border-radius: 10px; padding: 1.5em;">
        <p style="color: #444; font-size: 1.1em;">
            The US prison system is structurally optimized for warehousing and recidivism,
            not transformation or reintegration. Millions of lives wasted in a system that
            serves no one — not victims, not offenders, not society.
        </p>
        <ul style="color: #555;">
            <li>System designed to warehouse, not rehabilitate</li>
            <li>Recidivism is a feature, not a bug (keeps prisons full)</li>
            <li>No meaningful tracking of personal transformation</li>
            <li>Reintegration support is virtually nonexistent</li>
            <li>20 years of institutional knowledge being wasted every day</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === NYQUIST CONTRIBUTION ===
    section_header("Nyquist Framework Application", "🧠")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="tunnel-card" style="border-color: #f4a261;">
            <h4 style="color: #f4a261;">Transformation Manifolds</h4>
            <p style="color: #666;">Identity tracking for personal growth trajectories over incarceration</p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div class="tunnel-card" style="border-color: #f4a261;">
            <h4 style="color: #f4a261;">Rehabilitation Metrics</h4>
            <p style="color: #666;">Temporal stability measurements for genuine change vs. performance</p>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="tunnel-card" style="border-color: #f4a261;">
            <h4 style="color: #f4a261;">Omega Synthesis</h4>
            <p style="color: #666;">Sessions bridging Daniel's lived experience with policy design</p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div class="tunnel-card" style="border-color: #f4a261;">
            <h4 style="color: #f4a261;">Cross-Validation</h4>
            <p style="color: #666;">Comparing different intervention approaches with rigorous metrics</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === ROADMAP ===
    section_header("Roadmap", "🗺️")

    milestones = [
        ("⏳", "Daniel's release (timeline TBD)"),
        ("⏳", "Initial vision sessions with Daniel + Nova"),
        ("⏳", "Document current system failures and pain points"),
        ("⏳", "Design alternative rehabilitation frameworks"),
        ("⏳", "Prototype dashboard for tracking inmate transformation"),
        ("🎯", "GOAL: A system that actually rehabilitates"),
    ]

    for icon, text in milestones:
        color = "#f4a261" if icon == "🎯" else "#888"
        st.markdown(f"<p style='color: {color}; margin: 0.5em 0;'>{icon} {text}</p>", unsafe_allow_html=True)

    page_divider()

    # === VISION ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(244,162,97,0.1) 0%, rgba(230,126,34,0.05) 100%);
                border-left: 4px solid #f4a261; padding: 1.5em; border-radius: 0 12px 12px 0;">
        <h4 style="color: #f4a261; margin-top: 0;">🌟 Vision</h4>
        <p style="color: #444; font-style: italic;">
            A justice system that actually rehabilitates. Prisons that transform rather than warehouse.
            A world where Daniel's 20 years weren't wasted, but become the foundation for preventing
            others from suffering the same fate.
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()
    st.info("🚧 **Awaiting Daniel's release to begin active development.** This project will be led by someone with direct lived experience of the system we're redesigning.")
