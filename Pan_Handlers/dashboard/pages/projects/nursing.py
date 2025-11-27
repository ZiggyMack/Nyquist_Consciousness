"""
NURSING PROGRAM PROJECT PAGE — Education Innovation

Dashboard for the nursing program improvement project.
"""

import streamlit as st
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent))
from utils import page_divider, section_header, get_status_badge


def render():
    """Render the Nursing Program project page."""

    # Header
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(52,152,219,0.15) 0%, rgba(41,128,185,0.1) 100%);
                border: 2px solid #3498db; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;">
        <h1 style="color: #3498db; margin: 0;">🏥 Nursing Program Improvement</h1>
        <p style="color: #666; font-size: 1.1em; margin: 0.5em 0 0 0;">
            Designing better feedback, mentoring, and curriculum loops for nurses
        </p>
    </div>
    """, unsafe_allow_html=True)

    st.markdown(f"""
    <p>{get_status_badge("Concept")} <strong>Track:</strong> Education / Healthcare</p>
    """, unsafe_allow_html=True)

    page_divider()

    # === WHY THIS EXISTS ===
    section_header("Why This Exists", "❓")

    st.markdown("""
    <div style="background: rgba(0,0,0,0.2); border-radius: 10px; padding: 1.5em;">
        <p style="color: #444; font-size: 1.1em;">
            Nursing programs often lack granular feedback loops and struggle to detect student
            difficulties early. Many capable students fail out due to structural issues in
            program design rather than capability limitations.
        </p>
        <ul style="color: #555;">
            <li>Feedback is often delayed and non-specific</li>
            <li>Early warning signs of struggle go undetected</li>
            <li>Clinical skill development isn't tracked granularly</li>
            <li>Programs optimized for institutional convenience, not student success</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === NYQUIST CONTRIBUTION ===
    section_header("Nyquist Framework Application", "🧠")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="tunnel-card" style="border-color: #3498db;">
            <h4 style="color: #3498db;">Identity Manifolds for Growth</h4>
            <p style="color: #666;">Track student skill development trajectories over time using identity tracking</p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div class="tunnel-card" style="border-color: #3498db;">
            <h4 style="color: #3498db;">Temporal Stability Metrics</h4>
            <p style="color: #666;">Detect when students are "drifting off-track" before they fail</p>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="tunnel-card" style="border-color: #3498db;">
            <h4 style="color: #3498db;">Pattern Fidelity Index</h4>
            <p style="color: #666;">Adapted PFI to measure clinical skill retention and application</p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div class="tunnel-card" style="border-color: #3498db;">
            <h4 style="color: #3498db;">Real-Time Dashboards</h4>
            <p style="color: #666;">Student progress visualization for instructors and students</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === ROADMAP ===
    section_header("Roadmap", "🗺️")

    milestones = [
        ("⏳", "Define pilot nursing program partner"),
        ("⏳", "Interview nursing instructors about pain points"),
        ("⏳", "Draft student feedback dashboard mockups"),
        ("⏳", "Design S3-style validation experiment"),
        ("🎯", "GOAL: Pilot program with measurable outcomes"),
    ]

    for icon, text in milestones:
        color = "#f4a261" if icon == "🎯" else "#888"
        st.markdown(f"<p style='color: {color}; margin: 0.5em 0;'>{icon} {text}</p>", unsafe_allow_html=True)

    page_divider()

    # === VISION ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(52,152,219,0.1) 0%, rgba(41,128,185,0.05) 100%);
                border-left: 4px solid #3498db; padding: 1.5em; border-radius: 0 12px 12px 0;">
        <h4 style="color: #3498db; margin-top: 0;">🌟 Vision</h4>
        <p style="color: #444; font-style: italic;">
            Nursing programs that adaptively support every student, detect struggles early, and
            graduate more competent, confident nurses. Programs designed around human development
            curves, not arbitrary institutional timelines.
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()
    st.info("🚧 **This page will expand as the project develops.** Check back for dashboard mockups, interview findings, and pilot program updates.")
