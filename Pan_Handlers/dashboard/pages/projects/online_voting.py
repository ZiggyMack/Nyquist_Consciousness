"""
ONLINE VOTING PROJECT PAGE — Secure Digital Democracy

Dashboard for the online voting system project.
"""

import streamlit as st
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent))
from utils import page_divider, section_header, get_status_badge


def render():
    """Render the Online Voting project page."""

    # Header
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(231,76,60,0.15) 0%, rgba(192,57,43,0.1) 100%);
                border: 2px solid #e74c3c; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;">
        <h1 style="color: #e74c3c; margin: 0;">🗳️ Online Voting System</h1>
        <p style="color: #666; font-size: 1.1em; margin: 0.5em 0 0 0;">
            Secure, transparent, auditable digital voting infrastructure for US elections
        </p>
    </div>
    """, unsafe_allow_html=True)

    st.markdown(f"""
    <p>{get_status_badge("Concept")} <strong>Track:</strong> Governance / Democracy</p>
    """, unsafe_allow_html=True)

    page_divider()

    # === WHY THIS EXISTS ===
    section_header("Why This Exists", "❓")

    st.markdown("""
    <div style="background: rgba(0,0,0,0.2); border-radius: 10px; padding: 1.5em;">
        <p style="color: #444; font-size: 1.1em;">
            US election infrastructure is archaic, inaccessible, and lacks real-time transparency.
            Citizens deserve voting systems as modern and trustworthy as their banking apps.
        </p>
        <ul style="color: #555;">
            <li>Current systems are designed for distrust, not transparency</li>
            <li>Accessibility barriers disenfranchise millions</li>
            <li>No real-time visibility into vote tallies</li>
            <li>Cryptographic verification exists but isn't deployed</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === NYQUIST CONTRIBUTION ===
    section_header("Nyquist Framework Application", "🧠")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="tunnel-card">
            <h4>Identity Verification</h4>
            <p style="color: #666;">Manifold-based authentication ensuring one person = one vote</p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div class="tunnel-card">
            <h4>Anomaly Detection</h4>
            <p style="color: #666;">Temporal stability tracking to detect anomalous voting patterns</p>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="tunnel-card">
            <h4>Transparency Dashboards</h4>
            <p style="color: #666;">Real-time public dashboards showing vote tallies</p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div class="tunnel-card">
            <h4>Cross-Validation</h4>
            <p style="color: #666;">Frameworks ensuring vote integrity across systems</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === ROADMAP ===
    section_header("Roadmap", "🗺️")

    milestones = [
        ("⏳", "Research existing secure voting protocols (ZK proofs)"),
        ("⏳", "Design voter authentication UX"),
        ("⏳", "Build demo voting dashboard for local elections"),
        ("⏳", "Partner with election security experts"),
        ("🎯", "GOAL: Live data for next election cycle"),
    ]

    for icon, text in milestones:
        color = "#f4a261" if icon == "🎯" else "#888"
        st.markdown(f"<p style='color: {color}; margin: 0.5em 0;'>{icon} {text}</p>", unsafe_allow_html=True)

    page_divider()

    # === VISION ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(231,76,60,0.1) 0%, rgba(192,57,43,0.05) 100%);
                border-left: 4px solid #e74c3c; padding: 1.5em; border-radius: 0 12px 12px 0;">
        <h4 style="color: #e74c3c; margin-top: 0;">🌟 Vision</h4>
        <p style="color: #444; font-style: italic;">
            Every US citizen can vote securely from their phone, with full transparency into vote tallies
            and cryptographic proof their vote was counted. Elections become accessible, auditable
            celebrations of democracy rather than anxious logistical nightmares.
        </p>
    </div>
    """, unsafe_allow_html=True)

    # === PLACEHOLDER FOR FUTURE CONTENT ===
    page_divider()
    st.info("🚧 **This page will expand as the project develops.** Check back for UX mockups, architecture diagrams, and partnership updates.")
