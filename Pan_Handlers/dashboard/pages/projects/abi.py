"""
ABI PROJECT PAGE — American Bureau of Investigation

Dashboard for the transparent intelligence agency redesign project.
"""

import streamlit as st
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent))
from utils import page_divider, section_header, get_status_badge


def render():
    """Render the ABI project page."""

    # Header — Institutional Redesign
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(42,157,143,0.15) 0%, rgba(22,160,133,0.1) 100%);
                border: 2px solid #2a9d8f; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;">
        <div style="color: #888; font-size: 0.85em; margin-bottom: 0.3em;">🏛️ INSTITUTIONAL REDESIGN</div>
        <h1 style="color: #2a9d8f; margin: 0;">🔍 American Bureau of Investigation</h1>
        <p style="color: #666; font-size: 1.1em; margin: 0.5em 0 0 0;">
            Transparent, open-source intelligence work for the 21st century
        </p>
    </div>
    """, unsafe_allow_html=True)

    st.markdown(f"""
    <p>{get_status_badge("Concept")} <strong>Track:</strong> Intelligence / Governance | <strong>Lead:</strong> Ziggy + Community</p>
    """, unsafe_allow_html=True)

    page_divider()

    # === THE PROBLEM ===
    section_header("The Problem with Current Intelligence", "⚠️")

    st.markdown("""
    <div style="background: rgba(0,0,0,0.2); border-radius: 10px; padding: 1.5em;">
        <p style="color: #444; font-size: 1.1em;">
            Intelligence agencies operate in opacity, breeding mistrust and enabling abuse.
            The information architecture is Stone Age — disconnected databases, siloed knowledge,
            institutional amnesia.
        </p>
        <ul style="color: #555;">
            <li>Opacity breeds mistrust and enables abuse</li>
            <li>No public audit trails for investigative work</li>
            <li>Siloed databases prevent pattern recognition</li>
            <li>Institutional knowledge evaporates with personnel changes</li>
            <li>Legitimacy demanded through authority, not earned through transparency</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === THE VISION ===
    section_header("The ABI Vision", "🔭")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="health-card" style="border-color: #2a9d8f;">
            <h3 style="color: #2a9d8f;">Open-Source Tools</h3>
            <p style="color: #666;">
                Investigation tools built in the open. Methods that can be inspected,
                verified, and improved by the public.
            </p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div class="health-card" style="border-color: #2a9d8f;">
            <h3 style="color: #2a9d8f;">Public Audit Logs</h3>
            <p style="color: #666;">
                Every investigation step logged. Privacy-safe redaction for sensitive info.
                But the process itself is visible.
            </p>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="health-card" style="border-color: #2a9d8f;">
            <h3 style="color: #2a9d8f;">Entity Relationship Graphs</h3>
            <p style="color: #666;">
                Visual networks of connections between entities, evidence,
                and claims. Knowledge that builds over time.
            </p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div class="health-card" style="border-color: #2a9d8f;">
            <h3 style="color: #2a9d8f;">Case Dashboards</h3>
            <p style="color: #666;">
                Public-facing dashboards showing case status,
                evidence graphs, and investigative progress.
            </p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === NYQUIST CONTRIBUTION ===
    section_header("Nyquist Framework Application", "🧠")

    contributions = [
        ("Identity Tracking", "Track entities under investigation across time and contexts"),
        ("Temporal Drift Detection", "Detect evolving narratives and claim inconsistencies"),
        ("Cross-Model Triangulation", "Nova, Gemini, Grok validating claims independently"),
        ("Evidence Stream Manifolds", "Evidence modeled as temporal identity trajectories (S7)"),
        ("Public Dashboards", "Case status and evidence graphs visible to citizens"),
    ]

    for title, desc in contributions:
        st.markdown(f"""
        <div style="border-left: 3px solid #2a9d8f; padding-left: 1em; margin: 0.5em 0;">
            <strong style="color: #2a9d8f;">{title}:</strong>
            <span style="color: #666;">{desc}</span>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === ROADMAP ===
    section_header("Roadmap", "🗺️")

    milestones = [
        ("⏳", "Define transparency vs privacy boundaries"),
        ("⏳", "Design entity relationship graph system"),
        ("⏳", "Build prototype investigation dashboard"),
        ("⏳", "Develop privacy-safe redaction protocols"),
        ("⏳", "Create public demo case study"),
        ("🎯", "GOAL: Investigations you can trust because you can inspect them"),
    ]

    for icon, text in milestones:
        color = "#f4a261" if icon == "🎯" else "#888"
        st.markdown(f"<p style='color: {color}; margin: 0.5em 0;'>{icon} {text}</p>", unsafe_allow_html=True)

    page_divider()

    # === VISION ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(22,160,133,0.05) 100%);
                border-left: 4px solid #2a9d8f; padding: 1.5em; border-radius: 0 12px 12px 0;">
        <h4 style="color: #2a9d8f; margin-top: 0;">🌟 Vision</h4>
        <p style="color: #444; font-style: italic;">
            Intelligence work that serves democracy, not undermines it.
            Investigations you can trust because you can inspect them.
            Agencies that earn legitimacy through transparency, not demand it through authority.
        </p>
    </div>
    """, unsafe_allow_html=True)

    page_divider()
    st.info("🚧 **This page will expand as the project develops.** Looking for contributors with OSINT, graph database, and security expertise.")
