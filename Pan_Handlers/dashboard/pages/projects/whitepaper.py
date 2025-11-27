"""
WHITEPAPER PROJECT PAGE — Nyquist Identity Manifold Publication

Dashboard for tracking the white paper publication pipeline.
"""

import streamlit as st
import sys
from pathlib import Path

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent))
from config import PATHS
from utils import page_divider, section_header, get_status_badge, load_publication_status


def render():
    """Render the Whitepaper project page."""

    # Header
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(155,89,182,0.15) 0%, rgba(52,152,219,0.1) 100%);
                border: 2px solid #9b59b6; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;">
        <h1 style="color: #9b59b6; margin: 0;">📄 Nyquist Identity Manifold White Paper</h1>
        <p style="color: #666; font-size: 1.1em; margin: 0.5em 0 0 0;">
            From chat logs to publishable theory of identity compression
        </p>
    </div>
    """, unsafe_allow_html=True)

    # Status badge
    st.markdown(f"""
    <p>{get_status_badge("In Preparation")} <strong>Track:</strong> Research / Theory</p>
    """, unsafe_allow_html=True)

    page_divider()

    # === PUBLICATION STATUS ===
    section_header("Publication Pipeline", "📊")

    pub_status = load_publication_status()
    pubs = pub_status.get('publications', {})

    col1, col2, col3 = st.columns(3)

    with col1:
        workshop = pubs.get('workshop', {})
        completion = int(workshop.get('completion', 0) * 100)
        st.markdown(f"""
        <div class="metric-box" style="border-color: #2a9d8f;">
            <div class="metric-value" style="color: #2a9d8f;">{completion}%</div>
            <div class="metric-label">Workshop Draft</div>
            <div style="color: #888; font-size: 0.8em;">{workshop.get('status', 'N/A').upper()}</div>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        arxiv = pubs.get('arxiv', {})
        completion = int(arxiv.get('completion', 0) * 100)
        st.markdown(f"""
        <div class="metric-box" style="border-color: #f4a261;">
            <div class="metric-value" style="color: #f4a261;">{completion}%</div>
            <div class="metric-label">arXiv Preprint</div>
            <div style="color: #888; font-size: 0.8em;">{arxiv.get('status', 'N/A').upper()}</div>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        journal = pubs.get('journal', {})
        completion = int(journal.get('completion', 0) * 100)
        st.markdown(f"""
        <div class="metric-box" style="border-color: #666;">
            <div class="metric-value" style="color: #666;">{completion}%</div>
            <div class="metric-label">Journal Submission</div>
            <div style="color: #888; font-size: 0.8em;">{journal.get('status', 'N/A').upper()}</div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === MILESTONES ===
    section_header("Milestones", "🎯")

    milestones = [
        ("✅", "S0-S6 frozen specification"),
        ("✅", "S7 preregistration complete"),
        ("✅", "EXP1 & EXP2 empirical validation (σ² = 0.000869)"),
        ("✅", "AI Armada Run 006 (174 probes, 100%)"),
        ("🟡", "EXP3 human rater infrastructure ready"),
        ("⏳", "Workshop draft in progress"),
        ("⏳", "arXiv submission planned"),
    ]

    col1, col2 = st.columns(2)
    mid = len(milestones) // 2 + 1

    with col1:
        for icon, text in milestones[:mid]:
            color = "#00ff41" if icon == "✅" else "#f4a261" if icon == "🟡" else "#888"
            st.markdown(f"<p style='color: {color}; margin: 0.3em 0;'>{icon} {text}</p>", unsafe_allow_html=True)

    with col2:
        for icon, text in milestones[mid:]:
            color = "#00ff41" if icon == "✅" else "#f4a261" if icon == "🟡" else "#888"
            st.markdown(f"<p style='color: {color}; margin: 0.3em 0;'>{icon} {text}</p>", unsafe_allow_html=True)

    page_divider()

    # === NYQUIST CONTRIBUTION ===
    section_header("Nyquist Framework Contribution", "🧠")

    contributions = [
        "Identity manifolds for tracking persona compression",
        "Temporal stability framework (S7) for measuring drift",
        "Cross-architecture validation (AI Armada)",
        "Omega synthesis sessions bridging theory and lived experience",
    ]

    for c in contributions:
        st.markdown(f"- {c}")

    page_divider()

    # === VISION ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(0,255,65,0.1) 0%, rgba(42,157,143,0.1) 100%);
                border-left: 4px solid #00ff41; padding: 1.5em; border-radius: 0 12px 12px 0;">
        <h4 style="color: #00ff41; margin-top: 0;">🌟 Vision</h4>
        <p style="color: #444; font-style: italic;">
            A world where AI identity is measurable, compressible, and stable across architectures.
            Where human-AI collaboration produces rigorous science that neither could achieve alone.
        </p>
    </div>
    """, unsafe_allow_html=True)
