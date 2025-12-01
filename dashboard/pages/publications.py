"""
PUBLICATIONS PAGE — Publications & White Papers

Full publication tracking dashboard with Publication Perfection Meter,
paper drafts, venue targets, and research milestone tracking.
"""

import streamlit as st
import pandas as pd
from pathlib import Path
from config import PATHS
from utils import load_markdown_file, load_publication_status, page_divider

REPO_ROOT = PATHS['repo_root']


def render_publication_meter():
    """Render the Publication Perfection Meter showing research maturity."""
    pub_status = load_publication_status()
    pubs = pub_status.get("publications", {})

    if not pubs:
        st.info("📊 Publication tracking not yet configured. Add `publication_status.json` to enable the Perfection Meter.")
        return

    st.markdown("## 🎯 Publication Perfection Meter")
    st.markdown("*Track progress toward world-stage research publication*")

    page_divider()

    # Overview table
    rows = []
    for key in ["workshop", "arxiv", "journal"]:
        if key in pubs:
            info = pubs[key]
            status_emoji = {
                "ready": "✅",
                "drafting": "🟡",
                "concept": "⚪",
                "submitted": "🚀",
                "published": "🏆"
            }.get(info.get("status", ""), "❓")

            rows.append({
                "Track": key.capitalize(),
                "Target": info.get("target", ""),
                "Status": f"{status_emoji} {info.get('status', '').upper()}",
                "Progress": f"{int(info.get('completion', 0.0) * 100)}%"
            })

    if rows:
        df = pd.DataFrame(rows)
        st.dataframe(df, use_container_width=True, hide_index=True)

    page_divider()

    # Detailed breakdown per publication
    for key in ["workshop", "arxiv", "journal"]:
        if key not in pubs:
            continue

        info = pubs[key]

        with st.expander(f"📄 {key.capitalize()} — {info.get('target', 'TBD')}", expanded=(key == "workshop")):
            col1, col2 = st.columns([2, 1])

            with col1:
                st.markdown(f"**Target Venue:** {info.get('target', 'TBD')}")
                st.markdown(f"**Status:** `{info.get('status', 'unknown').upper()}`")

                completion = info.get('completion', 0.0)
                st.progress(completion)
                st.caption(f"{int(completion * 100)}% Complete")

                if "notes" in info:
                    st.markdown(f"**Notes:** {info['notes']}")

            with col2:
                st.markdown("### Requirements")
                reqs = info.get("requirements", {})
                if reqs:
                    for req_key, done in reqs.items():
                        check = "✅" if done else "❌"
                        # Format requirement key nicely
                        req_label = req_key.replace("_", " ").title()
                        st.markdown(f"{check} {req_label}")
                else:
                    st.caption("_No requirements defined_")

    # Milestones section
    milestones = pub_status.get("milestones", {})
    if milestones:
        page_divider()
        st.markdown("### 🎯 Current Milestones")

        col1, col2, col3 = st.columns(3)

        with col1:
            st.metric("Current", milestones.get("current", "—"))

        with col2:
            st.metric("Next", milestones.get("next", "—"))

        with col3:
            target_date = milestones.get("publication_target_date", "—")
            st.metric("Target Date", target_date)

        if "notes" in milestones:
            st.info(f"**Note:** {milestones['notes']}")


def render_publication_tracks():
    """Render publication track overview with targets and timeline."""
    st.markdown("## 📚 Publication Tracks")
    st.markdown("*Three-track research publication strategy*")

    page_divider()

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("### 🏛️ Workshop Track")
        st.markdown("""
        **Target:** AAAI 2025 / NeurIPS Workshop

        **Focus:** Novel identity framework demonstration

        **Status:** Primary drafting phase

        **Key Deliverables:**
        - Core theoretical framework
        - Empirical validation results
        - Cross-architecture experiments
        """)

    with col2:
        st.markdown("### 📜 arXiv Track")
        st.markdown("""
        **Target:** arXiv Preprint

        **Focus:** Full technical specification

        **Status:** In preparation

        **Key Deliverables:**
        - Complete S0-S11 specification
        - Mathematical formalization
        - Comprehensive appendices
        """)

    with col3:
        st.markdown("### 🏆 Journal Track")
        st.markdown("""
        **Target:** Nature Machine Intelligence

        **Focus:** Peer-reviewed publication

        **Status:** Future milestone

        **Key Deliverables:**
        - Rigorous peer review
        - Extended empirical studies
        - Community validation
        """)


def render_paper_drafts():
    """Render paper drafts from the paper/ directory."""
    st.markdown("## 📝 Paper Drafts")
    st.markdown("*Current manuscripts and working documents*")

    page_divider()

    paper_root = REPO_ROOT / "paper"
    white_paper_root = REPO_ROOT / "WHITE-PAPER"

    if not paper_root.exists() and not white_paper_root.exists():
        st.info("No paper/ or WHITE-PAPER/ directory found yet.")
        return

    # Check paper/ directory
    if paper_root.exists():
        st.markdown("### 📂 paper/")
        for sub in sorted(paper_root.iterdir()):
            if sub.is_dir():
                st.markdown(f"#### {sub.name}")
                md_files = list(sub.glob("*.md"))
                if not md_files:
                    st.write("_No markdown files yet._")
                for md in md_files:
                    with st.expander(f"📄 {md.name}"):
                        st.markdown(load_markdown_file(md))

    # Check WHITE-PAPER/ directory
    if white_paper_root.exists():
        st.markdown("### 📂 WHITE-PAPER/")
        md_files = list(white_paper_root.glob("*.md"))
        if md_files:
            for md in sorted(md_files):
                with st.expander(f"📄 {md.name}"):
                    st.markdown(load_markdown_file(md))
        else:
            st.write("_No markdown files yet._")


def render_key_results():
    """Render key empirical results summary - toot our horn!"""
    st.markdown("## 🏆 Key Empirical Results")
    st.markdown("*Validated findings ready for publication*")

    page_divider()

    # Hero metrics
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric(
            "Cross-Arch Variance",
            "σ² = 0.000869",
            delta="Remarkably Low",
            delta_color="normal"
        )

    with col2:
        st.metric(
            "Hypotheses Confirmed",
            "14/25",
            delta="56%",
            delta_color="normal"
        )

    with col3:
        st.metric(
            "Armada Success",
            "100%",
            delta="174 probes",
            delta_color="normal"
        )

    with col4:
        st.metric(
            "S7 Runs Complete",
            "6/8",
            delta="75%",
            delta_color="normal"
        )

    page_divider()

    # Validated claims
    st.markdown("### ✅ Validated Claims")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        **S3 — Temporal Stability**
        - ✅ Cross-architecture variance σ² = 0.000869
        - ✅ Domain hierarchy: TECH > ANAL > SELF ≈ PHIL > NARR
        - ✅ Tier-3 compression preserves ≥80% fidelity

        **S4 — Mathematical Formalism**
        - ✅ Convergent Reconstruction Theorem
        - ✅ Drift Cancellation Theorem
        - ✅ Triangulation Optimality (29-ship armada)
        """)

    with col2:
        st.markdown("""
        **S7 — Identity Dynamics**
        - ✅ Logarithmic drift bounds: D_t ≤ α log(1 + t) + β
        - ✅ Stability half-life T½ exists
        - ✅ Omega convergence with exponential decay
        - ✅ Spectral decomposition (Keely 3-6-9)

        **S6 — Omega Nova**
        - ✅ Five Pillars tested at scale (174 probes)
        - ✅ Zero Ziggy interventions needed
        """)

    page_divider()

    # Open questions
    st.markdown("### 🔬 Open Questions (Future Work)")
    st.markdown("""
    - **S8:** What is the identity gravity constant γ?
    - **S9:** How does human coupling (HGF) vary across personas?
    - **S10:** Do emergence thresholds (H, G, R, T, B) hold empirically?
    - **S3_EXP_003:** Human validation awaiting raters
    """)


def render_research_checklist():
    """Render research publication readiness checklist."""
    st.markdown("## ✅ Publication Readiness Checklist")
    st.markdown("*Key items for submission readiness*")

    page_divider()

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("### Theoretical Foundation")
        st.markdown("""
| Status | Item |
|--------|------|
| ✅ | S0-S6 Foundation frozen |
| ✅ | Nyquist Kernel formalized |
| ✅ | Five-Pillar synthesis defined |
| ✅ | Identity dynamics equations |
| 🔄 | S7 Identity Dynamics (active) |
| 🔄 | S8 Identity Gravity (design) |
| 🔄 | S9 AVLAR Protocol (seeded) |
| 🔄 | S10 Frame Theory (seeded) |
| 🔄 | S11 Hybrid Emergence (active) |
        """)

        st.markdown("### Empirical Validation")
        st.markdown("""
| Status | Item |
|--------|------|
| ✅ | S3_EXP_001 Single-persona baseline |
| ✅ | S3_EXP_002 Cross-architecture (σ² = 0.000869) |
| 🔄 | S3_EXP_003 Human validation (ready) |
| ✅ | S7_RUN_001-006 Meta-Loop experiments |
| ✅ | S7_RUN_006 Armada (174 probes, 100%) |
| ✅ | S7_RUN_008 Great Recalibration (29 ships) |
| 🔄 | S7_RUN_009 Persona injection (planned) |
        """)

    with col2:
        st.markdown("### Documentation")
        st.markdown("""
| Status | Item |
|--------|------|
| ✅ | NYQUIST_SPEC.md complete |
| ✅ | STACKUP_MAP.md complete |
| ✅ | VALIDATION_STATUS.md complete |
| ✅ | HYPOTHESES_AND_RESULTS.md complete |
| ✅ | MASTER_GLOSSARY.md + decoder rings |
| 🔄 | Tutorial notebooks |
| ⬜ | External reviewer feedback |
        """)

        st.markdown("### Publication Mechanics")
        st.markdown("""
| Status | Item |
|--------|------|
| 🔄 | Abstract drafted |
| 🔄 | Introduction written |
| 🔄 | Methods section |
| ✅ | Key results documented |
| ⬜ | Discussion section |
| ⬜ | References compiled |
| ⬜ | Figures generated |
        """)


def render():
    """Render the Publications page."""
    st.title("📄 Publications & White Papers")
    st.markdown("*Research publication tracking and manuscript management*")

    page_divider()

    # Tab layout for different sections
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "🏆 Key Results",
        "🎯 Perfection Meter",
        "📚 Publication Tracks",
        "📝 Paper Drafts",
        "✅ Readiness Checklist"
    ])

    with tab1:
        render_key_results()

    with tab2:
        render_publication_meter()

    with tab3:
        render_publication_tracks()

    with tab4:
        render_paper_drafts()

    with tab5:
        render_research_checklist()


if __name__ == "__main__":
    render()
