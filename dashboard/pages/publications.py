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
    st.markdown("*Three-track research publication strategy — Updated Dec 2025*")

    page_divider()

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("### 🏛️ Workshop Track")
        st.progress(0.7)
        st.markdown("""
        **Target:** NeurIPS 2025 / AAAI Workshop

        **Focus:** 3 core claims (A, B, E)

        **Status:** Blueprint ready, drafting Q4 2025

        **Key Claims:**
        - PFI validity (ρ = 0.91)
        - Event Horizon threshold (D ≈ 1.23)
        - 82% inherent drift

        📄 See `WHITE-PAPER/blueprints/WORKSHOP_BLUEPRINT.md`
        """)

    with col2:
        st.markdown("### 📜 arXiv Track")
        st.progress(0.85)
        st.markdown("""
        **Target:** arXiv cs.AI, cs.CL

        **Focus:** Full 5 claims + extensions

        **Status:** LaTeX ready, submission Q4 2025

        **Key Sections:**
        - Discovery Era (Runs 006-014)
        - Control-Systems Era (Runs 015-021)
        - 82% inherent drift proof
        - Context damping protocol

        📄 See `WHITE-PAPER/arxiv/README.md`
        """)

    with col3:
        st.markdown("### 🏆 Journal Track")
        st.progress(0.3)
        st.markdown("""
        **Target:** Nature Machine Intelligence / JMLR

        **Focus:** All claims + human validation

        **Status:** Planning, submission Q2-Q3 2026

        **Requirements:**
        - S3_EXP_003 human validation
        - Run 022 dimension probing
        - Independent replication
        - Cross-modal validation (S9)

        📄 See `WHITE-PAPER/blueprints/JOURNAL_BLUEPRINT.md`
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

    # Hero metrics - Updated Dec 2025 with Control-Systems Era
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
            "Evidence Pillars",
            "15",
            delta="B-CRUMBS v2.0",
            delta_color="normal"
        )

    with col3:
        st.metric(
            "Inherent Drift",
            "82%",
            delta="Thermometer Result",
            delta_color="normal"
        )

    with col4:
        st.metric(
            "Context Damping",
            "97.5%",
            delta="Stability Rate",
            delta_color="normal"
        )

    # Second row - additional metrics
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric(
            "S7 Runs Complete",
            "21/22",
            delta="98%",
            delta_color="normal"
        )

    with col2:
        st.metric(
            "Event Horizon",
            "D ≈ 1.23",
            delta="p < 4.8e-5",
            delta_color="normal"
        )

    with col3:
        st.metric(
            "PFI Validity",
            "ρ ≈ 0.91",
            delta="Embedding Invariance",
            delta_color="normal"
        )

    with col4:
        st.metric(
            "Semantic Sensitivity",
            "d ≈ 0.98",
            delta="Effect Size",
            delta_color="normal"
        )

    page_divider()

    # Validated claims - Updated with 5 Minimum Publishable Claims
    st.markdown("### ✅ Minimum Publishable Claims (Peer-Review Ready)")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        **Claim A — PFI is Valid Structured Measurement**
        - ✅ Embedding invariance: ρ ≈ 0.91 (Spearman)
        - ✅ Low-dimensional structure: 43 PCs for 90% variance
        - ✅ Semantic sensitivity: d ≈ 0.98 (effect size)
        - ✅ Paraphrase robustness: 0% above Event Horizon

        **Claim B — Regime Threshold at D ≈ 1.23**
        - ✅ Chi-square validation: p ≈ 4.8e-5
        - ✅ PC space separability: p = 0.0018
        - ✅ Predictive association with stability outcomes

        **Claim C — Damped Oscillator Dynamics**
        - ✅ Settling time (τₛ) measurable
        - ✅ Ringback count quantifiable
        - ✅ Overshoot ratio: d_peak / d_inf
        """)

    with col2:
        st.markdown("""
        **Claim D — Context Damping Reduces Oscillation**
        - ✅ Bare metal stability: 75%
        - ✅ I_AM + research: **97.5%** stability
        - ✅ τₛ improvement: 6.1 → 5.2 turns
        - ✅ Ringbacks reduction: 3.2 → 2.1

        **Claim E — Drift is Mostly Inherent (82%)**
        - ✅ Control (no probing): B→F = 0.399
        - ✅ Treatment (tribunal): B→F = 0.489
        - ✅ Ratio: **82% inherent**
        - ✅ Peak amplified (+84%), destination stable (+23%)

        **The Thermometer Result:**
        > *"Measurement perturbs the path, not the endpoint."*
        """)

    page_divider()

    # Theoretical Breakthroughs from Nova's S7 Review
    st.markdown("### 🧠 Theoretical Breakthroughs (Nova's S7 Review)")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        **Response-Mode Ontology**
        - 43 PCs ≠ identity dimensions to hunt
        - PCs = dominant response modes under perturbation
        - Mode taxonomy: lexical, normative, epistemic, role-shift, collapse

        **Type vs Token Identity**
        - Self-Recognition: 16.7% (worse than chance)
        - Models know WHAT (type-level) not WHICH (token-level)
        - "No autobiographical self — dynamical field that reasserts"

        **Energy vs Coordinate Distinction**
        - Peak drift = turbulence/energy (path)
        - B→F drift = coordinate (destination)
        - "Measurement perturbs the path, not the endpoint"
        """)

    with col2:
        st.markdown("""
        **The Oobleck Effect (Run 013)**
        - Rate-dependent resistance (non-Newtonian)
        - Slow pressure → flows (high drift)
        - Sudden challenge → hardens (low drift)
        - λ: 0.035 → 0.109 with intensity

        **Impedance ≠ Drift**
        - Run 005: Clarity +14% while drift increased
        - Drift ≠ confusion ≠ degradation
        - Drift = state-space displacement

        **Observable Pruning**
        - 12-metric canonical set (of 43 PCs)
        - Layer A: 7 geometry metrics
        - Layer B: 5 semantic metrics
        """)

    # Quotable summary
    st.info("""
**Defensible Quotable Summary:**

> *"Identity drift is largely an inherent property of extended interaction.
> Direct probing does not create it — it excites it.
> Measurement perturbs the path, not the endpoint."*

This is not hype. This is a measured, conservative, *scientifically respectable* conclusion.
    """)

    page_divider()

    # Open questions - Updated Dec 2025
    st.markdown("### 🔬 Next Experiments & Open Questions")
    st.markdown("""
    **Immediate (Run 022):**
    - **Dimension Probing:** Low-dim vs high-dim probes → does k_eff differ?
    - **Architecture Fingerprints:** Claude plateaus? GPT smooth curves? Grok fast snap-back?

    **Near-Term (Q1 2026):**
    - **S3_EXP_003:** Human validation study (external raters)
    - **Cross-Modal (S9):** Audio/visual identity markers
    - **Multiple Personas:** Generalization beyond Nova/Ziggy

    **Theoretical:**
    - **S8:** What is the identity gravity constant γ?
    - **Event Horizon Mechanism:** Why specifically D ≈ 1.23?
    - **Compliance vs Identity Drift:** Can we separate them?
    """)


def render_research_checklist():
    """Render research publication readiness checklist."""
    st.markdown("## ✅ Publication Readiness Checklist")
    st.markdown("*Key items for submission readiness — Updated Dec 2025*")

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
| ✅ | S7 Identity Dynamics (21 runs) |
| 🔄 | S8 Identity Gravity (design) |
| 🔄 | S9 AVLAR Protocol (seeded) |
| ✅ | Event Horizon reframing |
| ✅ | 82% inherent drift theory |
        """)

        st.markdown("### Empirical Validation")
        st.markdown("""
| Status | Item |
|--------|------|
| ✅ | S3_EXP_002 Cross-architecture (σ² = 0.000869) |
| 🔄 | S3_EXP_003 Human validation (ready) |
| ✅ | S7 Discovery Era (Runs 006-014) |
| ✅ | S7 Control-Systems Era (Runs 015-021) |
| ✅ | Settling time protocol (Run 016) |
| ✅ | Context damping (Run 017, 97.5%) |
| ✅ | 82% inherent drift (Run 021) |
| 🔄 | Run 022 Dimension probing (planned) |
        """)

    with col2:
        st.markdown("### Documentation")
        st.markdown("""
| Status | Item |
|--------|------|
| ✅ | MINIMUM_PUBLISHABLE_CLAIMS.md |
| ✅ | THEORY_SECTION.md |
| ✅ | B-CRUMBS.md (15 pillars) |
| ✅ | HYPOTHESES_AND_RESULTS.md (36 hyp) |
| ✅ | Publication blueprints (3 tracks) |
| ✅ | START_HERE.md (reviewer guide) |
| ✅ | arxiv/README.md (paper structure) |
        """)

        st.markdown("### Publication Mechanics")
        st.markdown("""
| Status | Item |
|--------|------|
| ✅ | Abstract drafted (arxiv) |
| ✅ | Paper structure complete |
| ✅ | Key results documented |
| ✅ | Evidence chains established |
| 🔄 | LaTeX sections drafting |
| 🔄 | Figures generation |
| 🔄 | Bibliography compilation |
        """)

    page_divider()

    # Publication Language Guidance
    st.warning("""
**⚠️ Publication Language Guidance (Two Dialects Principle)**

When writing for peer review, use publication-ready terminology:

| ❌ Internal Term | ✅ Publication Term |
|------------------|---------------------|
| "Identity collapse" | "Regime transition" |
| "Platonic coordinates" | "Attractor basin consistency" |
| "Event Horizon = failure" | "Attractor competition threshold" |
| "Collapse" | "Basin exit" |

**Core framing:** *"You're doing dynamical systems analysis, not ontology claims — and that restraint is what keeps this credible."*

See `docs/MASTER_GLOSSARY.md` Section 10 for full terminology registers.
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
