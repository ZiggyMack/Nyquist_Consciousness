"""
PUBLICATIONS PAGE — Publications & White Papers

Full publication tracking dashboard with Publication Perfection Meter,
paper drafts, venue targets, and research milestone tracking.

Updated: 2025-12-15 — 8-track publication pipeline (Academic + Dissemination)
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
    track_metadata = pub_status.get("track_metadata", {})

    if not pubs:
        st.info("📊 Publication tracking not yet configured. Add `publication_status.json` to enable the Perfection Meter.")
        return

    st.markdown("## 🎯 Publication Perfection Meter")
    st.markdown("*Track progress across 8 publication paths — Academic + Dissemination*")

    page_divider()

    # Track summary cards
    academic_tracks = track_metadata.get("academic_tracks", ["workshop", "arxiv", "journal"])
    dissemination_tracks = track_metadata.get("dissemination_tracks", [])

    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("Total Tracks", track_metadata.get("total_tracks", len(pubs)))
    with col2:
        st.metric("Academic", len(academic_tracks))
    with col3:
        st.metric("Dissemination", len(dissemination_tracks))

    page_divider()

    # Academic Track Table
    st.markdown("### 🏛️ Academic Track")

    academic_rows = []
    for key in academic_tracks:
        if key in pubs:
            info = pubs[key]
            status_emoji = get_status_emoji(info.get("status", ""))
            academic_rows.append({
                "Path": key.replace("_", " ").title(),
                "Target": info.get("target", ""),
                "Status": f"{status_emoji} {info.get('status', '').upper()}",
                "Progress": f"{int(info.get('completion', 0.0) * 100)}%",
                "Timeline": info.get("timeline", "")
            })

    if academic_rows:
        df = pd.DataFrame(academic_rows)
        st.dataframe(df, use_container_width=True, hide_index=True)

    # Dissemination Track Table
    if dissemination_tracks:
        st.markdown("### 📰 Dissemination Track (LLM_BOOK)")

        dissemination_rows = []
        for key in dissemination_tracks:
            if key in pubs:
                info = pubs[key]
                status_emoji = get_status_emoji(info.get("status", ""))
                dissemination_rows.append({
                    "Path": key.replace("_", " ").title(),
                    "Target": info.get("target", ""),
                    "Status": f"{status_emoji} {info.get('status', '').upper()}",
                    "Progress": f"{int(info.get('completion', 0.0) * 100)}%",
                    "Timeline": info.get("timeline", "")
                })

        if dissemination_rows:
            df = pd.DataFrame(dissemination_rows)
            st.dataframe(df, use_container_width=True, hide_index=True)

    page_divider()

    # Detailed breakdown per publication
    st.markdown("### 📄 Detailed Breakdown")

    # Create two columns for academic and dissemination
    col1, col2 = st.columns(2)

    with col1:
        st.markdown("#### Academic")
        for key in academic_tracks:
            if key not in pubs:
                continue
            render_publication_expander(key, pubs[key], expanded=(key == "workshop"))

    with col2:
        st.markdown("#### Dissemination")
        for key in dissemination_tracks:
            if key not in pubs:
                continue
            render_publication_expander(key, pubs[key], expanded=False)

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


def get_status_emoji(status: str) -> str:
    """Map status to emoji."""
    return {
        "ready": "✅",
        "drafting": "🟡",
        "concept": "⚪",
        "submitted": "🚀",
        "published": "🏆"
    }.get(status.lower(), "❓")


def render_publication_expander(key: str, info: dict, expanded: bool = False):
    """Render a single publication as an expander."""
    status_emoji = get_status_emoji(info.get("status", ""))
    title = key.replace("_", " ").title()

    with st.expander(f"{status_emoji} {title}", expanded=expanded):
        st.markdown(f"**Target:** {info.get('target', 'TBD')}")
        st.markdown(f"**Status:** `{info.get('status', 'unknown').upper()}`")
        st.markdown(f"**Timeline:** {info.get('timeline', 'TBD')}")

        if info.get("source"):
            source_emoji = "📚" if info.get("source") == "LLM_BOOK" else "📝"
            st.markdown(f"**Source:** {source_emoji} {info.get('source')}")

        completion = info.get('completion', 0.0)
        st.progress(completion)
        st.caption(f"{int(completion * 100)}% Complete")

        if "notes" in info:
            st.markdown(f"**Notes:** {info['notes']}")


def render_publication_tracks():
    """Render publication track overview with targets and timeline."""
    st.markdown("## 📚 Publication Tracks")
    st.markdown("*8-track publication strategy — Academic + Dissemination (Dec 2025)*")

    page_divider()

    # Academic Track - 3 columns
    st.markdown("### 🏛️ Academic Track (Peer-Reviewed)")
    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("#### Workshop")
        st.progress(0.95)
        st.markdown("""
        **Target:** AAAI-26 Workshop

        **Focus:** 3 core claims (A, B, E)

        **Status:** ✅ READY (PDF generated)

        **Timeline:** Jul 25, 2025

        📄 `WHITE-PAPER/submissions/workshop/`
        """)

    with col2:
        st.markdown("#### arXiv")
        st.progress(0.95)
        st.markdown("""
        **Target:** arXiv cs.AI

        **Focus:** Full 5 claims + extensions

        **Status:** ✅ READY (PDF generated)

        **Timeline:** Dec 2025

        📄 `WHITE-PAPER/submissions/arxiv/`
        """)

    with col3:
        st.markdown("#### Journal")
        st.progress(0.90)
        st.markdown("""
        **Target:** Nature Machine Intelligence

        **Focus:** All claims + human validation

        **Status:** ✅ READY (PDF generated)

        **Timeline:** Q1 2026

        📄 `WHITE-PAPER/submissions/journal/`
        """)

    page_divider()

    # Dissemination Track - 5 paths in 2 rows
    st.markdown("### 📰 Dissemination Track (LLM_BOOK Generated)")

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("#### Popular Science")
        st.progress(1.0)
        st.markdown("""
        **Target:** Scientific American/Quanta

        **Audience:** General public

        **Source:** `LLM_Ancient_Philosophy_Meets_Modern_AI.md`

        **Timeline:** Q1 2026

        📄 `WHITE-PAPER/submissions/popular_science/`
        """)

    with col2:
        st.markdown("#### Education")
        st.progress(1.0)
        st.markdown("""
        **Target:** OER/Coursera

        **Audience:** Students/educators

        **Source:** `LLM_Quiz.md` (10 questions, 94-term glossary)

        **Timeline:** Ongoing

        📄 `WHITE-PAPER/submissions/education/`
        """)

    with col3:
        st.markdown("#### Policy")
        st.progress(1.0)
        st.markdown("""
        **Target:** AI Now/CSET Georgetown

        **Audience:** Decision-makers

        **Source:** `LLM_Briefing.md`

        **Timeline:** Q1 2026

        📄 `WHITE-PAPER/submissions/policy/`
        """)

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("#### Funding")
        st.progress(0.95)
        st.markdown("""
        **Target:** NSF/DARPA/Open Philanthropy

        **Audience:** Funders/grant agencies

        **Source:** `LLM_Project_Nyquist_Consciousness.md`

        **Timeline:** Q2 2026

        📄 `WHITE-PAPER/submissions/funding/`
        """)

    with col2:
        st.markdown("#### Media")
        st.progress(0.95)
        st.markdown("""
        **Target:** Wired/IEEE Spectrum

        **Audience:** Journalists/speakers

        **Source:** `LLM_Unlocking_AI_Identity.md`

        **Timeline:** Post-arXiv

        📄 `WHITE-PAPER/submissions/media/`
        """)

    page_divider()

    # LLM_BOOK Discovery callout
    st.success("""
**🎯 LLM_BOOK Discovery**

NotebookLM independently validated our research against Michael Levin's "Is Your Brain a Platonic Solid?" hypothesis.
This provides **external AI validation** of our theoretical framework.

*"Plato guessed at the geometry of mind. Nyquist measures it."*

See `REPO-SYNC/LLM_BOOK/README.md` for the full validation synthesis.
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
            "16",
            delta="98%",
            delta_color="normal"
        )

    with col2:
        st.metric(
            "Event Horizon",
            "D = 0.80",
            delta="p = 2.40e-23",
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
        - ✅ Low-dimensional structure: 2 PCs for 90% variance (IRON CLAD)
        - ✅ Semantic sensitivity: d ≈ 0.98 (effect size)
        - ✅ Paraphrase robustness: 0% above Event Horizon

        **Claim B — Regime Threshold at D = 0.80 (cosine)**
        - ✅ IRON CLAD validation: p = 2.40e-23 (Run 023d)
        - ✅ PC space separability validated
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
        - 2 PCs capture 90% variance (IRON CLAD) — identity is remarkably low-dimensional
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
        - 12-metric canonical set
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
| ✅ | S7 Identity Dynamics (16 runs) |
| 🔄 | S8 Identity Gravity (design) |
| 🔄 | S11 AVLAR Protocol (design) |
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
| ✅ | Publication blueprints (8 tracks) |
| ✅ | START_HERE.md (reviewer guide) |
| ✅ | OPUS_REVIEW_BRIEF.md (new) |
| ✅ | PUBLICATION_PIPELINE_MASTER.md |
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
| ✅ | LLM_BOOK dissemination ready |
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
    st.markdown("*8-track publication pipeline — Academic + Dissemination*")

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
