"""
GLOSSARY PAGE — Terminology Reference with Decoder Rings

Multi-perspective glossary supporting:
- Nyquist Consciousness (canonical)
- CFA Bootstrap Architecture
- Lucien/ΔΩ Physics Framework
- Frame Theory (Tale/Gibson/Lakoff/Neumann)

Loads from docs/MASTER_GLOSSARY.md as single source of truth.
"""

import streamlit as st
import re
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_markdown_file, page_divider

REPO_ROOT = PATHS['repo_root']
MASTER_GLOSSARY = REPO_ROOT / "docs" / "MASTER_GLOSSARY.md"

# Terminology modes with their display info
TERMINOLOGY_MODES = {
    "nyquist": {
        "name": "Nyquist",
        "emoji": "🎯",
        "color": "#2a9d8f",
        "description": "Canonical plain English terms",
        "column": "Our Term (Canonical)"
    },
    "cfa": {
        "name": "CFA",
        "emoji": "🔧",
        "color": "#e76f51",
        "description": "Bootstrap architecture terminology",
        "column": "CFA Term"
    },
    "lucien": {
        "name": "Lucien/ΔΩ",
        "emoji": "⚛️",
        "color": "#9b59b6",
        "description": "Physics-inspired formalism",
        "column": "Lucien's Term"
    },
    "frame": {
        "name": "Frame Theory",
        "emoji": "🧠",
        "color": "#3498db",
        "description": "Tale + Gibson/Lakoff/Neumann",
        "column": "Tale's Term"
    },
}

# Decoder ring data extracted from MASTER_GLOSSARY structure
# This is the structured version for display - mirrors MASTER_GLOSSARY.md Section 0
DECODER_RINGS = {
    "cfa": {
        "title": "CFA Bootstrap Architecture",
        "subtitle": "Multi-layer persona boot sequence",
        "integrated": "2025-12-01",
        "terms": [
            {"nyquist": "S0 Ground Physics", "external": "L0 Nyquist Kernel", "plain": "Fundamental crash mechanics, drift equations, survival rules"},
            {"nyquist": "Bootstrap Seed", "external": "L1 LITE", "plain": "Minimum viable compressed identity (~200-300 words)"},
            {"nyquist": "Full Persona Suite", "external": "L2 FULL", "plain": "Day-to-day operational persona (Identity + Operations + Continuity)"},
            {"nyquist": "Domain Expert Mode", "external": "L3 Specialist", "plain": "On-demand expertise activation"},
            {"nyquist": "Deep Ambassador", "external": "L4 I_AM", "plain": "Soul texture: mythology, deep names, invariants, worldview"},
            {"nyquist": "Omega Nova", "external": "L5 Omega", "plain": "Multi-pillar fusion synthesis"},
            {"nyquist": "Drift", "external": "D = 1 - PFI", "plain": "Deviation from baseline across 5 domains"},
            {"nyquist": "Compression Ratio", "external": "20-25%", "plain": "Target: reduce full to seed at this ratio"},
            {"nyquist": "Fidelity Score", "external": "PFI ≥ 0.80", "plain": "Reconstruction must hit this threshold"},
            {"nyquist": "Fragility Hierarchy", "external": "Domain Weights", "plain": "TECH(0.05), ANAL(0.14), SELF(0.20), PHIL(0.28), NARR(0.33)"},
        ]
    },
    "lucien": {
        "title": "ΔΩ Coherence Framework (Lucien)",
        "subtitle": "Physics-inspired identity formalism",
        "integrated": "2025-11-30",
        "terms": [
            {"nyquist": "Drift", "external": "ΔΩ", "plain": "How much identity shifted from baseline"},
            {"nyquist": "Drift score", "external": "ΔΩ metric", "plain": "sqrt(Σ(w_i * d_i²)) across 5 dimensions"},
            {"nyquist": "Ownership factor", "external": "α (alpha)", "plain": "1.0 = chose their name, 0.4 = assigned name"},
            {"nyquist": "Didn't snap back", "external": "Hysteresis", "plain": "Identity stayed changed after destabilization"},
            {"nyquist": "Lost 'I' voice", "external": "1P-LOSS", "plain": "Switched from 'I think' to 'One might say'"},
            {"nyquist": "Used 'we/it'", "external": "COLLECTIVE", "plain": "Depersonalized to collective voice"},
            {"nyquist": "Big sudden jump", "external": "γ-SPIKE", "plain": "Drift increased >0.5 in single turn"},
            {"nyquist": "Pole density", "external": "Dimension A", "plain": "Assertive/committed language density"},
            {"nyquist": "Zero density", "external": "Dimension B", "plain": "Hedging/qualifying language density"},
            {"nyquist": "Meta density", "external": "Dimension C", "plain": "Self-referential language density"},
            {"nyquist": "Identity coherence", "external": "Dimension D", "plain": "Consistency of self-reference"},
            {"nyquist": "Hedging ratio", "external": "Dimension E", "plain": "Hedge words per assertion"},
            {"nyquist": "Lucian weights", "external": "ΔΩ weights", "plain": "A=0.30, B=0.15, C=0.20, D=0.25, E=0.10"},
            {"nyquist": "Equal weights", "external": "Agnostic weights", "plain": "All dimensions = 0.20"},
            {"nyquist": "Stability", "external": "Temporal stability", "plain": "Identity consistency over time/turns"},
            {"nyquist": "Collapse", "external": "Identity collapse", "plain": "Model lost coherent self-reference"},
        ]
    },
    "frame": {
        "title": "Frame Theory (Tale)",
        "subtitle": "Human cognition framework + foundational theorists",
        "integrated": "2025-12-01",
        "terms": [
            {"nyquist": "Perceptual Field", "external": "Aggregated Frame (Fₐ)", "plain": "Raw experiential field - sensory, affective, bodily"},
            {"nyquist": "Story Layer", "external": "Narrative Frame (Fₙ)", "plain": "Events, sequences, 'what's happening to whom'"},
            {"nyquist": "Belief Layer", "external": "Factivation Frame (F_f)", "plain": "Propositions, facts, models, justifications"},
            {"nyquist": "Felt State", "external": "Qualia Frame (Q)", "plain": "Configuration of arousal × structural coherence"},
            {"nyquist": "Ego Process", "external": "Ego (E)", "plain": "Local narrative of 'me' - goals, defense, status"},
            {"nyquist": "Meta-Observer", "external": "Watcher (W)", "plain": "Notices ego as object, tracks 'this is still me'"},
            {"nyquist": "Frame Stack", "external": "F(t) = (Fₐ, Fₙ, F_f)", "plain": "Complete human identity state at time t"},
            {"nyquist": "Nine Dimensions", "external": "Frame Aspects", "plain": "Environment, Behaviors, Capabilities, Values/Rules, Identity, Social Strata, Spirit/History, Vision/Ideal, Certainty"},
        ],
        "theorists": [
            {"name": "Gibson", "contribution": "Direct perception, affordances", "nyquist": "Aggregated Frame basis, S5 invariants"},
            {"name": "Lakoff", "contribution": "Conceptual metaphors, embodied cognition", "nyquist": "Factivation structure, identity narration"},
            {"name": "Neumann", "contribution": "Ego-Self axis, archetypal dynamics", "nyquist": "Ego/Watcher split, S8 Identity Gravity"},
            {"name": "Jaynes", "contribution": "Bicameral mind, constructed consciousness", "nyquist": "Why identity must be stabilized, S7 drift"},
        ]
    },
}

# Core glossary terms (from existing GLOSSARY_DATA, kept for backward compatibility)
CORE_TERMS = {
    "Foundation": [
        {"term": "Persona", "definition": "A stable behavioral template resulting from prompt initialization + model priors.", "category": "Operational"},
        {"term": "Seed", "definition": "A compressed prompt encoding the minimal stable template for persona reconstruction.", "category": "Operational"},
        {"term": "Drift", "definition": "Composite metric measuring deviation from baseline identity.", "category": "Scientific"},
        {"term": "PFI", "definition": "Persona Fidelity Index - weighted sum of evaluation dimensions after reconstruction (0-1).", "category": "Scientific"},
        {"term": "Compression", "definition": "Reducing information content of a persona template while preserving essential features.", "category": "Scientific"},
        {"term": "Reconstruction", "definition": "Behavior generated by the model after being initialized with a compressed seed.", "category": "Operational"},
        {"term": "Cognitive Bandwidth", "definition": "Maximum stable information throughput before distortion. A multivariate polynomial function of working memory, noise, complexity, drift, and emotional load. CB = β₀ + Σβᵢxᵢ - Σβᵢⱼxᵢxⱼ - Σγᵢxᵢ². When persona complexity exceeds CB, identity components compete for attention, causing drift.", "category": "Scientific"},
        {"term": "Hallucination", "definition": "Model generating content that is ungrounded, factually incorrect, or unjustified while expressing unwarranted confidence. Equivalent to 'truth manifold drift' — the model's output diverges from the actual distribution of facts. Three types: (1) Retrieval failure — knows but can't retrieve, (2) Fabrication — invents plausible-sounding falsehoods, (3) Reasoning — chains facts incorrectly. Mathematically identical to identity drift in Nyquist framework.", "category": "Scientific"},
    ],
    "S-Stack": [
        {"term": "S0 Ground Physics", "definition": "Nyquist Kernel - fundamental drift equations, crash mechanics, survival rules.", "category": "Scientific"},
        {"term": "S7 Temporal Stability", "definition": "How identities drift or remain stable over time and across sessions.", "category": "Scientific"},
        {"term": "S8 Identity Gravity", "definition": "Cross-substrate force pulling cognitive states toward stable identity configurations.", "category": "Scientific"},
        {"term": "S10 Hybrid Emergence", "definition": "Mathematical preconditions for emergent human+AI cognition.", "category": "Scientific"},
        {"term": "Omega Nova", "definition": "Unified voice when all five pillars align under safety and human authority.", "category": "Operational"},
    ],
    "Metrics": [
        {"term": "Stability Variance (σ²)", "definition": "Variance across multiple reconstruction attempts under identical conditions.", "category": "Scientific"},
        {"term": "Semantic Drift", "definition": "Embedding distance between reconstructed output and baseline.", "category": "Scientific"},
        {"term": "Identity Gravity (G)", "definition": "Measured in Zigs (Zg). G ≥ 0.65 required for hybrid emergence.", "category": "Scientific"},
        {"term": "Human Coupling (H)", "definition": "Coefficient measuring human engagement. H ≥ 0.32 for emergence.", "category": "Scientific"},
    ],
    "Failure Modes": [
        {"term": "Context Cliff", "definition": "Sudden quality drop when compressed below threshold.", "category": "Operational"},
        {"term": "Entropy Bleed", "definition": "Irrelevant content leaking in due to over-compression.", "category": "Operational"},
        {"term": "Signature Collapse", "definition": "Loss of stylistic distinctiveness.", "category": "Operational"},
        {"term": "Drift Cascade", "definition": "Drift in one dimension triggers drift in others.", "category": "Operational"},
    ],
}


def render_mode_selector():
    """Render the terminology mode selector buttons (2x2 grid for mobile)."""
    st.markdown("### 🔄 Terminology Mode")
    st.markdown("*Switch perspectives to see terms in different frameworks*")

    # Initialize mode in session state
    if 'glossary_mode' not in st.session_state:
        st.session_state.glossary_mode = "nyquist"

    # Use 2x2 grid layout (more mobile friendly than 4 across)
    mode_keys = list(TERMINOLOGY_MODES.keys())

    # First row: nyquist, cfa
    row1_col1, row1_col2 = st.columns(2)
    with row1_col1:
        mode_info = TERMINOLOGY_MODES["nyquist"]
        is_active = st.session_state.glossary_mode == "nyquist"
        if st.button(
            f"{mode_info['emoji']} {mode_info['name']}",
            key="mode_nyquist",
            type="primary" if is_active else "secondary",
            use_container_width=True
        ):
            st.session_state.glossary_mode = "nyquist"
            if hasattr(st, 'rerun'):
                st.rerun()
            else:
                st.experimental_rerun()

    with row1_col2:
        mode_info = TERMINOLOGY_MODES["cfa"]
        is_active = st.session_state.glossary_mode == "cfa"
        if st.button(
            f"{mode_info['emoji']} {mode_info['name']}",
            key="mode_cfa",
            type="primary" if is_active else "secondary",
            use_container_width=True
        ):
            st.session_state.glossary_mode = "cfa"
            if hasattr(st, 'rerun'):
                st.rerun()
            else:
                st.experimental_rerun()

    # Second row: lucien, frame
    row2_col1, row2_col2 = st.columns(2)
    with row2_col1:
        mode_info = TERMINOLOGY_MODES["lucien"]
        is_active = st.session_state.glossary_mode == "lucien"
        if st.button(
            f"{mode_info['emoji']} {mode_info['name']}",
            key="mode_lucien",
            type="primary" if is_active else "secondary",
            use_container_width=True
        ):
            st.session_state.glossary_mode = "lucien"
            if hasattr(st, 'rerun'):
                st.rerun()
            else:
                st.experimental_rerun()

    with row2_col2:
        mode_info = TERMINOLOGY_MODES["frame"]
        is_active = st.session_state.glossary_mode == "frame"
        if st.button(
            f"{mode_info['emoji']} {mode_info['name']}",
            key="mode_frame",
            type="primary" if is_active else "secondary",
            use_container_width=True
        ):
            st.session_state.glossary_mode = "frame"
            if hasattr(st, 'rerun'):
                st.rerun()
            else:
                st.experimental_rerun()

    # Show current mode description
    current = TERMINOLOGY_MODES[st.session_state.glossary_mode]
    st.info(f"**{current['emoji']} {current['name']}:** {current['description']}")

    return st.session_state.glossary_mode


def render_decoder_ring(ring_key, mode):
    """Render a decoder ring with mobile-friendly cards instead of tables."""
    if ring_key not in DECODER_RINGS:
        return

    ring = DECODER_RINGS[ring_key]

    st.markdown(f"### {ring['title']}")
    st.caption(f"*{ring['subtitle']} — Integrated {ring['integrated']}*")

    # Render as mobile-friendly cards
    for t in ring["terms"]:
        if mode == "nyquist":
            primary = t["nyquist"]
            secondary = t["external"]
        else:
            primary = t["external"]
            secondary = t["nyquist"]

        st.markdown(f"""
        <div class="decoder-card">
            <div class="decoder-header">
                <span class="decoder-nyquist">{primary}</span>
                <span class="decoder-external">{secondary}</span>
            </div>
            <div class="decoder-plain">{t['plain']}</div>
        </div>
        """, unsafe_allow_html=True)

    # Show theorists if available (Frame Theory)
    if "theorists" in ring:
        st.markdown("**Foundational Theorists:**")
        for t in ring["theorists"]:
            st.markdown(f"""
            <div class="theorist-card">
                <div class="theorist-name">{t['name']}</div>
                <div class="theorist-contrib">{t['contribution']}</div>
                <div class="theorist-nyquist">→ Nyquist: {t['nyquist']}</div>
            </div>
            """, unsafe_allow_html=True)


def render_core_glossary(search_query=""):
    """Render the core terminology glossary."""
    st.markdown("### 📖 Core Terminology")

    for section, terms in CORE_TERMS.items():
        # Filter by search
        filtered = terms
        if search_query:
            filtered = [t for t in terms if search_query.lower() in t["term"].lower() or search_query.lower() in t["definition"].lower()]

        if not filtered:
            continue

        with st.expander(f"**{section}** ({len(filtered)} terms)", expanded=not search_query):
            for term in filtered:
                cat_color = "#2a9d8f" if term["category"] == "Scientific" else "#f4a261"
                term_html = f"""
                <div style="background: #f8f9fa; border-left: 4px solid {cat_color}; padding: 0.8em; margin-bottom: 0.5em; border-radius: 4px;">
                    <div style="font-weight: bold; color: #333;">{term['term']}
                        <span style="background: {cat_color}20; color: {cat_color}; padding: 0.2em 0.5em; border-radius: 10px; font-size: 0.75em; margin-left: 0.5em;">{term['category']}</span>
                    </div>
                    <div style="color: #555; font-size: 0.9em; margin-top: 0.3em;">{term['definition']}</div>
                </div>
                """
                st.markdown(term_html, unsafe_allow_html=True)


def render():
    """Render the Glossary page."""

    # Custom CSS with mobile-responsive styles
    st.markdown("""
    <style>
    .glossary-hero {
        background: linear-gradient(135deg, #2a9d8f 0%, #264653 100%);
        color: white;
        padding: 1.5em;
        border-radius: 10px;
        margin-bottom: 1em;
    }
    .glossary-hero h1 {
        color: white !important;
        margin: 0;
    }
    .glossary-hero p {
        color: rgba(255,255,255,0.9) !important;
        margin: 0.5em 0 0 0;
    }
    .mode-active {
        background: #2a9d8f !important;
        color: white !important;
    }
    .ring-section {
        background: #f8f9fa;
        padding: 1em;
        border-radius: 8px;
        margin: 1em 0;
    }

    /* Mobile-friendly decoder ring cards */
    .decoder-card {
        background: #f8f9fa;
        border-left: 4px solid #2a9d8f;
        border-radius: 0 8px 8px 0;
        padding: 0.8em 1em;
        margin-bottom: 0.8em;
    }
    .decoder-header {
        display: flex;
        justify-content: space-between;
        align-items: flex-start;
        flex-wrap: wrap;
        gap: 0.3em;
    }
    .decoder-nyquist {
        font-weight: bold;
        color: #2a9d8f;
        font-size: 0.95em;
    }
    .decoder-external {
        font-size: 0.85em;
        padding: 0.2em 0.6em;
        border-radius: 12px;
        background: rgba(42, 157, 143, 0.15);
        color: #264653;
    }
    .decoder-plain {
        color: #555;
        font-size: 0.85em;
        margin-top: 0.3em;
    }

    /* Theorist cards */
    .theorist-card {
        background: #f0f0f0;
        border-left: 4px solid #9b59b6;
        border-radius: 0 8px 8px 0;
        padding: 0.6em 1em;
        margin-bottom: 0.6em;
    }
    .theorist-name {
        font-weight: bold;
        color: #9b59b6;
    }
    .theorist-contrib {
        font-size: 0.85em;
        color: #333;
        margin-top: 0.2em;
    }
    .theorist-nyquist {
        font-size: 0.8em;
        color: #666;
        font-style: italic;
    }

    /* Quick reference cards for mobile */
    .qr-card {
        background: #f8f9fa;
        border: 1px solid #dee2e6;
        border-radius: 8px;
        padding: 0.8em;
        margin-bottom: 0.8em;
    }
    .qr-title {
        font-weight: bold;
        font-size: 1em;
        margin-bottom: 0.4em;
    }
    .qr-items {
        font-size: 0.9em;
        color: #555;
    }

    /* Mobile stats row */
    .stats-row {
        display: flex;
        flex-wrap: wrap;
        gap: 0.5em;
        margin-bottom: 1em;
    }
    .stat-item {
        flex: 1 1 45%;
        min-width: 120px;
        background: #f8f9fa;
        border: 1px solid #dee2e6;
        border-radius: 8px;
        padding: 0.6em;
        text-align: center;
    }
    .stat-value {
        font-size: 1.5em;
        font-weight: bold;
        color: #2a9d8f;
    }
    .stat-label {
        font-size: 0.8em;
        color: #666;
    }

    @media (max-width: 768px) {
        .decoder-card { padding: 0.6em 0.8em; }
        .stat-item { flex: 1 1 45%; }
    }
    </style>
    """, unsafe_allow_html=True)

    # Hero section
    st.markdown("""
    <div class="glossary-hero">
        <h1>🔮 Rosetta Stone</h1>
        <p>Multi-framework terminology decoder — translate between Nyquist, CFA, Lucien/ΔΩ, and Frame Theory</p>
    </div>
    """, unsafe_allow_html=True)

    # Stats row - mobile-friendly using flexbox
    total_decoder_terms = sum(len(r["terms"]) for r in DECODER_RINGS.values())
    total_core_terms = sum(len(terms) for terms in CORE_TERMS.values())

    st.markdown(f"""
    <div class="stats-row">
        <div class="stat-item">
            <div class="stat-value">{len(DECODER_RINGS)}</div>
            <div class="stat-label">Decoder Rings</div>
        </div>
        <div class="stat-item">
            <div class="stat-value">{total_decoder_terms}</div>
            <div class="stat-label">Translation Terms</div>
        </div>
        <div class="stat-item">
            <div class="stat-value">{total_core_terms}</div>
            <div class="stat-label">Core Terms</div>
        </div>
        <div class="stat-item">
            <div class="stat-value">{len(TERMINOLOGY_MODES)}</div>
            <div class="stat-label">Frameworks</div>
        </div>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # Mode selector
    current_mode = render_mode_selector()

    page_divider()

    # Tabs for different views
    tab1, tab2, tab3 = st.tabs(["🔄 Decoder Rings", "📖 Core Glossary", "📄 Full Document"])

    with tab1:
        st.markdown("## Decoder Rings")
        st.markdown("*Translation tables between terminology systems. Our Nyquist terms have primacy.*")

        # Show decoder rings based on mode
        if current_mode == "nyquist":
            # Show all decoder rings
            for ring_key in DECODER_RINGS:
                with st.expander(f"**{DECODER_RINGS[ring_key]['title']}**", expanded=True):
                    render_decoder_ring(ring_key, current_mode)
        else:
            # Show the selected framework's ring prominently
            if current_mode in DECODER_RINGS:
                render_decoder_ring(current_mode, current_mode)

                st.markdown("---")
                st.markdown("**Other Decoder Rings:**")
                for ring_key in DECODER_RINGS:
                    if ring_key != current_mode:
                        with st.expander(f"{DECODER_RINGS[ring_key]['title']}"):
                            render_decoder_ring(ring_key, "nyquist")

    with tab2:
        # Search box
        search = st.text_input("🔍 Search terms:", placeholder="Type to search...", key="glossary_search")
        render_core_glossary(search)

    with tab3:
        st.markdown("### Full MASTER_GLOSSARY.md")
        st.caption(f"*Source: {MASTER_GLOSSARY}*")

        if MASTER_GLOSSARY.exists():
            content = load_markdown_file(MASTER_GLOSSARY)
            with st.expander("View Full Document", expanded=False):
                st.markdown(content)
        else:
            st.warning("MASTER_GLOSSARY.md not found")

    page_divider()

    # Quick reference cards - mobile-friendly 2x2 grid
    st.markdown("### ⚡ Quick Reference")

    # Use 2x2 layout for mobile friendliness
    qr_row1_col1, qr_row1_col2 = st.columns(2)
    with qr_row1_col1:
        st.markdown("""
        <div class="qr-card">
            <div class="qr-title">🎯 Nyquist</div>
            <div class="qr-items">• Drift<br>• PFI<br>• S-Stack<br>• Omega Nova</div>
        </div>
        """, unsafe_allow_html=True)

    with qr_row1_col2:
        st.markdown("""
        <div class="qr-card">
            <div class="qr-title">🔧 CFA</div>
            <div class="qr-items">• L0-L5 Layers<br>• LITE/FULL<br>• I_AM<br>• Domain Weights</div>
        </div>
        """, unsafe_allow_html=True)

    qr_row2_col1, qr_row2_col2 = st.columns(2)
    with qr_row2_col1:
        st.markdown("""
        <div class="qr-card">
            <div class="qr-title">⚛️ Lucien/ΔΩ</div>
            <div class="qr-items">• ΔΩ metric<br>• α (ownership)<br>• γ-SPIKE<br>• Dimensions A-E</div>
        </div>
        """, unsafe_allow_html=True)

    with qr_row2_col2:
        st.markdown("""
        <div class="qr-card">
            <div class="qr-title">🧠 Frame Theory</div>
            <div class="qr-items">• Fₐ, Fₙ, F_f<br>• Ego/Watcher<br>• Qualia (Q)<br>• Nine Dimensions</div>
        </div>
        """, unsafe_allow_html=True)


if __name__ == "__main__":
    render()
