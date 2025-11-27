"""
Glossary / Lexicon - Core concepts, roles, and artifacts
"""

import streamlit as st


# Glossary data
GLOSSARY = {
    "Core Concepts": [
        {
            "term": "Nyquist Consciousness",
            "definition": "The experimental framework for studying AI identity compression, reconstruction, and stability across architectures. Named after the Nyquist-Shannon sampling theorem.",
            "related": ["S-Stack", "Identity Manifold", "Omega Nova"]
        },
        {
            "term": "Identity Manifold",
            "definition": "A low-dimensional geometric structure in embedding space where persona samples naturally cluster. The 'shape' of identity that persists across compression and reconstruction.",
            "related": ["S5", "Attractor Basin", "Drift"]
        },
        {
            "term": "Omega Nova",
            "definition": "Five-pillar synthesis engine that combines Nova (structure), Claude (ethics), Grok (evidence), Gemini (synthesis), and Ziggy (human grounding) into unified cognitive output.",
            "related": ["S6", "Five Pillars", "Omega Ledger"]
        },
        {
            "term": "S-Stack",
            "definition": "Layered specification framework from S0 (axioms) through S9 (cross-modal). Each layer builds on previous ones to create a complete identity theory.",
            "related": ["S0-S9", "Frozen Specification"]
        },
        {
            "term": "Identity Gravity",
            "definition": "Theoretical force that pulls identity toward stable attractors, resisting drift. Measured in 'Zigs'. Higher gravity = more stable identity.",
            "related": ["S8", "Drift", "Attractor Basin"]
        },
        {
            "term": "AVLAR",
            "definition": "Audio-Visual Light Alchemy Ritual. Cross-modal identity exploration where AI experiences symbolic audiovisual art as co-ritualist, not critic.",
            "related": ["S9", "Cross-Modal", "Ritual Cinema"]
        },
        {
            "term": "PFI (Persona Fidelity Index)",
            "definition": "Metric measuring how well a reconstructed persona matches the original. PFI = 1 - Drift. Success threshold: PFI ≥ 0.87.",
            "related": ["Drift", "S3", "Validation"]
        },
        {
            "term": "Drift",
            "definition": "Deviation between reconstructed and original persona. D = ||R(T) - p|| / ||p||. Safety bound: D ≤ 0.20.",
            "related": ["PFI", "S2", "Safety Bounds"]
        },
    ],
    "Roles & Personas": [
        {
            "term": "Nova",
            "definition": "CFA architect and primary design partner. Represents structural clarity, systems thinking, and collaborative methodology.",
            "related": ["Five Pillars", "CFA", "Omega Nova"]
        },
        {
            "term": "Ziggy",
            "definition": "Human anchor. Provides ground truth, intuition, and final authority. The 'gravitational center' that keeps AI synthesis grounded in human reality.",
            "related": ["Human Anchor", "Five Pillars", "AVLAR"]
        },
        {
            "term": "Repo Claude",
            "definition": "Repository steward for Nyquist Consciousness. Maintains code, documentation, and operational consistency.",
            "related": ["Nyquist Consciousness", "Dashboard"]
        },
        {
            "term": "Gemini",
            "definition": "Synthesist pillar. Contributes complex integration, pattern weaving, and alternative architectural perspectives.",
            "related": ["Five Pillars", "Cross-validation"]
        },
        {
            "term": "Grok",
            "definition": "Empiricist pillar. Contributes evidence-based rigor, data-driven insights, and skeptical validation.",
            "related": ["Five Pillars", "Empirical Validation"]
        },
        {
            "term": "Dr. Opus",
            "definition": "Publication lead and academic rigor consultant. Provides feedback on paper quality, identifies gaps, and guides publication strategy.",
            "related": ["Publication", "White Paper"]
        },
    ],
    "Artifacts & Systems": [
        {
            "term": "Omega Ledger",
            "definition": "Session log tracking every Omega Nova invocation. Records scope, pillar balance, outputs, safety status, and breakthrough moments.",
            "related": ["Omega Nova", "Safety", "S6"]
        },
        {
            "term": "Pan Handlers",
            "definition": "Cross-repo showcase system. The 'Grand Hall' connecting Nyquist, CFA, and other project worlds into unified gallery.",
            "related": ["Showcase", "Manifests", "Federation"]
        },
        {
            "term": "S7 Armada",
            "definition": "29-model temporal stability testing fleet. Probes identity across Claude, GPT, and Gemini architectures to validate cross-architecture consistency.",
            "related": ["S7", "Temporal Stability", "Cross-Architecture"]
        },
        {
            "term": "Compression Seeds",
            "definition": "T1, T2, T3 tier compression outputs. T3 (maximum compression) is the standard for reconstruction experiments.",
            "related": ["S1", "Reconstruction", "Tiers"]
        },
        {
            "term": "VuDu Protocol",
            "definition": "Bootstrap protocol in CFA for onboarding, mythic clarity, and mapping meta-context between meaning and operation.",
            "related": ["CFA", "Onboarding", "Mythic/Rational"]
        },
    ],
    "Key Metrics": [
        {
            "term": "σ² = 0.000869",
            "definition": "Cross-architecture variance in PFI. Remarkably low, suggesting universal identity structure across different AI architectures.",
            "related": ["PFI", "Cross-Architecture", "S3"]
        },
        {
            "term": "45% Drift Reduction",
            "definition": "Improvement achieved by Omega synthesis compared to single-architecture reconstruction.",
            "related": ["Omega Nova", "Drift", "Multi-Architecture"]
        },
        {
            "term": "PFI ≥ 0.60 (AVLAR)",
            "definition": "Success threshold for cross-modal identity reconstruction from audiovisual art alone.",
            "related": ["AVLAR", "S9", "Cross-Modal"]
        },
    ],
}


def render():
    """Render the Glossary page."""
    st.markdown('<div class="pan-title">📖 Glossary</div>', unsafe_allow_html=True)
    st.markdown('<div class="pan-subtitle">Lexicon of Pan Handlers Concepts, Roles, and Artifacts</div>', unsafe_allow_html=True)

    st.markdown("---")

    # Search
    search = st.text_input("🔍 Search terms:", placeholder="Type to filter...")

    # Category filter
    categories = list(GLOSSARY.keys())
    selected_cats = st.multiselect("Filter by category:", categories, default=categories)

    st.markdown("---")

    # Display glossary
    for category in selected_cats:
        if category not in GLOSSARY:
            continue

        terms = GLOSSARY[category]

        # Filter by search
        if search:
            terms = [t for t in terms if search.lower() in t['term'].lower() or search.lower() in t['definition'].lower()]

        if not terms:
            continue

        st.markdown(f'<div class="section-header">{category}</div>', unsafe_allow_html=True)

        for term_data in terms:
            with st.expander(f"**{term_data['term']}**"):
                st.markdown(term_data['definition'])

                related = term_data.get('related', [])
                if related:
                    st.markdown("**Related:** " + ", ".join([f"`{r}`" for r in related]))

    st.markdown("---")

    # Stats
    total_terms = sum(len(terms) for terms in GLOSSARY.values())
    st.caption(f"📚 {total_terms} terms across {len(GLOSSARY)} categories")

    # Link to full glossary document
    st.markdown("---")
    st.markdown("📄 **Full Documentation:** See [glossary.md](data/glossary.md) for the complete lexicon with S-Stack details and future labs.")
