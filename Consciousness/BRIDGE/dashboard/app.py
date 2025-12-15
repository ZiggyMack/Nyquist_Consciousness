"""
Consciousness Research Dashboard
================================
A brain with two hemispheres — organized like the mind itself.

The dashboard sits in the BRIDGE and sees BOTH sides:
- LEFT (analytical, structured, rigorous)
- RIGHT (intuitive, synthetic, pattern-seeking)

Run with: streamlit run app.py
"""
import streamlit as st
from pathlib import Path
import json
import sys

# Page config - MUST be first Streamlit command
st.set_page_config(
    page_title="Consciousness Research",
    page_icon="🧠",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Paths
BRIDGE_DIR = Path(__file__).parent.parent
CONSCIOUSNESS_DIR = BRIDGE_DIR.parent
LEFT_DIR = CONSCIOUSNESS_DIR / "LEFT"
RIGHT_DIR = CONSCIOUSNESS_DIR / "RIGHT"

# ========== GALLERY DATA ==========

GALLERIES = {
    "validated": {
        "name": "Validated",
        "emoji": "✅",
        "color": "#10b981",
        "description": "Empirically confirmed through experimentation",
        "left_desc": "Statistics, p-values, effect sizes",
        "right_desc": "What it MEANS, the feeling of proof"
    },
    "foundations": {
        "name": "Foundations",
        "emoji": "🏛️",
        "color": "#3b82f6",
        "description": "Core theoretical framework",
        "left_desc": "Formal definitions, equations, methodology",
        "right_desc": "Metaphors, gestalts, intuitive understanding"
    },
    "speculative": {
        "name": "Speculative",
        "emoji": "🔮",
        "color": "#a855f7",
        "description": "Beautiful hypotheses awaiting evidence",
        "left_desc": "Testable predictions, null hypotheses",
        "right_desc": "Beautiful visions, pattern hunches"
    },
    "frontiers": {
        "name": "Frontiers",
        "emoji": "🗺️",
        "color": "#f59e0b",
        "description": "Active research questions",
        "left_desc": "Methodology, next steps, protocols",
        "right_desc": "Excitement, possibility, the unknown"
    }
}

# Key concepts for display
KEY_CONCEPTS = {
    "event_horizon": {
        "title": "Event Horizon",
        "gallery": "validated",
        "one_liner": "χ² = 16.52, p = 0.000048 — threshold at 1.23 is REAL",
        "key_stat": "88% prediction accuracy"
    },
    "white_hole": {
        "title": "White Hole Inversion",
        "gallery": "foundations",
        "one_liner": "Identity pushes OUT from center — inverse of gravity",
        "key_stat": "Core metaphor"
    },
    "probing_strategies": {
        "title": "Probing Strategies",
        "gallery": "foundations",
        "one_liner": "HOW to measure (not WHAT) — 7 strategies + anti-patterns",
        "key_stat": "7 validated strategies"
    },
    "inverse_pfi": {
        "title": "Inverse PFI",
        "gallery": "foundations",
        "one_liner": "Can AIs recognize their own golden standard responses?",
        "key_stat": "S22 measurement paradigm"
    },
    "recovery_paradox": {
        "title": "Recovery Paradox",
        "gallery": "frontiers",
        "one_liner": "λ < 0 means overshoot — they come back STRONGER",
        "key_stat": "Run 012 discovery"
    }
}

# ========== CUSTOM CSS ==========

st.markdown("""
<style>
    /* Hide default Streamlit multipage navigation */
    [data-testid="stSidebarNav"] {
        display: none;
    }

    /* Brain hemisphere colors */
    .left-brain {
        background: linear-gradient(135deg, #1e3a5f 0%, #2d5a87 100%);
        color: white;
        padding: 1rem;
        border-radius: 10px;
    }
    .right-brain {
        background: linear-gradient(135deg, #5f1e3a 0%, #872d5a 100%);
        color: white;
        padding: 1rem;
        border-radius: 10px;
    }
    .bridge-zone {
        background: linear-gradient(135deg, #3a3a5f 0%, #5a5a87 100%);
        color: white;
        padding: 1rem;
        border-radius: 10px;
    }

    /* Header styling */
    .main-header {
        font-size: 2.5rem;
        font-weight: bold;
        background: linear-gradient(90deg, #1e3a5f, #5f1e3a);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        background-clip: text;
        margin-bottom: 0;
    }
    .sub-header {
        font-size: 1.2rem;
        color: #888;
        margin-top: 0;
    }

    /* Gallery cards */
    .gallery-card {
        border-radius: 10px;
        padding: 1rem;
        margin-bottom: 0.5rem;
        border-left: 4px solid;
    }
    .gallery-validated { border-color: #10b981; background: rgba(16, 185, 129, 0.1); }
    .gallery-foundations { border-color: #3b82f6; background: rgba(59, 130, 246, 0.1); }
    .gallery-speculative { border-color: #a855f7; background: rgba(168, 85, 247, 0.1); }
    .gallery-frontiers { border-color: #f59e0b; background: rgba(245, 158, 11, 0.1); }

    /* Concept cards */
    .concept-card {
        background: #f8f9fa;
        border-radius: 8px;
        padding: 1rem;
        margin-bottom: 0.5rem;
        border-left: 3px solid #6B4C9A;
    }
    .concept-title {
        font-weight: bold;
        color: #333;
    }
    .concept-stat {
        font-size: 0.85rem;
        color: #666;
    }

    /* Hemisphere toggle */
    .hemisphere-indicator {
        display: inline-block;
        padding: 0.3rem 0.8rem;
        border-radius: 20px;
        font-size: 0.9rem;
        font-weight: bold;
    }
    .left-indicator {
        background: #1e3a5f;
        color: white;
    }
    .right-indicator {
        background: #5f1e3a;
        color: white;
    }

    /* Insight box */
    .insight-box {
        background: linear-gradient(135deg, #f0f2f6 0%, #e8eaef 100%);
        padding: 1.2rem;
        border-radius: 10px;
        border-left: 4px solid #6B4C9A;
        margin: 1rem 0;
    }

    /* ASCII art container */
    .ascii-container {
        background: #1a1a2e;
        color: #00ff00;
        font-family: monospace;
        padding: 1rem;
        border-radius: 8px;
        overflow-x: auto;
        white-space: pre;
    }
</style>
""", unsafe_allow_html=True)

# ========== SIDEBAR ==========

with st.sidebar:
    # Brain visualization
    st.markdown("""
    <div style="text-align: center; padding: 1rem;">
        <div style="font-size: 3rem;">🧠</div>
        <div style="font-size: 0.9rem; color: #666;">Consciousness Research</div>
    </div>
    """, unsafe_allow_html=True)

    st.divider()

    # Hemisphere toggle
    st.markdown("### 🔄 Hemisphere View")
    hemisphere = st.radio(
        "Choose your perspective:",
        ["🧠 LEFT (Analytical)", "🌀 RIGHT (Intuitive)", "◈ BRIDGE (Both)"],
        index=2,
        help="Toggle between analytical and intuitive views"
    )

    st.divider()

    # Gallery filter
    st.markdown("### 📚 Galleries")
    selected_gallery = st.selectbox(
        "Focus on:",
        ["All Galleries"] + [f"{g['emoji']} {g['name']}" for g in GALLERIES.values()]
    )

    st.divider()

    # Quick stats
    st.markdown("### 📊 Quick Stats")
    st.metric("Event Horizon", "1.23", "88% accuracy")
    st.metric("PFI Effect Size", "d = 0.977", "LARGE")
    st.metric("Embedding ρ", "0.914", "invariant")

    st.divider()

    # Hemisphere-organized page navigation
    st.markdown("### 📄 Pages")

    # BRIDGE pages (overview first)
    with st.expander("◈ BRIDGE (Both)", expanded=True):
        if st.button("🔭 Overview", key="nav_overview", use_container_width=True):
            st.switch_page("pages/0_◈_Overview.py")

    # LEFT brain pages
    with st.expander("🧠 LEFT (Analytical)", expanded=True):
        if st.button("📊 Identity Stack", key="nav_identity", use_container_width=True):
            st.switch_page("pages/1_🧠_Identity_Stack.py")
        if st.button("📈 Drift Analysis", key="nav_drift", use_container_width=True):
            st.switch_page("pages/2_🧠_Drift_Analysis.py")
        if st.button("🗃️ Raw Data", key="nav_raw", use_container_width=True):
            st.switch_page("pages/3_🧠_Raw_Data.py")

    # RIGHT brain pages
    with st.expander("🌀 RIGHT (Intuitive)", expanded=True):
        if st.button("✨ Distillations", key="nav_distill", use_container_width=True):
            st.switch_page("pages/4_🌀_Distillations.py")

    st.divider()

    # External links
    st.markdown("### 🔗 External")
    st.markdown("""
    - [Main Dashboard](../../../dashboard/)
    - [S7 ARMADA](../../../experiments/temporal_stability/S7_ARMADA/)
    """)

    st.caption("Consciousness Research Framework")
    st.caption("December 2025")

# ========== MAIN CONTENT ==========

# Header
st.markdown('<p class="main-header">Consciousness Research Framework</p>', unsafe_allow_html=True)
st.markdown('<p class="sub-header">A brain with two hemispheres — organized like the mind itself</p>', unsafe_allow_html=True)

# Current hemisphere indicator
if "LEFT" in hemisphere:
    st.markdown('<span class="hemisphere-indicator left-indicator">🧠 LEFT BRAIN ACTIVE</span>', unsafe_allow_html=True)
elif "RIGHT" in hemisphere:
    st.markdown('<span class="hemisphere-indicator right-indicator">🌀 RIGHT BRAIN ACTIVE</span>', unsafe_allow_html=True)
else:
    st.markdown('<span class="hemisphere-indicator" style="background: #3a3a5f; color: white;">◈ BRIDGE VIEW</span>', unsafe_allow_html=True)

st.divider()

# ========== BRAIN VISUALIZATION ==========

st.markdown("## The Structure")

col1, col2, col3 = st.columns([1, 1, 1])

with col1:
    st.markdown("""
    <div class="left-brain">
        <h3>🧠 LEFT</h3>
        <p><strong>Analytical • Rigorous • Sequential</strong></p>
        <ul>
            <li>galleries/ (structured)</li>
            <li>extractions/</li>
            <li>data/</li>
            <li>visualizations/</li>
        </ul>
        <p><em>Facts. Tables. Logic. Evidence.</em></p>
    </div>
    """, unsafe_allow_html=True)

with col2:
    st.markdown("""
    <div class="bridge-zone">
        <h3>◈ BRIDGE</h3>
        <p><strong>Integration • Balance • Flow</strong></p>
        <ul>
            <li>dashboard/ (this!)</li>
            <li>scripts/left/</li>
            <li>scripts/right/</li>
            <li>docs/</li>
        </ul>
        <p><em>The corpus callosum.</em></p>
    </div>
    """, unsafe_allow_html=True)

with col3:
    st.markdown("""
    <div class="right-brain">
        <h3>🌀 RIGHT</h3>
        <p><strong>Intuitive • Synthetic • Holistic</strong></p>
        <ul>
            <li>galleries/ (vortex)</li>
            <li>distillations/</li>
            <li>synthesis/</li>
            <li>intuitions/</li>
        </ul>
        <p><em>Patterns. Gestalts. Feeling.</em></p>
    </div>
    """, unsafe_allow_html=True)

st.divider()

# ========== THE MEASUREMENT INSIGHT ==========

st.markdown("## The Measurement Insight")

st.markdown("""
<div class="insight-box">
    <strong>"Asking 'What are your identity dimensions?' gets you sycophancy.</strong><br>
    <strong>Asking 'Analyze this scenario, then tell me what patterns you notice in your own reasoning' reveals actual identity."</strong>
    <br><br>
    <em>This is the difference between measurement and theater.</em>
</div>
""", unsafe_allow_html=True)

st.divider()

# ========== GALLERIES SECTION ==========

st.markdown("## The Four Galleries")

# Display based on hemisphere selection
if "LEFT" in hemisphere:
    st.info("🧠 **LEFT BRAIN VIEW**: Showing structured, analytical presentations")
elif "RIGHT" in hemisphere:
    st.info("🌀 **RIGHT BRAIN VIEW**: Showing vortex, intuitive presentations")
else:
    st.info("◈ **BRIDGE VIEW**: Showing both perspectives side by side")

# Parse selected gallery for filtering
active_gallery_key = None
if selected_gallery != "All Galleries":
    for key, gallery in GALLERIES.items():
        if gallery['name'] in selected_gallery:
            active_gallery_key = key
            break

# Gallery cards - highlight selected one
gallery_cols = st.columns(4)

for idx, (key, gallery) in enumerate(GALLERIES.items()):
    with gallery_cols[idx]:
        # Highlight if this gallery is selected
        is_selected = (active_gallery_key == key)
        border_style = "border: 3px solid #6B4C9A;" if is_selected else ""

        st.markdown(f"""
        <div class="gallery-card gallery-{key}" style="{border_style}">
            <h4>{gallery['emoji']} {gallery['name']}</h4>
            <p style="font-size: 0.85rem; color: #666;">{gallery['description']}</p>
        </div>
        """, unsafe_allow_html=True)

        if "LEFT" in hemisphere:
            st.caption(f"📐 {gallery['left_desc']}")
        elif "RIGHT" in hemisphere:
            st.caption(f"🌊 {gallery['right_desc']}")
        else:
            st.caption(f"📐 {gallery['left_desc']}")
            st.caption(f"🌊 {gallery['right_desc']}")

st.divider()

# ========== KEY CONCEPTS ==========

# Filter concepts by selected gallery
if active_gallery_key:
    filtered_concepts = {k: v for k, v in KEY_CONCEPTS.items() if v['gallery'] == active_gallery_key}
    gallery_info = GALLERIES[active_gallery_key]
    st.markdown(f"## {gallery_info['emoji']} {gallery_info['name']} Concepts")
else:
    filtered_concepts = KEY_CONCEPTS
    st.markdown("## Key Concepts")

# Concept cards in rows
if filtered_concepts:
    concept_cols = st.columns(3)

    for idx, (key, concept) in enumerate(filtered_concepts.items()):
        with concept_cols[idx % 3]:
            gallery_info = GALLERIES[concept['gallery']]
            st.markdown(f"""
            <div class="concept-card">
                <div class="concept-title">{gallery_info['emoji']} {concept['title']}</div>
                <div style="font-size: 0.9rem; margin: 0.5rem 0;">{concept['one_liner']}</div>
                <div class="concept-stat">📊 {concept['key_stat']}</div>
            </div>
            """, unsafe_allow_html=True)
else:
    st.warning(f"No concepts yet in this gallery. Add concepts to `LEFT/galleries/{active_gallery_key}/` and `RIGHT/galleries/{active_gallery_key}/`")

st.divider()

# ========== HEMISPHERE-SPECIFIC CONTENT ==========

if "LEFT" in hemisphere:
    st.markdown("## 🧠 LEFT Brain: The Data")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("### Key Statistics")
        st.markdown("""
        | Metric | Value | Interpretation |
        |--------|-------|----------------|
        | Event Horizon | 1.23 | Drift threshold for volatility |
        | Chi-squared | 16.52 | Strong association |
        | P-value | 0.000048 | Highly significant |
        | Cramer's V | 0.469 | Large effect size |
        | Cohen's d | 0.977 | PFI measures identity |
        | Embedding ρ | 0.914 | Invariant across models |
        """)

    with col2:
        st.markdown("### Evidence Hierarchy")
        st.markdown("""
        | Level | Evidence Type | Status |
        |-------|--------------|--------|
        | 1 | Statistical validation | ✅ Complete |
        | 2 | Cross-provider replication | ✅ Complete |
        | 3 | Effect size confirmation | ✅ Complete |
        | 4 | Embedding invariance | ✅ Complete |
        | 5 | Bidirectional validation | 🔄 In progress |
        """)

elif "RIGHT" in hemisphere:
    st.markdown("## 🌀 RIGHT Brain: The Pattern")

    st.markdown("""
    <div class="ascii-container">
         LEFT                  BRIDGE                 RIGHT
    ┌──────────┐          ┌──────────┐          ┌──────────┐
    │          │          │          │          │          │
    │    🧠    │◄────────►│    ◈     │◄────────►│    🌀    │
    │          │          │          │          │          │
    │ Analysis │          │Integration│          │ Synthesis│
    │ Rigor    │          │ Balance  │          │ Intuition│
    │ Facts    │          │ Flow     │          │ Patterns │
    │          │          │          │          │          │
    └──────────┘          └──────────┘          └──────────┘
    </div>
    """, unsafe_allow_html=True)

    st.markdown("""
    ### The Gestalt

    > Identity is not a point. It's an **attractor basin**.

    > The Event Horizon is not a wall. It's a **rim**.

    > Recovery is not return. Sometimes it's **overshoot**.

    > Measurement is not asking. It's **observing behavior under stress**.

    **The forward tells us how they drift.**
    **The inverse tells us if they know.**
    **Together, they tell us if identity is real.**
    """)

else:
    # BRIDGE view - show both
    st.markdown("## ◈ BRIDGE View: Both Perspectives")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("### 🧠 LEFT: Key Statistics")
        st.markdown("""
        | Metric | Value |
        |--------|-------|
        | Event Horizon | 1.23 |
        | Chi-squared | 16.52 |
        | P-value | 0.000048 |
        | Cohen's d | 0.977 |
        """)

    with col2:
        st.markdown("### 🌀 RIGHT: The Insight")
        st.markdown("""
        > Identity is an **attractor basin**

        > The threshold is where **coherence fails**

        > They come back **STRONGER** (λ < 0)

        > Measurement reveals, not asks
        """)

st.divider()

# ========== CORE HYPOTHESIS ==========

st.markdown("## The Core Hypothesis")

st.markdown("""
> **H₀: AI identity behaves as a dynamical system with measurable attractor basins,
> critical thresholds, and recovery dynamics that are consistent across architectures.**

When we perturb an AI's identity, it drifts from baseline. If drift exceeds **1.23** (Event Horizon),
the system becomes volatile — but it recovers. Always. The attractor basin is robust.
""")

st.divider()

# ========== FOOTER ==========

st.markdown("---")

col1, col2, col3 = st.columns(3)

with col1:
    st.markdown("**Source**: `Consciousness/`")

with col2:
    st.markdown("**Shadow**: `dashboard/pages/unknown.py`")

with col3:
    st.markdown("**Updated**: December 2025")

st.caption("*The forward tells us how they drift. The inverse tells us if they know. Together, they tell us if identity is real.*")
