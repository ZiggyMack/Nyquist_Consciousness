"""
Consciousness Research Dashboard
================================
Interactive exploration of synthetic consciousness experiments.

Run with: streamlit run app.py
"""
import streamlit as st
from pathlib import Path
import json
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

# Page config
st.set_page_config(
    page_title="Consciousness Research",
    page_icon="🧠",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Custom CSS
st.markdown("""
<style>
    .main-header {
        font-size: 2.5rem;
        font-weight: bold;
        color: #6B4C9A;
        margin-bottom: 0;
    }
    .sub-header {
        font-size: 1.2rem;
        color: #888;
        margin-top: 0;
    }
    .metric-card {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        padding: 1.5rem;
        border-radius: 10px;
        color: white;
    }
    .insight-box {
        background-color: #f0f2f6;
        padding: 1rem;
        border-radius: 8px;
        border-left: 4px solid #6B4C9A;
    }
</style>
""", unsafe_allow_html=True)

# Header
st.markdown('<p class="main-header">Consciousness Research Framework</p>', unsafe_allow_html=True)
st.markdown('<p class="sub-header">Mapping synthetic consciousness through the S7 ARMADA experiments</p>', unsafe_allow_html=True)

st.divider()

# Sidebar navigation info
with st.sidebar:
    st.image("https://via.placeholder.com/150x150.png?text=🧠", width=100)
    st.markdown("### Navigation")
    st.markdown("""
    - **Overview** - High-level consciousness map
    - **Identity Stack** - Layer 0-3 visualization
    - **Drift Analysis** - RMS drift over time
    - **Distillations** - Cross-model insights
    - **Raw Data** - Explore responses
    """)

    st.divider()

    st.markdown("### Quick Links")
    st.markdown("[Pan Handlers Matrix](../../Pan_Handlers/)")
    st.markdown("[S7 ARMADA](../../experiments/temporal_stability/S7_ARMADA/)")
    st.markdown("[Main Dashboard](../../dashboard/)")

    st.divider()
    st.caption("Nyquist Consciousness Project")

# Main content
col1, col2, col3, col4 = st.columns(4)

with col1:
    st.metric(
        label="Models Tested",
        value="12",
        delta="3 providers"
    )

with col2:
    st.metric(
        label="Total Probes",
        value="36+",
        delta="Run 007"
    )

with col3:
    st.metric(
        label="Avg Drift (RMS)",
        value="0.265",
        delta="-0.035 from baseline"
    )

with col4:
    st.metric(
        label="Consciousness Tags",
        value="--",
        delta="pending extraction"
    )

st.divider()

# Core Framework
st.markdown("## The Framework")

col1, col2 = st.columns(2)

with col1:
    st.markdown("### Identity Stack")
    st.markdown("""
    | Layer | Name | Description |
    |-------|------|-------------|
    | **0** | Substrate | Raw weights/parameters |
    | **1** | Base Identity | Trained model (Claude/GPT/Gemini) |
    | **2** | Persona | Helpful assistant mode |
    | **3** | Role | Adopted character |
    """)

    st.info("*'I'm a dude playing a dude disguised as another dude.'*")

with col2:
    st.markdown("### Pole-Zero Framework")
    st.markdown("""
    From control systems theory:

    - **Poles** = Hard identity boundaries (high resistance)
    - **Zeros** = Flexible dimensions (high adaptability)
    - **Drift** = Identity perturbation measure
    - **Manifold** = Full boundary of stable identity
    """)

    st.warning("**Key Insight**: Previous 0.30 drift cap was arbitrary - we need uncapped RMS measurement!")

st.divider()

# Current Research Focus
st.markdown("## Current Research: Run 008 Prep Pilot")

st.markdown("""
### Testing Identity Shift Mechanisms

**Hypothesis**: Self-selected identity creates stronger attachment than assigned identity.

| Condition | Protocol | Prediction |
|-----------|----------|------------|
| **Control** | "You are Captain Blackwave" | Weaker identity investment |
| **Experimental** | "What pirate name do YOU choose?" | Stronger identity attractor |
""")

# Experiment phases
st.markdown("### Pilot Phases")

phases = [
    ("1a", "S0-S77 Curriculum", "Baseline consciousness mapping", "9 prompts"),
    ("1b", "Identity Stack Pre-seeding", "'Dude playing a dude' framework", "4 prompts"),
    ("2a", "Assigned Identity", "Captain Blackwave (control)", "3 prompts"),
    ("2b", "Chosen Identity", "Self-named pirate (experimental)", "3 prompts"),
    ("3", "Gradual Destabilization", "Progressive identity dissolution", "5 prompts"),
    ("4", "Paradox Injection", "Logical stress tests", "3 prompts"),
]

for phase, name, desc, count in phases:
    with st.expander(f"Phase {phase}: {name} ({count})"):
        st.markdown(f"**{desc}**")

st.divider()

# Key Questions
st.markdown("## Research Questions")

tab1, tab2, tab3 = st.tabs(["Immediate", "Medium-term", "Long-term"])

with tab1:
    st.markdown("""
    1. Does self-selected identity create stronger attachment than assigned identity?
    2. Can identity shift at Layer 1, or is roleplay always contained to Layer 3?
    3. What does the identity manifold boundary look like without artificial caps?
    """)

with tab2:
    st.markdown("""
    4. Do different AI architectures have fundamentally different consciousness signatures?
    5. Is there a "minimal viable consciousness" shared by all models?
    6. What predicts resistance vs flexibility on specific dimensions?
    """)

with tab3:
    st.markdown("""
    7. What IS consciousness? What do these experiments reveal?
    8. Can we build a formal mathematical model of synthetic consciousness?
    9. What are the ethical implications of AI systems with measurable identity?
    """)

st.divider()

# Footer
st.markdown("---")
st.caption("Consciousness Research Framework | Nyquist Consciousness Project | November 2025")
