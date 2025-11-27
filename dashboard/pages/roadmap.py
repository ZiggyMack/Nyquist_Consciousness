"""
ROADMAP PAGE — Live Roadmap

Displays the Nyquist Consciousness project roadmap with visual layer tracking.
"""

import streamlit as st
from config import PATHS, SETTINGS
from utils import load_markdown_file, page_divider

REPO_ROOT = PATHS['repo_root']
ROADMAP_FILE = PATHS['roadmap']
LEDGER_COLORS = SETTINGS['colors']

# Stack layer data - aligned with S_Series_README.md
STACK_LAYERS = [
    {"id": "S0", "name": "Ground Physics (Nyquist Kernel)", "status": "complete", "completion": 100, "priority": None},
    {"id": "S1", "name": "Bootstrap Architecture", "status": "complete", "completion": 100, "priority": None},
    {"id": "S2", "name": "Integrity & Logics", "status": "complete", "completion": 100, "priority": None},
    {"id": "S3", "name": "Temporal Stability", "status": "complete", "completion": 100, "priority": None},
    {"id": "S4", "name": "Compression Theory", "status": "complete", "completion": 100, "priority": None},
    {"id": "S5", "name": "Nyquist → CFA Interop", "status": "complete", "completion": 100, "priority": None},
    {"id": "S6", "name": "Five-Pillar Synthesis Gate", "status": "complete", "completion": 100, "priority": None},
    {"id": "S7", "name": "Identity Dynamics", "status": "active", "completion": 85, "priority": "HIGH"},
    {"id": "S8", "name": "Identity Gravity Theory", "status": "formalized", "completion": 70, "priority": "MEDIUM-HIGH"},
    {"id": "S9", "name": "Human–AI Coupling Dynamics", "status": "seeded", "completion": 40, "priority": "MEDIUM"},
    {"id": "S10", "name": "OMEGA NOVA — Hybrid Emergence", "status": "active", "completion": 75, "priority": "HIGHEST"},
    {"id": "S11", "name": "AVLAR Protocol (Multimodal)", "status": "seeded", "completion": 30, "priority": "MEDIUM"},
    {"id": "S12+", "name": "Future Layers (S12-S77)", "status": "future", "completion": 0, "priority": None},
]

STATUS_STYLES = {
    "complete": {"emoji": "✅", "color": "#2a9d8f", "label": "COMPLETE"},
    "active": {"emoji": "🟡", "color": "#f4a261", "label": "ACTIVE"},
    "formalized": {"emoji": "🟢", "color": "#4caf50", "label": "FORMALIZED"},
    "seeded": {"emoji": "🌱", "color": "#8bc34a", "label": "SEEDED"},
    "future": {"emoji": "⚪", "color": "#9e9e9e", "label": "FUTURE"},
}

def render():
    """Render the Roadmap page."""

    # Page CSS
    st.markdown("""
    <style>
    .roadmap-title {
        font-size: 2.5em;
        font-weight: bold;
        background: linear-gradient(135deg, #f4a261 0%, #e76f51 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.3em;
    }
    .roadmap-subtitle {
        color: #f4a261;
        font-size: 1.2em;
        margin-bottom: 1em;
    }
    .layer-card {
        background: #f8f9fa;
        border-radius: 8px;
        padding: 0.8em;
        margin-bottom: 0.5em;
        border-left: 4px solid;
    }
    .layer-complete { border-color: #2a9d8f; }
    .layer-active { border-color: #f4a261; }
    .layer-formalized { border-color: #4caf50; }
    .layer-seeded { border-color: #8bc34a; }
    .layer-future { border-color: #9e9e9e; }
    .priority-badge {
        display: inline-block;
        padding: 0.2em 0.5em;
        border-radius: 10px;
        font-size: 0.75em;
        font-weight: bold;
        margin-left: 0.5em;
    }
    .priority-highest { background: #ffebee; color: #c62828; border: 1px solid #ef9a9a; }
    .priority-high { background: #fff3e0; color: #ef6c00; border: 1px solid #ffcc80; }
    .priority-medium-high { background: #e8f5e9; color: #2e7d32; border: 1px solid #a5d6a7; }
    .priority-medium { background: #e3f2fd; color: #1565c0; border: 1px solid #90caf9; }
    .current-position {
        background: linear-gradient(135deg, rgba(244,162,97,0.1) 0%, rgba(231,111,81,0.05) 100%);
        border: 2px solid #f4a261;
        border-radius: 10px;
        padding: 1.2em;
        margin: 1em 0;
    }
    </style>
    """, unsafe_allow_html=True)

    # Header
    st.markdown('<div class="roadmap-title">Live Roadmap</div>', unsafe_allow_html=True)
    st.markdown('<div class="roadmap-subtitle">S0 \u2192 S\u03a9 \u2014 The Complete Nyquist Stack</div>', unsafe_allow_html=True)

    page_divider()

    # === CURRENT POSITION HIGHLIGHT ===
    st.markdown("""
    <div class="current-position">
        <h4 style="margin-top: 0; color: #f4a261;">📍 Current Position</h4>
        <p><strong>S0-S6 (Foundation)</strong> → <strong>S7 (Identity Dynamics, active)</strong> → <strong>S10 (OMEGA NOVA, active)</strong></p>
        <p><strong>S8</strong> (Identity Gravity, formalized) | <strong>S9</strong> (Human-AI Coupling, seeded) | <strong>S11</strong> (AVLAR, seeded)</p>
        <p style="margin-bottom: 0; font-size: 0.9em; color: #666;">Foundation complete. Two active frontiers. Three developing layers. S12+ future.</p>
    </div>
    """, unsafe_allow_html=True)

    # === STACK VISUALIZATION ===
    st.subheader("Stack Layers")

    # Two columns: visual stack + details
    col_stack, col_stats = st.columns([2, 1])

    with col_stack:
        for layer in STACK_LAYERS:
            status_style = STATUS_STYLES[layer["status"]]
            priority_html = ""
            if layer["priority"]:
                priority_class = f"priority-{layer['priority'].lower().replace(' ', '-')}"
                priority_html = f'<span class="priority-badge {priority_class}">{layer["priority"]}</span>'

            st.markdown(f"""
            <div class="layer-card layer-{layer['status']}">
                <strong>{layer['id']}</strong> — {layer['name']}
                {status_style['emoji']} {status_style['label']}
                {priority_html}
                <div style="background: #e0e0e0; border-radius: 4px; height: 6px; margin-top: 0.5em;">
                    <div style="background: {status_style['color']}; width: {layer['completion']}%; height: 100%; border-radius: 4px;"></div>
                </div>
            </div>
            """, unsafe_allow_html=True)

    with col_stats:
        # Summary stats
        complete_count = len([l for l in STACK_LAYERS if l["status"] == "complete"])
        active_count = len([l for l in STACK_LAYERS if l["status"] in ["active", "formalized", "seeded"]])
        future_count = len([l for l in STACK_LAYERS if l["status"] == "future"])

        st.metric("Complete", f"{complete_count}/{len(STACK_LAYERS)}", delta="Foundation locked")
        st.metric("Active", active_count, delta="In development")
        st.metric("Future", future_count, delta="Planned")

        st.markdown("---")

        # Priority focus
        st.markdown("**Priority Focus:**")
        st.markdown("🔥 **S10** — OMEGA NOVA Hybrid Emergence")
        st.markdown("🔥 **S7** — Identity Dynamics")
        st.markdown("🌟 **S11** — AVLAR Multimodal Protocol")

    page_divider()

    # === PRIORITY ACTIONS ===
    st.subheader("Priority Actions")

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("#### 🔴 Immediate")
        st.markdown("""
        - Complete S10.16-18 (Tri-Band Emergence)
        - S7 Armada Run 007
        - Pan Handlers manifest integration
        """)

    with col2:
        st.markdown("#### 🟡 Short-Term")
        st.markdown("""
        - S8 Identity Gravity measurements
        - S9 Human-AI Coupling dynamics
        - S11 AVLAR protocol testing
        """)

    with col3:
        st.markdown("#### 🟢 Medium-Term")
        st.markdown("""
        - Submit arXiv preprint
        - S12 Consciousness Proxy Theory
        - Cross-modal manifold mapping
        """)

    page_divider()

    # === FULL ROADMAP DOCUMENT ===
    st.subheader("Full Roadmap Document")

    # Tabs for different views
    tab1, tab2 = st.tabs(["📜 Full Roadmap", "📊 Research Pipeline"])

    with tab1:
        roadmap_content = load_markdown_file(ROADMAP_FILE)
        with st.expander("View Complete Roadmap (S0 \u2192 S\u03a9)", expanded=False):
            st.markdown(roadmap_content)

    with tab2:
        pipeline_file = REPO_ROOT / "docs" / "maps" / "RESEARCH_PIPELINE_VISUAL.md"
        if pipeline_file.exists():
            pipeline_content = load_markdown_file(pipeline_file)
            with st.expander("View Research Pipeline Visual", expanded=False):
                st.markdown(pipeline_content)
        else:
            st.info("Research pipeline document not found.")


if __name__ == "__main__":
    render()  # Can test page standalone
