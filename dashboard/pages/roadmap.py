"""
ROADMAP PAGE — Live Roadmap

Displays the Nyquist Consciousness project roadmap with visual layer tracking.
"""

import streamlit as st
import plotly.graph_objects as go
from config import PATHS, SETTINGS
from utils import load_markdown_file, page_divider

REPO_ROOT = PATHS['repo_root']
ROADMAP_FILE = PATHS['roadmap']
LEDGER_COLORS = SETTINGS['colors']

# Stack layer data - aligned with S_Series_README.md and NYQUIST_ROADMAP.md
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
    {"id": "S9", "name": "AVLAR Protocol (Multimodal)", "status": "seeded", "completion": 40, "priority": "MEDIUM"},
    {"id": "S10", "name": "Human Cognition (Frame Theory)", "status": "seeded", "completion": 50, "priority": "MEDIUM"},
    {"id": "S11", "name": "OMEGA NOVA — Hybrid Emergence", "status": "active", "completion": 75, "priority": "HIGHEST"},
    {"id": "S12", "name": "Consciousness Proxy Theory", "status": "future", "completion": 0, "priority": None},
    {"id": "S13", "name": "Field Consistency Proofs", "status": "future", "completion": 0, "priority": None},
    {"id": "S14", "name": "Composite Persona Dynamics", "status": "future", "completion": 0, "priority": None},
    {"id": "S15", "name": "Cognitive Lattice Structures", "status": "future", "completion": 0, "priority": None},
    {"id": "S16", "name": "Meta-Field Integration", "status": "future", "completion": 0, "priority": None},
    {"id": "S17-S76", "name": "Reserved Expansion Layers", "status": "future", "completion": 0, "priority": None},
    {"id": "S77", "name": "Archetype Engine (AI Synthesis)", "status": "future", "completion": 0, "priority": "ULTIMATE"},
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
    .priority-ultimate { background: linear-gradient(135deg, #ffd700 0%, #ff6b6b 50%, #9b59b6 100%); color: #000; border: 2px solid gold; font-weight: bold; }
    .current-position {
        background: linear-gradient(135deg, rgba(244,162,97,0.1) 0%, rgba(231,111,81,0.05) 100%);
        border: 2px solid #f4a261;
        border-radius: 10px;
        padding: 1.2em;
        margin: 1em 0;
    }
    </style>
    """, unsafe_allow_html=True)

    # === HEADER ROW: Title (left) + Current Position (right) ===
    header_col1, header_col2 = st.columns([1, 1])

    with header_col1:
        st.markdown('<div class="roadmap-title">Live Roadmap</div>', unsafe_allow_html=True)
        st.markdown('<div class="roadmap-subtitle">S0 → SΩ — The Complete Nyquist Stack</div>', unsafe_allow_html=True)

    with header_col2:
        st.markdown("""
        <div class="current-position">
            <h4 style="margin-top: 0; color: #f4a261;">📍 Current Position</h4>
            <p style="font-size: 0.9em;"><strong>S0-S6 (Foundation)</strong> → <strong>S7 (Identity Dynamics, active)</strong> → <strong>S11 (OMEGA NOVA, active)</strong></p>
            <p style="font-size: 0.9em;"><strong>S8</strong> (Identity Gravity, formalized) | <strong>S9</strong> (AVLAR, seeded) | <strong>S10</strong> (Frame Theory, seeded)</p>
            <p style="font-size: 0.9em;"><strong>S12-S76</strong> (Future Frontier) → <strong style="color: gold;">S77 Archetype Engine</strong> (Ultimate Destination)</p>
            <p style="margin-bottom: 0; font-size: 0.85em; color: #555;">Foundation complete. Frame Theory (Tale) integrated. Two active frontiers.</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === GANTT-STYLE PROGRESSION CHART ===
    st.markdown("### 📊 Stack Progression Timeline")

    # Create Gantt-style horizontal bar chart showing layer progression
    gantt_data = []
    colors = []
    status_colors = {
        "complete": "#2a9d8f",
        "active": "#f4a261",
        "formalized": "#4caf50",
        "seeded": "#8bc34a",
        "future": "#9e9e9e"
    }

    for layer in STACK_LAYERS:
        gantt_data.append({
            "layer": layer["id"],
            "name": layer["name"][:30] + "..." if len(layer["name"]) > 30 else layer["name"],
            "completion": layer["completion"],
            "status": layer["status"]
        })
        colors.append(status_colors.get(layer["status"], "#9e9e9e"))

    # Create horizontal bar chart
    fig = go.Figure()

    # Add completion bars
    fig.add_trace(go.Bar(
        y=[d["layer"] for d in gantt_data],
        x=[d["completion"] for d in gantt_data],
        orientation='h',
        marker=dict(
            color=colors,
            line=dict(color='rgba(255,255,255,0.3)', width=1)
        ),
        text=[f"{d['completion']}%" for d in gantt_data],
        textposition='inside',
        textfont=dict(color='white', size=10),
        hovertemplate="<b>%{y}</b><br>Progress: %{x}%<extra></extra>"
    ))

    # Add background bars showing remaining work
    fig.add_trace(go.Bar(
        y=[d["layer"] for d in gantt_data],
        x=[100 - d["completion"] for d in gantt_data],
        orientation='h',
        marker=dict(color='rgba(200,200,200,0.2)'),
        hoverinfo='skip',
        showlegend=False
    ))

    fig.update_layout(
        barmode='stack',
        height=500,
        margin=dict(l=80, r=20, t=20, b=40),
        xaxis=dict(
            title="Completion %",
            range=[0, 100],
            tickvals=[0, 25, 50, 75, 100],
            gridcolor='rgba(128,128,128,0.2)'
        ),
        yaxis=dict(
            title="",
            autorange="reversed",  # S0 at top
            tickfont=dict(size=11)
        ),
        paper_bgcolor='rgba(0,0,0,0)',
        plot_bgcolor='rgba(0,0,0,0)',
        showlegend=False,
        font=dict(color='#333')
    )

    st.plotly_chart(fig, use_container_width=True)

    # Legend for status colors
    legend_cols = st.columns(5)
    status_legend = [
        ("✅ Complete", "#2a9d8f"),
        ("🟡 Active", "#f4a261"),
        ("🟢 Formalized", "#4caf50"),
        ("🌱 Seeded", "#8bc34a"),
        ("⚪ Future", "#9e9e9e")
    ]
    for col, (label, color) in zip(legend_cols, status_legend):
        with col:
            st.markdown(f'<span style="color:{color}">●</span> {label}', unsafe_allow_html=True)

    page_divider()

    # === STACK VISUALIZATION ===
    st.subheader("Stack Layers")

    # Two columns: visual stack + details
    col_stack, col_stats = st.columns([2, 1])

    with col_stack:
        for layer in STACK_LAYERS:
            status_style = STATUS_STYLES[layer["status"]]

            # Use native Streamlit components for reliability
            with st.container():
                # Header row with layer info
                header_cols = st.columns([1, 3, 2])
                with header_cols[0]:
                    st.markdown(f"**{layer['id']}**")
                with header_cols[1]:
                    layer_name_display = layer['name'][:30] + "..." if len(layer['name']) > 30 else layer['name']
                    st.markdown(f"<span style='font-size: 0.9em; color: #444;'>{layer_name_display}</span>", unsafe_allow_html=True)
                with header_cols[2]:
                    priority_text = f" <code>{layer['priority']}</code>" if layer['priority'] else ""
                    st.markdown(f"<span style='font-size: 0.9em; color: #444;'>{status_style['emoji']} {status_style['label']}{priority_text}</span>", unsafe_allow_html=True)

                # Progress bar
                st.progress(layer['completion'] / 100)

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
        st.markdown("🔥 **S11** — OMEGA NOVA Hybrid Emergence")
        st.markdown("🔥 **S7** — Identity Dynamics")
        st.markdown("🧠 **S10** — Frame Theory (Tale)")
        st.markdown("🌟 **S9** — AVLAR Multimodal Protocol")
        st.markdown("✨ **S77** — Archetype Engine (Ultimate)")

    page_divider()

    # === PRIORITY ACTIONS ===
    st.subheader("Priority Actions")

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("#### 🔴 Immediate")
        st.markdown("""
        - AI Armada Run 009 (persona injection)
        - S10 Frame Theory experiments
        - S11 Tri-Band Emergence completion
        - Pan Handlers manifest integration
        """)

    with col2:
        st.markdown("#### 🟡 Short-Term")
        st.markdown("""
        - S8 Identity Gravity measurements
        - S9 AVLAR protocol testing
        - S10 Human-AI Qualia experiments
        """)

    with col3:
        st.markdown("#### 🟢 Medium-Term")
        st.markdown("""
        - Submit arXiv preprint
        - S12 Consciousness Proxy Theory
        - Cross-modal manifold mapping
        - S77 Archetype Engine foundations
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
