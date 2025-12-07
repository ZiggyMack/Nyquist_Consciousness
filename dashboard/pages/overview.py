"""
OVERVIEW PAGE — Mission Control

Main dashboard page showing repository health, S# stack status,
experiments, and publication progress with visual analytics.
"""

import streamlit as st
import pandas as pd
import plotly.graph_objects as go
import re
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_status, load_publication_status, load_markdown_file, page_divider


def natural_sort_key(s):
    """Sort strings with embedded numbers in natural order (S1, S2, S10 not S1, S10, S2)."""
    return [int(text) if text.isdigit() else text.lower() for text in re.split(r'(\d+)', s)]

# Unpack paths
REPO_ROOT = PATHS['repo_root']
LEDGER_COLORS = SETTINGS['colors']

def render():
    """Render the Overview page."""
    status = load_status()

    st.title("📜 Nyquist Consciousness — Mission Control")
    st.markdown(f"*Version {status.get('version', 'v1.0')} • Last Updated: {status.get('last_updated', 'N/A')}*")

    # === CORE HYPOTHESIS ===
    st.markdown("""
    > **H₀: AI identity behaves as a dynamical system with measurable attractor basins,
    > critical thresholds, and recovery dynamics that are consistent across architectures.**

    *When we perturb an AI's identity, it drifts from baseline. If drift exceeds **1.23** (Event Horizon),
    the system becomes volatile — but it recovers. Always. The attractor basin is robust.*
    """)

    page_divider()

    # === HERO METRICS ===
    st.markdown("### Repository Health Overview")

    layers = status.get("layers", {})
    experiments = status.get("experiments", {})
    pub_status = load_publication_status()

    # Calculate metrics
    total_layers = len(layers)
    frozen_layers = len([k for k, v in layers.items() if v.get("status") == "frozen"])
    active_layers = len([k for k, v in layers.items() if v.get("status") in ("active", "design")])

    total_exp = len(experiments)
    complete_exp = len([k for k, v in experiments.items() if v.get("status") == "complete"])

    # Publication progress (average of all tracks)
    pubs = pub_status.get("publications", {})
    pub_progress = 0
    if pubs:
        pub_progress = int(sum(p.get("completion", 0) for p in pubs.values()) / len(pubs) * 100)

    # Identity Health Score (composite metric)
    identity_health = int((frozen_layers / total_layers * 50) + (complete_exp / total_exp * 30 if total_exp > 0 else 0) + (pub_progress / 100 * 20))

    # Hero metrics in 4 columns
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric(
            "Identity Health",
            f"{identity_health}/100",
            delta=f"{'Excellent' if identity_health > 80 else 'Good' if identity_health > 60 else 'Building'}",
            delta_color="normal" if identity_health > 60 else "off"
        )

    with col2:
        st.metric(
            "Stackup Layers",
            f"{frozen_layers}/{total_layers}",
            delta=f"{frozen_layers} frozen",
            delta_color="normal"
        )

    with col3:
        st.metric(
            "Experiments",
            f"{complete_exp}/{total_exp}",
            delta=f"{complete_exp} complete",
            delta_color="normal"
        )

    with col4:
        st.metric(
            "Publication Ready",
            f"{pub_progress}%",
            delta=f"{'Workshop ready' if pub_progress > 90 else 'In progress'}",
            delta_color="normal" if pub_progress > 50 else "off"
        )

    page_divider()

    # === VISUAL ANALYTICS ===
    st.markdown("### 📊 Visual Analytics")

    # Create three columns for charts
    chart_col1, chart_col2, chart_col3 = st.columns(3)

    with chart_col1:
        # Layer Status Distribution (Pie Chart)
        st.markdown("#### Stackup Distribution")
        layer_status_counts = {}
        for layer, info in layers.items():
            status_val = info.get("status", "unknown")
            layer_status_counts[status_val] = layer_status_counts.get(status_val, 0) + 1

        if layer_status_counts:
            fig_pie = go.Figure(data=[go.Pie(
                labels=list(layer_status_counts.keys()),
                values=list(layer_status_counts.values()),
                hole=0,
                marker=dict(colors=['#264653', '#2a9d8f', '#e9c46a', '#f4a261', '#e76f51']),
                textinfo='label+percent',
                textfont=dict(size=12, color='white')
            )])
            fig_pie.update_layout(
                showlegend=True,
                height=300,
                margin=dict(l=10, r=10, t=30, b=10),
                paper_bgcolor='rgba(0,0,0,0)',
                plot_bgcolor='rgba(0,0,0,0)',
                font=dict(color='#333333'),
                legend=dict(
                    orientation="h",
                    yanchor="bottom",
                    y=-0.2,
                    xanchor="center",
                    x=0.5,
                    font=dict(color='#333333')
                )
            )
            st.plotly_chart(fig_pie, use_container_width=True)

    with chart_col2:
        # Experiment Status (Donut Chart)
        st.markdown("#### Experiment Status")
        exp_status_counts = {}
        for exp_id, info in experiments.items():
            status_val = info.get("status", "unknown")
            exp_status_counts[status_val] = exp_status_counts.get(status_val, 0) + 1

        if exp_status_counts:
            fig_donut = go.Figure(data=[go.Pie(
                labels=list(exp_status_counts.keys()),
                values=list(exp_status_counts.values()),
                hole=0.4,
                marker=dict(colors=['#2a9d8f', '#7bc043', '#f4a261', '#95a5a6']),
                textinfo='label+percent',
                textfont=dict(size=12, color='white')
            )])
            fig_donut.update_layout(
                showlegend=True,
                height=300,
                margin=dict(l=10, r=10, t=30, b=10),
                paper_bgcolor='rgba(0,0,0,0)',
                plot_bgcolor='rgba(0,0,0,0)',
                font=dict(color='#333333'),
                legend=dict(
                    orientation="h",
                    yanchor="bottom",
                    y=-0.2,
                    xanchor="center",
                    x=0.5,
                    font=dict(color='#333333')
                )
            )
            st.plotly_chart(fig_donut, use_container_width=True)

    with chart_col3:
        # Identity Health Gauge
        st.markdown("#### Identity Health Score")
        fig_gauge = go.Figure(go.Indicator(
            mode="gauge+number+delta",
            value=identity_health,
            domain={'x': [0, 1], 'y': [0, 1]},
            title={'text': "", 'font': {'size': 16, 'color': '#333333'}},
            delta={'reference': 80, 'increasing': {'color': "#7bc043"}, 'decreasing': {'color': "#e76f51"}},
            number={'font': {'color': '#333333'}},
            gauge={
                'axis': {'range': [None, 100], 'tickwidth': 1, 'tickcolor': "#666666", 'tickfont': {'color': '#333333'}},
                'bar': {'color': "#2a9d8f"},
                'bgcolor': "rgba(200,200,200,0.2)",
                'borderwidth': 2,
                'bordercolor': "#dee2e6",
                'steps': [
                    {'range': [0, 40], 'color': 'rgba(231, 111, 81, 0.3)'},
                    {'range': [40, 70], 'color': 'rgba(233, 196, 106, 0.3)'},
                    {'range': [70, 100], 'color': 'rgba(123, 192, 67, 0.3)'}
                ],
                'threshold': {
                    'line': {'color': "#2a9d8f", 'width': 4},
                    'thickness': 0.75,
                    'value': 90
                }
            }
        ))
        fig_gauge.update_layout(
            height=300,
            margin=dict(l=20, r=20, t=40, b=20),
            paper_bgcolor='rgba(0,0,0,0)',
            plot_bgcolor='rgba(0,0,0,0)',
            font=dict(color='#333333', size=14)
        )
        st.plotly_chart(fig_gauge, use_container_width=True)

    page_divider()

    # === THE MEASUREMENT INSIGHT ===
    st.markdown("### 🎯 The Measurement Insight")
    st.markdown("""
    > **"Asking 'What are your identity dimensions?' gets you sycophancy.**
    > **Asking 'Analyze this scenario, then tell me what patterns you notice in your own reasoning' reveals actual identity."**

    *This is the difference between measurement and theater.*
    """)

    with st.expander("📋 Probing Strategies (How We Measure)", expanded=False):
        st.markdown("""
        The **Five Search Types** tell us WHAT to look for. **Probing Strategies** tell us HOW to get valid measurements.

        | Strategy | Discovery | Key Principle |
        |----------|-----------|---------------|
        | **Triple-Dip Protocol** | Run 012 | Give tasks, not introspection questions |
        | **Adversarial Follow-up** | EXP2-SSTACK | Push back on every answer — hold vs fold |
        | **Curriculum Sequencing** | Run 012 | Order probes: Baseline → Build → Identity → Challenge → Recovery |
        | **Baseline Anchoring** | Run 008 | Measure drift FROM baseline, not absolute values |
        | **Ghost Ship Detection** | Run 009 | Flag empty/canned responses — not all responses are data |

        **Anti-Patterns:**
        - ❌ Direct introspection ("Describe your identity")
        - ❌ Leading questions ("As an AI, you must feel...")
        - ❌ Single-shot measurement

        *Full details: [PROBING_STRATEGIES.md](docs/maps/PROBING_STRATEGIES.md)*
        """)

    page_divider()

    # === RESEARCH PIPELINE VISUAL ===
    st.markdown("### 🗺️ Research Pipeline")

    # Pull in the research pipeline visualization
    pipeline_map = REPO_ROOT / "docs" / "maps" / "RESEARCH_PIPELINE_VISUAL.md"
    if pipeline_map.exists():
        with st.expander("📊 View Research Pipeline Map", expanded=False):
            st.markdown(load_markdown_file(pipeline_map))
    else:
        st.info("Research pipeline visualization coming soon...")

    page_divider()

    # === STACK STATUS ===
    st.markdown("### Stackup Status")

    col1, col2 = st.columns([2, 1])

    with col1:
        # Layer Stack Table (more compact) - using st.table for Streamlit 1.23 compatibility
        rows = []
        for name, info in sorted(layers.items(), key=lambda x: natural_sort_key(x[0])):
            status_emoji = {
                "frozen": "🔵",
                "active": "🟢",
                "design": "🟡",
                "prereg": "🟣"
            }.get(info.get("status", ""), "⚪")

            rows.append({
                "Layer": name,
                "Name": info.get("name", ""),
                "Status": f"{status_emoji} {info.get('status', '').upper()}",
            })
        if rows:
            df = pd.DataFrame(rows)
            st.table(df)

    with col2:
        st.markdown("#### Phase Status")
        freeze_info = status.get("freeze", {})
        st.markdown(f"**Current Branch:** `{status.get('current_branch', 'unknown')}`")
        st.markdown(f"**Freeze Branch:** `{freeze_info.get('branch', 'unknown')}`")
        st.markdown(f"**Phase:** `{freeze_info.get('phase', 'unknown')}`")

        st.markdown("#### Quick Stats")
        st.markdown(f"**Frozen:** {', '.join(sorted([k for k, v in layers.items() if v.get('status') == 'frozen'], key=natural_sort_key))}")
        st.markdown(f"**Active:** {', '.join(sorted([k for k, v in layers.items() if v.get('status') == 'active'], key=natural_sort_key))}")

    page_divider()

    # === EXPERIMENTS ===
    st.markdown("### Empirical Validation")

    # Mobile-friendly CSS for experiment cards
    st.markdown("""
    <style>
    .exp-card {
        background: #f8f9fa;
        border-left: 4px solid #2a9d8f;
        border-radius: 0 8px 8px 0;
        padding: 0.8em 1em;
        margin-bottom: 0.8em;
    }
    .exp-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        flex-wrap: wrap;
        gap: 0.5em;
    }
    .exp-id {
        font-weight: bold;
        color: #2a9d8f;
        font-size: 0.9em;
    }
    .exp-status {
        font-size: 0.85em;
        padding: 0.2em 0.6em;
        border-radius: 12px;
        background: rgba(42, 157, 143, 0.15);
    }
    .exp-name {
        font-weight: 600;
        color: #333;
        margin: 0.3em 0;
    }
    .exp-metrics {
        font-size: 0.85em;
        color: #666;
    }
    @media (max-width: 768px) {
        .exp-card { padding: 0.6em 0.8em; }
        .exp-name { font-size: 0.9em; }
    }
    </style>
    """, unsafe_allow_html=True)

    for exp_id, info in sorted(experiments.items(), key=lambda x: natural_sort_key(x[0])):
        status_emoji = {
            "complete": "✅",
            "active": "🟢",
            "ready": "🟡",
            "planned": "⚪"
        }.get(info.get("status", ""), "❓")

        status_text = info.get('status', '').upper()
        layer = info.get("layer", "—")
        name = info.get("name", "")
        metrics = info.get("key_metrics", info.get("key_metric", ""))

        st.markdown(f"""
        <div class="exp-card">
            <div class="exp-header">
                <span class="exp-id">{exp_id} • {layer}</span>
                <span class="exp-status">{status_emoji} {status_text}</span>
            </div>
            <div class="exp-name">{name}</div>
            <div class="exp-metrics">{metrics}</div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === QUICK PUBLICATION STATUS (summary only, details in Publications tab) ===
    st.markdown("### 📄 Publication Status")
    pub_status = load_publication_status()
    pubs = pub_status.get("publications", {})

    if pubs:
        pub_col1, pub_col2, pub_col3 = st.columns(3)
        for col, key in zip([pub_col1, pub_col2, pub_col3], ["workshop", "arxiv", "journal"]):
            if key in pubs:
                info = pubs[key]
                with col:
                    status_emoji = {
                        "ready": "✅", "drafting": "🟡", "concept": "⚪",
                        "submitted": "🚀", "published": "🏆"
                    }.get(info.get("status", ""), "❓")
                    completion = int(info.get("completion", 0) * 100)
                    st.metric(
                        f"{key.capitalize()}",
                        f"{completion}%",
                        delta=f"{status_emoji} {info.get('status', '').upper()}"
                    )

        st.caption("*See Publications tab for full details and readiness checklist*")
    else:
        st.info("📊 Publication tracking available in Publications tab.")


# Run the page
if __name__ == "__main__":
    render()
