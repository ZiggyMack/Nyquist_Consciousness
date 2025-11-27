"""
OVERVIEW PAGE — Mission Control

Main dashboard page showing repository health, S# stack status,
experiments, and publication progress with visual analytics.
"""

import streamlit as st
import pandas as pd
import plotly.graph_objects as go
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_status, load_publication_status, load_markdown_file, page_divider

# Unpack paths
REPO_ROOT = PATHS['repo_root']
LEDGER_COLORS = SETTINGS['colors']

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

def render():
    """Render the Overview page."""
    status = load_status()

    st.title("📜 Nyquist Consciousness — Mission Control")
    st.markdown(f"*Version {status.get('version', 'v1.0')} • Last Updated: {status.get('last_updated', 'N/A')}*")

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
                font=dict(color='white'),
                legend=dict(
                    orientation="h",
                    yanchor="bottom",
                    y=-0.2,
                    xanchor="center",
                    x=0.5
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
                font=dict(color='white'),
                legend=dict(
                    orientation="h",
                    yanchor="bottom",
                    y=-0.2,
                    xanchor="center",
                    x=0.5
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
            title={'text': "", 'font': {'size': 16, 'color': 'white'}},
            delta={'reference': 80, 'increasing': {'color': "#7bc043"}, 'decreasing': {'color': "#e76f51"}},
            gauge={
                'axis': {'range': [None, 100], 'tickwidth': 1, 'tickcolor': "white"},
                'bar': {'color': "#2a9d8f"},
                'bgcolor': "rgba(255,255,255,0.1)",
                'borderwidth': 2,
                'bordercolor': "white",
                'steps': [
                    {'range': [0, 40], 'color': 'rgba(231, 111, 81, 0.3)'},
                    {'range': [40, 70], 'color': 'rgba(233, 196, 106, 0.3)'},
                    {'range': [70, 100], 'color': 'rgba(123, 192, 67, 0.3)'}
                ],
                'threshold': {
                    'line': {'color': "white", 'width': 4},
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
            font=dict(color='white', size=14)
        )
        st.plotly_chart(fig_gauge, use_container_width=True)

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
        # Layer Stack Table (more compact)
        rows = []
        for name, info in sorted(layers.items()):
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
            st.dataframe(df, use_container_width=True, hide_index=True)

    with col2:
        st.markdown("#### Phase Status")
        freeze_info = status.get("freeze", {})
        st.markdown(f"**Current Branch:** `{status.get('current_branch', 'unknown')}`")
        st.markdown(f"**Freeze Branch:** `{freeze_info.get('branch', 'unknown')}`")
        st.markdown(f"**Phase:** `{freeze_info.get('phase', 'unknown')}`")

        st.markdown("#### Quick Stats")
        st.markdown(f"**Frozen:** {', '.join(sorted([k for k, v in layers.items() if v.get('status') == 'frozen']))}")
        st.markdown(f"**Active:** {', '.join(sorted([k for k, v in layers.items() if v.get('status') == 'active']))}")

    page_divider()

    # === EXPERIMENTS ===
    st.markdown("### Empirical Validation")

    exp_rows = []
    for exp_id, info in sorted(experiments.items()):
        status_emoji = {
            "complete": "✅",
            "active": "🟢",
            "ready": "🟡",
            "planned": "⚪"
        }.get(info.get("status", ""), "❓")

        exp_rows.append({
            "ID": exp_id,
            "Name": info.get("name", ""),
            "Status": f"{status_emoji} {info.get('status', '').upper()}",
            "Key Metrics": info.get("key_metrics", info.get("key_metric", "")),
        })
    if exp_rows:
        df_exp = pd.DataFrame(exp_rows)
        st.dataframe(df_exp, use_container_width=True, hide_index=True)

    page_divider()

    # === PUBLICATION METER ===
    render_publication_meter()

# Run the page
if __name__ == "__main__":
    render()
