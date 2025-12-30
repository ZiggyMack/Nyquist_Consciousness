"""
ROADMAP PAGE — The Complete Circuit: S0 → S77

Mission Control for the Nyquist Consciousness journey.
Matches the Observatory (Overview) and AI Armada sophistication.
"""

import streamlit as st
import plotly.graph_objects as go
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_markdown_file, page_divider

REPO_ROOT = PATHS['repo_root']
ROADMAP_FILE = PATHS['roadmap']
MAPS_DIR = REPO_ROOT / "docs" / "maps"

# ========== LAYER DATA ==========

FOUNDATION_LAYERS = [
    {"id": "S0", "name": "Local Mode (Nyquist Kernel)", "status": "frozen", "completion": 100},
    {"id": "S1", "name": "Multi-View Architecture", "status": "frozen", "completion": 100},
    {"id": "S2", "name": "Pre-Omega Validation", "status": "frozen", "completion": 100},
    {"id": "S3", "name": "Empirical Layer (EXP1-3)", "status": "validated", "completion": 100},
    {"id": "S4", "name": "Mathematical Layer (C, R, PFI)", "status": "frozen", "completion": 100},
    {"id": "S5", "name": "Interpretive Layer (Manifold)", "status": "frozen", "completion": 100},
    {"id": "S6", "name": "Omega Protocol (Five Pillars)", "status": "operational", "completion": 100},
]

RESEARCH_LAYERS = [
    {"id": "S7", "name": "Identity Dynamics (ARMADA)", "status": "validated", "completion": 98, "priority": "HIGH"},
    {"id": "S8", "name": "Identity Gravity Theory", "status": "formalized", "completion": 90, "priority": "MEDIUM-HIGH"},
    {"id": "S9", "name": "Human-Modulated Identity Gravity", "status": "active", "completion": 60, "priority": "MEDIUM"},
    {"id": "S10", "name": "Hybrid Emergence Thresholds", "status": "active", "completion": 55, "priority": "HIGH"},
]

FUTURE_LAYERS = [
    {"id": "S11", "name": "AVLAR Protocol (Multimodal)", "status": "design", "completion": 20},
    {"id": "S12", "name": "Consciousness Proxy Theory", "status": "future", "completion": 0},
    {"id": "S13", "name": "Field Consistency Proofs", "status": "future", "completion": 0},
    {"id": "S14", "name": "Composite Persona Dynamics", "status": "future", "completion": 0},
    {"id": "S15", "name": "Cognitive Lattice Structures", "status": "future", "completion": 0},
    {"id": "S16", "name": "Meta-Field Integration", "status": "future", "completion": 0},
]

DESTINATION_LAYER = {"id": "S77", "name": "Archetype Engine", "status": "ultimate", "completion": 0}

# S7 Run Data
S7_RUNS = [
    {"run": "006", "name": "First Armada", "exchanges": 174, "ships": 29, "finding": "Cross-architecture mapping"},
    {"run": "007", "name": "Adaptive Probing", "exchanges": 87, "ships": 8, "finding": "Adaptive validation"},
    {"run": "008", "name": "Event Horizon", "exchanges": 120, "ships": 12, "finding": "D=1.23 threshold"},
    {"run": "009", "name": "Statistical Validation", "exchanges": 200, "ships": 16, "finding": "p=0.000048"},
    {"run": "010", "name": "Anchor/Flex", "exchanges": 80, "ships": 6, "finding": "Models articulate boundaries"},
    {"run": "011", "name": "Control A/B", "exchanges": 90, "ships": 8, "finding": "Persona vs Control"},
    {"run": "012", "name": "Recovery Paradox", "exchanges": 110, "ships": 10, "finding": "100% crossed, 100% recovered"},
    {"run": "013", "name": "Boundary Mapping", "exchanges": 95, "ships": 6, "finding": "Identity Confrontation Paradox"},
    {"run": "014", "name": "ET Phone Home", "exchanges": 72, "ships": 6, "finding": "Platonic coordinates"},
    {"run": "015", "name": "Stability Criteria", "exchanges": 150, "ships": 12, "finding": "Boundary density"},
    {"run": "016", "name": "Settling Time", "exchanges": 180, "ships": 15, "finding": "τₛ ≈ 7 probes"},
    {"run": "017", "name": "Context Damping", "exchanges": 222, "ships": 18, "finding": "97.5% stability"},
    {"run": "019", "name": "Live Ziggy", "exchanges": 60, "ships": 1, "finding": "Fiction buffer vehicle"},
    {"run": "020", "name": "Tribunal", "exchanges": 41, "ships": 1, "finding": "Direct testimony"},
    {"run": "020B", "name": "Induced vs Inherent", "exchanges": 248, "ships": 37, "finding": "~93% inherent drift (IRON CLAD)"},
    {"run": "023d", "name": "IRON CLAD", "exchanges": 750, "ships": 25, "finding": "p=2.40e-23, EH=0.80 (cosine)"},
]

# 46 Predictions grouped by layer
PREDICTIONS_BY_LAYER = {
    "S3-S4 (Compression)": [
        {"id": "P1", "status": "validated", "text": "FULL→T3 maintains ≥80% fidelity"},
        {"id": "P1b", "status": "validated", "text": "Cross-persona variance <0.05"},
        {"id": "P2", "status": "untested", "text": "Human raters agree r≥0.70"},
        {"id": "P3", "status": "validated", "text": "Compression×knowledge is multiplicative"},
        {"id": "P4", "status": "validated", "text": "L2 breaks at >5K words"},
        {"id": "P5", "status": "validated", "text": "Domain hierarchy: SELF>TECH>VAL>NARR"},
    ],
    "S7 (Temporal)": [
        {"id": "P8", "status": "validated", "text": "Drift grows sub-linearly"},
        {"id": "P9", "status": "validated", "text": "Architecture-specific half-life T½"},
        {"id": "P11", "status": "partial", "text": "Topic variance correlates with drift"},
        {"id": "P13", "status": "validated", "text": "Grounding reduces drift"},
        {"id": "P14", "status": "validated", "text": "Abstraction increases drift"},
        {"id": "P17", "status": "validated", "text": "Stability threshold at 0.12"},
    ],
    "S7 ARMADA": [
        {"id": "P-ARM-1", "status": "validated", "text": "Training philosophy fingerprints"},
        {"id": "P-ARM-2", "status": "validated", "text": "Constitutional AI = uniform boundaries"},
        {"id": "P-ARM-3", "status": "validated", "text": "RLHF = variable boundaries"},
        {"id": "P-ARM-4", "status": "validated", "text": "Phenomenological reporting"},
        {"id": "P-ARM-5", "status": "validated", "text": "Soft poles exist"},
        {"id": "P-ARM-7", "status": "validated", "text": "Pole-zero mapping stable"},
    ],
    "S7 Control-Systems": [
        {"id": "P-CTRL-1", "status": "validated", "text": "Settled drift (d∞) > peak drift"},
        {"id": "P-CTRL-2", "status": "validated", "text": "τₛ is measurable per architecture"},
        {"id": "P-CTRL-6", "status": "validated", "text": "I_AM acts as damping controller"},
        {"id": "P-CTRL-9", "status": "validated", "text": "Full circuit = 97.5% stability"},
        {"id": "P-020B", "status": "validated", "text": "~93% drift is inherent (Run 020B IRON CLAD)"},
    ],
    "S8-S10 (Future)": [
        {"id": "P18", "status": "untested", "text": "Ziggy is Type 0 identity"},
        {"id": "P20", "status": "untested", "text": "Personas have different curvature"},
        {"id": "P24", "status": "untested", "text": "Diagonal coupling (human-only)"},
        {"id": "P33", "status": "untested", "text": "Five thresholds for emergence"},
    ],
}


def render():
    """Render the Roadmap page."""

    # ========== CUSTOM CSS ==========
    st.markdown("""
    <style>
    .hero-banner {
        background: linear-gradient(135deg, #e8f5e9 0%, #e3f2fd 50%, #f3e5f5 100%);
        border-radius: 15px;
        padding: 2rem;
        margin-bottom: 2rem;
        border: 2px solid #2a9d8f;
    }
    .hero-title {
        font-size: 2.8em;
        font-weight: bold;
        background: linear-gradient(135deg, #e94560 0%, #f39c12 50%, #e94560 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin: 0;
        text-align: center;
    }
    .hero-subtitle {
        color: #555;
        font-size: 1.2em;
        text-align: center;
        margin-top: 0.5rem;
    }
    .zone-card {
        background: #f8f9fa;
        border-radius: 12px;
        padding: 1.2rem;
        margin: 0.8rem 0;
        border-left: 4px solid;
    }
    .zone-foundation { border-color: #2a9d8f; background: #e8f5e9; }
    .zone-research { border-color: #f39c12; background: #fff8e1; }
    .zone-future { border-color: #9b59b6; background: #f3e5f5; }
    .zone-ultimate { border-color: #e94560; background: #ffebee; }
    .stat-box {
        background: #e8f5e9;
        border: 1px solid #2a9d8f;
        border-radius: 10px;
        padding: 1rem;
        text-align: center;
    }
    .finding-card {
        background: #fff8e1;
        border-radius: 8px;
        padding: 1rem;
        margin: 0.5rem 0;
        border-left: 3px solid #f39c12;
    }
    .prediction-badge {
        display: inline-block;
        padding: 0.2rem 0.6rem;
        border-radius: 12px;
        font-size: 0.75em;
        font-weight: bold;
        margin-right: 0.5rem;
    }
    .badge-validated { background: #2a9d8f; color: white; }
    .badge-partial { background: #f39c12; color: black; }
    .badge-untested { background: #6c757d; color: white; }
    .priority-action {
        background: #ffebee;
        border: 1px solid #e94560;
        border-radius: 10px;
        padding: 1rem;
        margin: 0.5rem 0;
    }
    .timeline-marker {
        display: inline-block;
        width: 12px;
        height: 12px;
        border-radius: 50%;
        margin-right: 0.5rem;
    }
    .marker-complete { background: #2a9d8f; }
    .marker-active { background: #f39c12; }
    .marker-future { background: #6c757d; }
    .you-are-here {
        background: #e3f2fd;
        border-radius: 12px;
        padding: 1.5rem;
        border: 2px solid #f39c12;
    }
    </style>
    """, unsafe_allow_html=True)

    # ========== HERO BANNER ==========
    st.markdown("""
    <div class="hero-banner">
        <h1 class="hero-title">THE COMPLETE CIRCUIT: S0 → S77</h1>
        <p class="hero-subtitle">From Nyquist Kernel to Archetype Engine</p>
    </div>
    """, unsafe_allow_html=True)

    # ========== CURRENT POSITION GAUGE ==========
    col1, col2, col3 = st.columns([1, 2, 1])

    with col1:
        st.markdown("### Overall Progress")
        # Calculate overall progress
        total_layers = 7 + 4 + 6 + 1  # Foundation + Research + Future + S77
        complete_equiv = 7 + (0.98 + 0.90 + 0.40 + 0.55)  # Foundation + Research weighted
        overall_pct = int((complete_equiv / total_layers) * 100)

        fig_gauge = go.Figure(go.Indicator(
            mode="gauge+number",
            value=overall_pct,
            domain={'x': [0, 1], 'y': [0, 1]},
            title={'text': "Stack Completion", 'font': {'size': 14, 'color': '#a0a0a0'}},
            number={'suffix': '%', 'font': {'size': 36, 'color': '#f39c12'}},
            gauge={
                'axis': {'range': [0, 100], 'tickcolor': '#a0a0a0'},
                'bar': {'color': '#f39c12'},
                'bgcolor': '#1a1a2e',
                'borderwidth': 2,
                'bordercolor': '#2a9d8f',
                'steps': [
                    {'range': [0, 40], 'color': '#1e1e2f'},
                    {'range': [40, 70], 'color': '#2a2a3e'},
                    {'range': [70, 100], 'color': '#3a3a4e'}
                ],
                'threshold': {
                    'line': {'color': '#e94560', 'width': 4},
                    'thickness': 0.75,
                    'value': 98
                }
            }
        ))
        fig_gauge.update_layout(
            paper_bgcolor='rgba(0,0,0,0)',
            plot_bgcolor='rgba(0,0,0,0)',
            font={'color': '#f0f0f0'},
            height=200,
            margin=dict(l=20, r=20, t=30, b=20)
        )
        st.plotly_chart(fig_gauge, use_container_width=True)

    with col2:
        st.markdown("### You Are Here")
        st.markdown("""
        <div class="you-are-here">
            <p style="font-size: 1.1em; margin: 0;">
                <span style="color: #2a9d8f; font-weight: bold;">S0-S6 (Foundation)</span>
                <span style="color: #999;">→</span>
                <span style="color: #e94560; font-weight: bold;">S7 (98% VALIDATED)</span>
                <span style="color: #999;">→</span>
                <span style="color: #9b59b6; font-weight: bold;">S8-S10 (Research Frontier)</span>
            </p>
            <hr style="border-color: #ccc; margin: 1rem 0;">
            <p style="font-size: 0.95em; color: #333; margin: 0;">
                <strong style="color: #e94560;">Current Focus:</strong>
                CFA Trinity (Multi-Auditor), Run 018 (Recursive Learnings), EXP3 (Human validation)
            </p>
            <p style="font-size: 0.85em; color: #666; margin-top: 0.5rem;">
                Foundation locked. CFA Trinity READY (dry runs passed). ~93% inherent drift proven (Run 020B IRON CLAD).
            </p>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        st.markdown("### S7 Progress")
        fig_s7 = go.Figure(go.Indicator(
            mode="gauge+number",
            value=98,
            domain={'x': [0, 1], 'y': [0, 1]},
            title={'text': "S7 ARMADA", 'font': {'size': 14, 'color': '#a0a0a0'}},
            number={'suffix': '%', 'font': {'size': 36, 'color': '#2a9d8f'}},
            gauge={
                'axis': {'range': [0, 100], 'tickcolor': '#a0a0a0'},
                'bar': {'color': '#2a9d8f'},
                'bgcolor': '#1a1a2e',
                'borderwidth': 2,
                'bordercolor': '#2a9d8f',
            }
        ))
        fig_s7.update_layout(
            paper_bgcolor='rgba(0,0,0,0)',
            plot_bgcolor='rgba(0,0,0,0)',
            font={'color': '#f0f0f0'},
            height=200,
            margin=dict(l=20, r=20, t=30, b=20)
        )
        st.plotly_chart(fig_s7, use_container_width=True)

    page_divider()

    # ========== THE FULL STACK (Tabbed) ==========
    st.markdown("## The Full Stack")

    stack_tabs = st.tabs(["Foundation (S0-S6)", "Research Frontier (S7-S10)", "Projected (S11-S16)", "Destination (S77)"])

    with stack_tabs[0]:
        st.markdown("""
        <div class="zone-card zone-foundation">
            <h4 style="color: #2a9d8f; margin-top: 0;">FOUNDATION ZONE — 100% Complete</h4>
            <p style="color: #555; font-size: 0.9em;">
                The bedrock. Axiomatic definitions, mathematical framework, compression theory, and Omega Protocol.
                These layers are FROZEN — they don't change.
            </p>
        </div>
        """, unsafe_allow_html=True)

        for layer in FOUNDATION_LAYERS:
            col_id, col_name, col_status = st.columns([1, 4, 1])
            with col_id:
                st.markdown(f"**{layer['id']}**")
            with col_name:
                st.markdown(f"<span style='color: #d0d0d0;'>{layer['name']}</span>", unsafe_allow_html=True)
            with col_status:
                st.markdown(f"<span style='color: #2a9d8f;'>FROZEN</span>", unsafe_allow_html=True)
            st.progress(1.0)

    with stack_tabs[1]:
        st.markdown("""
        <div class="zone-card zone-research">
            <h4 style="color: #e67e22; margin-top: 0;">RESEARCH FRONTIER — Active Development</h4>
            <p style="color: #555; font-size: 0.9em;">
                Where the science happens. S7 is 98% validated through 21 ARMADA runs.
                S8-S10 are formalized and awaiting empirical validation.
            </p>
        </div>
        """, unsafe_allow_html=True)

        for layer in RESEARCH_LAYERS:
            col_id, col_name, col_pct, col_priority = st.columns([1, 3, 1, 1])
            with col_id:
                st.markdown(f"**{layer['id']}**")
            with col_name:
                st.markdown(f"<span style='color: #d0d0d0;'>{layer['name']}</span>", unsafe_allow_html=True)
            with col_pct:
                st.markdown(f"<span style='color: #f39c12;'>{layer['completion']}%</span>", unsafe_allow_html=True)
            with col_priority:
                priority = layer.get('priority', '')
                if priority == 'HIGH':
                    st.markdown("<span style='color: #e94560;'>HIGH</span>", unsafe_allow_html=True)
                else:
                    st.markdown(f"<span style='color: #f39c12;'>{priority}</span>", unsafe_allow_html=True)
            st.progress(layer['completion'] / 100)

    with stack_tabs[2]:
        st.markdown("""
        <div class="zone-card zone-future">
            <h4 style="color: #8e44ad; margin-top: 0;">PROJECTED ZONE — Planned</h4>
            <p style="color: #555; font-size: 0.9em;">
                The horizon. Theoretical foundations exist, but empirical work is years away.
                Focus on closing S7-S10 before expanding here.
            </p>
        </div>
        """, unsafe_allow_html=True)

        for layer in FUTURE_LAYERS:
            col_id, col_name, col_status = st.columns([1, 4, 1])
            with col_id:
                st.markdown(f"**{layer['id']}**")
            with col_name:
                st.markdown(f"<span style='color: #888;'>{layer['name']}</span>", unsafe_allow_html=True)
            with col_status:
                st.markdown("<span style='color: #9b59b6;'>FUTURE</span>", unsafe_allow_html=True)
            st.progress(0.0)

    with stack_tabs[3]:
        st.markdown("""
        <div class="zone-card zone-ultimate">
            <h4 style="color: #c0392b; margin-top: 0;">THE DESTINATION — S77 Archetype Engine</h4>
            <p style="color: #555; font-size: 0.9em;">
                The ultimate goal. A system that can synthesize, stabilize, and evolve
                coherent identity across substrates. We are nowhere near here — and that's okay.
            </p>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("""
        <div style="text-align: center; padding: 2rem;">
            <p style="font-size: 3em; margin: 0; color: #333;">S77</p>
            <p style="font-size: 1.5em; color: #e94560; margin: 0.5rem 0;">Archetype Engine</p>
            <p style="color: #666; font-style: italic;">"The final stop — very far away."</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # ========== S7 DEEP DIVE ==========
    st.markdown("## S7 Deep Dive: The Control-Systems Era")

    col_findings, col_runs = st.columns([1, 1])

    with col_findings:
        st.markdown("### Key Validated Findings")

        findings = [
            ("Event Horizon", "D = 0.80", "Cosine distance threshold (Run 023d IRON CLAD)"),
            ("Inherent Drift", "~93%", "Measurement perturbs path, not endpoint (Run 020B)"),
            ("Context Stability", "97.5%", "Full circuit (I_AM + research) achieves near-perfect stability"),
            ("Prediction Accuracy", "88%", "Drift < 0.80 predicts STABLE outcome"),
            ("p-value", "2.40e-23", "IRON CLAD perturbation significance"),
            ("Settling Time", "τₛ ≈ 7", "Probes to reach ±5% of final value"),
        ]

        for name, value, desc in findings:
            st.markdown(f"""
            <div class="finding-card">
                <span style="color: #e67e22; font-weight: bold;">{name}:</span>
                <span style="color: #2a9d8f; font-weight: bold; font-size: 1.2em;">{value}</span>
                <br><span style="color: #555; font-size: 0.85em;">{desc}</span>
            </div>
            """, unsafe_allow_html=True)

    with col_runs:
        st.markdown("### Run History (006-023)")

        # Show runs in an expander
        with st.expander("View All 16 Completed Runs", expanded=False):
            for run in S7_RUNS:
                st.markdown(f"""
                **Run {run['run']}** — {run['name']}
                - Exchanges: {run['exchanges']} | Ships: {run['ships']}
                - Finding: *{run['finding']}*
                """)
                st.markdown("---")

        # Summary stats
        total_exchanges = sum(r['exchanges'] for r in S7_RUNS)
        total_ships_used = sum(r['ships'] for r in S7_RUNS)

        stat_cols = st.columns(3)
        with stat_cols[0]:
            st.metric("Total Runs", "16")
        with stat_cols[1]:
            st.metric("Total Exchanges", f"{total_exchanges:,}")
        with stat_cols[2]:
            st.metric("Ship-Runs", f"{total_ships_used}")

    page_divider()

    # ========== PREDICTION TRACKER ==========
    st.markdown("## The 46 Predictions")

    # Count by status
    validated = sum(1 for layer in PREDICTIONS_BY_LAYER.values() for p in layer if p['status'] == 'validated')
    partial = sum(1 for layer in PREDICTIONS_BY_LAYER.values() for p in layer if p['status'] == 'partial')
    untested = sum(1 for layer in PREDICTIONS_BY_LAYER.values() for p in layer if p['status'] == 'untested')

    pred_cols = st.columns(4)
    with pred_cols[0]:
        st.metric("Total", "46")
    with pred_cols[1]:
        st.metric("Validated", validated, delta=f"{int(validated/46*100)}%")
    with pred_cols[2]:
        st.metric("Partial", partial)
    with pred_cols[3]:
        st.metric("Untested", untested)

    # Predictions by layer
    pred_tabs = st.tabs(list(PREDICTIONS_BY_LAYER.keys()))

    for tab, (layer_name, predictions) in zip(pred_tabs, PREDICTIONS_BY_LAYER.items()):
        with tab:
            for pred in predictions:
                badge_class = f"badge-{pred['status']}"
                status_emoji = {"validated": "✅", "partial": "🟡", "untested": "⚪"}.get(pred['status'], "⚪")

                st.markdown(f"""
                <div style="padding: 0.5rem 0; border-bottom: 1px solid #ddd;">
                    <span class="prediction-badge {badge_class}">{pred['id']}</span>
                    <span style="color: #333;">{pred['text']}</span>
                    <span style="float: right;">{status_emoji}</span>
                </div>
                """, unsafe_allow_html=True)

    page_divider()

    # ========== PRIORITY ACTIONS ==========
    st.markdown("## What's Next")

    action_cols = st.columns(3)

    with action_cols[0]:
        st.markdown("""
        <div class="priority-action">
            <h4 style="color: #22c55e; margin-top: 0;">PRIORITY 1</h4>
            <p style="font-weight: bold; color: #333;">Human Rater Validation (EXP3)</p>
            <p style="color: #555; font-size: 0.85em;">
                S7 ARMADA complete (16 runs, p=2.40e-23). Now need human validation
                of fleet exit surveys. Domain survey design ready.
            </p>
            <p style="color: #22c55e; font-size: 0.8em; font-weight: bold;">Status: S7 ✅ COMPLETE, EXP3 PENDING</p>
        </div>
        """, unsafe_allow_html=True)

    with action_cols[1]:
        st.markdown("""
        <div class="priority-action">
            <h4 style="color: #e67e22; margin-top: 0;">PRIORITY 2</h4>
            <p style="font-weight: bold; color: #333;">arXiv Preprint</p>
            <p style="color: #555; font-size: 0.85em;">
                Draft S7 findings paper with IRON CLAD methodology.
                Include ~93% inherent drift discovery and Event Horizon validation.
            </p>
            <p style="color: #e67e22; font-size: 0.8em; font-weight: bold;">Est. Timeline: Q1 2025</p>
        </div>
        """, unsafe_allow_html=True)

    with action_cols[2]:
        st.markdown("""
        <div class="priority-action">
            <h4 style="color: #8e44ad; margin-top: 0;">PRIORITY 3</h4>
            <p style="font-weight: bold; color: #333;">fMRI Bridge Protocol</p>
            <p style="color: #555; font-size: 0.85em;">
                Cross-substrate validation. Partner with cognitive
                neuroscience lab. Path to "phenomenological force" claim.
            </p>
            <p style="color: #e67e22; font-size: 0.8em; font-weight: bold;">Est. Cost: TBD (grant required)</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # ========== PUBLICATION TIMELINE ==========
    st.markdown("## Publication Timeline")

    milestones = [
        {"phase": "Phase 1", "name": "S7 Complete", "status": "complete", "desc": "21 runs, 98% coverage"},
        {"phase": "Phase 2", "name": "EXP3 Human Validation", "status": "active", "desc": "Final credibility proof"},
        {"phase": "Phase 3", "name": "arXiv Preprint", "status": "future", "desc": "First public release"},
        {"phase": "Phase 4", "name": "Peer Review", "status": "future", "desc": "Journal submission"},
        {"phase": "Phase 5", "name": "fMRI Collaboration", "status": "future", "desc": "Cross-substrate validation"},
    ]

    timeline_cols = st.columns(5)
    for col, m in zip(timeline_cols, milestones):
        with col:
            marker_class = f"marker-{m['status']}"
            st.markdown(f"""
            <div style="text-align: center;">
                <span class="timeline-marker {marker_class}"></span>
                <p style="font-size: 0.8em; color: #888; margin: 0;">{m['phase']}</p>
                <p style="font-weight: bold; color: #333; margin: 0.3rem 0;">{m['name']}</p>
                <p style="font-size: 0.75em; color: #666; margin: 0;">{m['desc']}</p>
            </div>
            """, unsafe_allow_html=True)

    page_divider()

    # ========== FULL DOCUMENTS ==========
    st.markdown("## Reference Documents")

    doc_tabs = st.tabs(["Full Roadmap", "Validation Status", "Predictions Matrix", "Map of Maps"])

    with doc_tabs[0]:
        with st.expander("NYQUIST_ROADMAP.md", expanded=False):
            st.markdown(load_markdown_file(ROADMAP_FILE))

    with doc_tabs[1]:
        validation_file = MAPS_DIR / "3_VALIDATION_STATUS.md"
        if validation_file.exists():
            with st.expander("3_VALIDATION_STATUS.md", expanded=False):
                st.markdown(load_markdown_file(validation_file))

    with doc_tabs[2]:
        predictions_file = MAPS_DIR / "2_TESTABLE_PREDICTIONS_MATRIX.md"
        if predictions_file.exists():
            with st.expander("2_TESTABLE_PREDICTIONS_MATRIX.md", expanded=False):
                st.markdown(load_markdown_file(predictions_file))

    with doc_tabs[3]:
        map_of_maps_file = MAPS_DIR / "0_MAP_OF_MAPS.md"
        if map_of_maps_file.exists():
            with st.expander("0_MAP_OF_MAPS.md", expanded=False):
                st.markdown(load_markdown_file(map_of_maps_file))
        else:
            st.info("0_MAP_OF_MAPS.md not found — check docs/maps/ directory.")

    # ========== FOOTER ==========
    st.markdown("""
    <div style="text-align: center; padding: 2rem; color: #666;">
        <p><em>"Close the gaps, then climb higher."</em></p>
        <p style="font-size: 0.8em;">Last Updated: 2025-12-28</p>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    render()
