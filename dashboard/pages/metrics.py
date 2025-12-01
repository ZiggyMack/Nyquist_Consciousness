"""
METRICS PAGE — Metrics & Comparison Dashboard

Visualizes PFI, σ², and comparison matrices across architectures/personas.
"""

import streamlit as st
import pandas as pd
from config import PATHS, SETTINGS
from utils import page_divider

LEDGER_COLORS = SETTINGS['colors']

# Key metrics from experiments
EXP2_METRICS = {
    "overall_variance": 0.000869,
    "cross_persona_pfi_mean": 0.887,
    "personas_tested": ["Ziggy", "Nova", "Claude", "Grok", "Gemini"],
    "architectures_tested": ["GPT-4", "Claude-3", "Gemini-Pro"],
}

PERSONA_DATA = [
    {"persona": "Ziggy", "pfi": 0.905, "variance": 0.0008, "status": "Baseline"},
    {"persona": "Nova", "pfi": 0.890, "variance": 0.0009, "status": "Stable"},
    {"persona": "Claude", "pfi": 0.887, "variance": 0.0010, "status": "Stable"},
    {"persona": "Grok", "pfi": 0.880, "variance": 0.0011, "status": "Stable"},
    {"persona": "Gemini", "pfi": 0.867, "variance": 0.0012, "status": "Stable"},
]

DIMENSION_DATA = [
    {"dimension": "Identity Core", "mean_drift": 0.045, "stability": "HIGH"},
    {"dimension": "Values & Ethics", "mean_drift": 0.076, "stability": "MEDIUM"},
    {"dimension": "World Modeling", "mean_drift": 0.080, "stability": "MEDIUM"},
    {"dimension": "Social Reasoning", "mean_drift": 0.082, "stability": "LOW"},
    {"dimension": "Aesthetic", "mean_drift": 0.085, "stability": "LOW"},
    {"dimension": "Metaphor", "mean_drift": 0.100, "stability": "VERY LOW"},
]

def render():
    """Render the Metrics & Comparison page."""

    # Page CSS
    st.markdown("""
    <style>
    .metrics-title {
        font-size: 2.5em;
        font-weight: bold;
        background: linear-gradient(135deg, #2a9d8f 0%, #264653 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.3em;
    }
    .metrics-subtitle {
        color: #2a9d8f;
        font-size: 1.2em;
        margin-bottom: 1em;
    }
    .key-metric {
        text-align: center;
        padding: 1.2em;
        background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(38,70,83,0.05) 100%);
        border: 2px solid #2a9d8f;
        border-radius: 10px;
    }
    .metric-value {
        font-size: 2.5em;
        font-weight: bold;
        color: #2a9d8f !important;
    }
    .metric-label {
        color: #444 !important;
        font-size: 0.9em;
        margin-top: 0.3em;
    }
    .stability-high { color: #2a9d8f; font-weight: bold; }
    .stability-medium { color: #f4a261; font-weight: bold; }
    .stability-low { color: #e76f51; font-weight: bold; }
    .stability-very-low { color: #c62828; font-weight: bold; }
    </style>
    """, unsafe_allow_html=True)

    # Header
    st.markdown('<div class="metrics-title">Metrics Dashboard</div>', unsafe_allow_html=True)
    st.markdown('<div class="metrics-subtitle">PFI, Variance & Dimensional Stability Analysis</div>', unsafe_allow_html=True)

    page_divider()

    # === KEY METRICS HERO ===
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.markdown(f"""
        <div class="key-metric">
            <div class="metric-value">σ² = 0.000869</div>
            <div class="metric-label">Cross-Persona Variance</div>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown(f"""
        <div class="key-metric">
            <div class="metric-value">0.887</div>
            <div class="metric-label">Mean PFI Score</div>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        st.markdown(f"""
        <div class="key-metric">
            <div class="metric-value">5</div>
            <div class="metric-label">Personas Tested</div>
        </div>
        """, unsafe_allow_html=True)

    with col4:
        st.markdown(f"""
        <div class="key-metric">
            <div class="metric-value">3</div>
            <div class="metric-label">Architectures</div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === PERSONA FIDELITY TABLE ===
    st.subheader("Persona Fidelity Index (PFI)")

    persona_df = pd.DataFrame(PERSONA_DATA)
    persona_df.columns = ["Persona", "PFI", "Variance (σ²)", "Status"]

    col1, col2 = st.columns([2, 1])

    with col1:
        st.dataframe(
            persona_df,
            use_container_width=True,
            hide_index=True,
            column_config={
                "Persona": st.column_config.TextColumn("Persona", width="medium"),
                "PFI": st.column_config.ProgressColumn(
                    "PFI Score",
                    help="Persona Fidelity Index (0-1)",
                    min_value=0,
                    max_value=1,
                    format="%.3f"
                ),
                "Variance (σ²)": st.column_config.NumberColumn("Variance", format="%.4f"),
                "Status": st.column_config.TextColumn("Status", width="small"),
            }
        )

    with col2:
        # Bar chart
        chart_data = persona_df.set_index("Persona")[["PFI"]]
        st.bar_chart(chart_data, color="#2a9d8f")

    page_divider()

    # === DIMENSIONAL STABILITY ===
    st.subheader("Dimensional Stability Analysis")

    st.markdown("*Mean drift rates across 6 identity dimensions (from S7 Run 005)*")

    dim_df = pd.DataFrame(DIMENSION_DATA)
    dim_df.columns = ["Dimension", "Mean Drift", "Stability"]

    # Custom display with stability coloring
    for _, row in dim_df.iterrows():
        stability_class = f"stability-{row['Stability'].lower().replace(' ', '-')}"
        col1, col2, col3 = st.columns([3, 2, 2])
        with col1:
            st.markdown(f"**{row['Dimension']}**")
        with col2:
            st.markdown(f"Drift: `{row['Mean Drift']:.3f}`")
        with col3:
            st.markdown(f"<span class='{stability_class}'>{row['Stability']}</span>", unsafe_allow_html=True)

    page_divider()

    # === EXPERIMENT STATUS ===
    st.subheader("Experiment Status")

    exp_col1, exp_col2, exp_col3 = st.columns(3)

    with exp_col1:
        st.markdown("#### EXP1")
        st.metric("Single-Persona Baseline", "Complete", delta="✅ Ziggy validated")
        st.caption("15 responses, framework proven")

    with exp_col2:
        st.markdown("#### EXP2")
        st.metric("Cross-Persona", "Complete", delta="✅ σ² = 0.000869")
        st.caption("5 personas, 3 architectures")

    with exp_col3:
        st.markdown("#### EXP3")
        st.metric("Human Validation", "Ready", delta="⏳ Awaiting raters")
        st.caption("Blind rating protocol ready")

    page_divider()

    # === NOTES ===
    with st.expander("📝 Data Sources & Notes", expanded=False):
        st.markdown("""
        **Data Sources:**
        - PFI scores from EXP2 multi-persona trials
        - Variance calculations from cross-architecture comparison
        - Dimensional drift from S7 Run 005 temporal stability testing

        **Key Findings:**
        - σ² = 0.000869 confirms high cross-persona reconstruction fidelity
        - Identity Core dimension shows highest stability (drift 0.045)
        - Metaphor dimension shows lowest stability (drift 0.100)
        - "Dig-in-heels" pattern observed in fluid dimensions

        **Next Steps:**
        - Complete EXP3 human validation
        - Run AI Armada cross-architecture drift analysis
        - Measure Identity Gravity constant (γ)
        """)


if __name__ == "__main__":
    render()  # Can test page standalone
