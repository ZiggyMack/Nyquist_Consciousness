"""
METRICS PAGE — Metrics & Comparison Dashboard

Visualizes PFI, σ², and comparison matrices across architectures/personas.
Includes dB scale view for better comparison of close values.
"""

import streamlit as st
import pandas as pd
import math
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


def to_db(value, reference=1.0):
    """Convert linear value to decibels."""
    if value <= 0:
        return -60  # Floor for zero/negative values
    return 20 * math.log10(value / reference)


def render():
    """Render the Metrics & Comparison page."""

    # Compact CSS
    st.markdown("""
    <style>
    .metrics-title {
        font-size: 1.8em;
        font-weight: bold;
        background: linear-gradient(135deg, #2a9d8f 0%, #264653 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.2em;
    }
    .metrics-subtitle {
        color: #2a9d8f;
        font-size: 0.95em;
        margin-bottom: 0.8em;
    }
    .key-metric-compact {
        text-align: center;
        padding: 0.8em;
        background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(38,70,83,0.05) 100%);
        border: 1px solid #2a9d8f;
        border-radius: 8px;
    }
    .metric-value-sm {
        font-size: 1.4em;
        font-weight: bold;
        color: #2a9d8f !important;
    }
    .metric-label-sm {
        color: #666 !important;
        font-size: 0.75em;
        margin-top: 0.2em;
    }
    .stability-high { color: #2a9d8f; font-weight: bold; }
    .stability-medium { color: #f4a261; font-weight: bold; }
    .stability-low { color: #e76f51; font-weight: bold; }
    .stability-very-low { color: #c62828; font-weight: bold; }
    .db-value {
        font-family: 'Courier New', monospace;
        font-weight: bold;
        color: #3b82f6 !important;
    }
    .linear-value {
        font-family: 'Courier New', monospace;
        color: #2a9d8f !important;
    }
    .comparison-row {
        display: flex;
        align-items: center;
        padding: 0.4em 0.6em;
        border-bottom: 1px solid rgba(42,157,143,0.2);
    }
    .comparison-row:hover {
        background: rgba(42,157,143,0.05);
    }
    .bar-container {
        flex: 1;
        height: 20px;
        background: rgba(42,157,143,0.1);
        border-radius: 4px;
        margin: 0 0.5em;
        position: relative;
        overflow: hidden;
    }
    .bar-fill-linear {
        height: 100%;
        background: linear-gradient(90deg, #2a9d8f 0%, #264653 100%);
        border-radius: 4px;
        transition: width 0.3s ease;
    }
    .bar-fill-db {
        height: 100%;
        background: linear-gradient(90deg, #3b82f6 0%, #8b5cf6 100%);
        border-radius: 4px;
        transition: width 0.3s ease;
    }
    </style>
    """, unsafe_allow_html=True)

    # Header - more compact
    st.markdown('<div class="metrics-title">Metrics Dashboard</div>', unsafe_allow_html=True)
    st.markdown('<div class="metrics-subtitle">PFI, Variance & Dimensional Stability Analysis</div>', unsafe_allow_html=True)

    # === KEY METRICS - Compact Row ===
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.markdown("""
        <div class="key-metric-compact">
            <div class="metric-value-sm">σ² = 0.000869</div>
            <div class="metric-label-sm">Cross-Persona Variance</div>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="key-metric-compact">
            <div class="metric-value-sm">0.887</div>
            <div class="metric-label-sm">Mean PFI Score</div>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        st.markdown("""
        <div class="key-metric-compact">
            <div class="metric-value-sm">5</div>
            <div class="metric-label-sm">Personas Tested</div>
        </div>
        """, unsafe_allow_html=True)

    with col4:
        st.markdown("""
        <div class="key-metric-compact">
            <div class="metric-value-sm">3</div>
            <div class="metric-label-sm">Architectures</div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === PERSONA FIDELITY INDEX - WITH dB TOGGLE ===
    st.markdown("### Persona Fidelity Index (PFI)")

    # Scale toggle
    scale_mode = st.radio(
        "View Mode:",
        ["📊 Linear Scale", "📈 dB Scale (spreads differences)"],
        horizontal=True,
        key="pfi_scale"
    )

    use_db = "dB" in scale_mode

    if use_db:
        st.info("💡 **dB Scale:** Spreads out closely-spaced values. PFI of 0.905 → -0.87 dB, 0.867 → -1.24 dB. The ~0.4 dB difference is now visible!")

    # Build comparison data
    persona_df = pd.DataFrame(PERSONA_DATA)

    # Calculate dB values (reference = 1.0 for PFI)
    persona_df['pfi_dB'] = persona_df['pfi'].apply(lambda x: to_db(x, 1.0))
    persona_df['variance_dB'] = persona_df['variance'].apply(lambda x: to_db(x, 0.001))  # Reference 0.001 for variance

    # Display table with both scales
    st.markdown("#### Comparison Table")

    if use_db:
        # dB scale display
        display_df = pd.DataFrame({
            'Persona': persona_df['persona'],
            'PFI (Linear)': persona_df['pfi'].apply(lambda x: f"{x:.3f}"),
            'PFI (dB)': persona_df['pfi_dB'].apply(lambda x: f"{x:.2f} dB"),
            'Δ from Best': persona_df['pfi_dB'].apply(lambda x: f"{x - persona_df['pfi_dB'].max():.2f} dB"),
            'Status': persona_df['status']
        })
    else:
        # Linear scale display
        display_df = pd.DataFrame({
            'Persona': persona_df['persona'],
            'PFI': persona_df['pfi'].apply(lambda x: f"{x:.3f}"),
            'Variance (σ²)': persona_df['variance'].apply(lambda x: f"{x:.4f}"),
            'Status': persona_df['status']
        })

    st.table(display_df)

    # Visual bar comparison
    st.markdown("#### Visual Comparison")

    if use_db:
        # dB scale bars - normalize to 0-100% range
        db_min = persona_df['pfi_dB'].min()
        db_max = persona_df['pfi_dB'].max()
        db_range = db_max - db_min if db_max != db_min else 1

        for _, row in persona_df.iterrows():
            # Normalize dB value to percentage (inverted - closer to 0 dB is better)
            pct = ((row['pfi_dB'] - db_min) / db_range) * 100
            delta = row['pfi_dB'] - db_max

            st.markdown(f"""
            <div class="comparison-row">
                <span style="width: 80px; font-weight: bold;">{row['persona']}</span>
                <div class="bar-container">
                    <div class="bar-fill-db" style="width: {pct}%;"></div>
                </div>
                <span class="db-value" style="width: 70px; text-align: right;">{row['pfi_dB']:.2f} dB</span>
                <span style="width: 60px; text-align: right; color: #666; font-size: 0.8em;">({delta:.2f})</span>
            </div>
            """, unsafe_allow_html=True)
    else:
        # Linear scale bars
        pfi_min = 0.85  # Floor for visualization
        pfi_max = persona_df['pfi'].max()
        pfi_range = pfi_max - pfi_min

        for _, row in persona_df.iterrows():
            pct = ((row['pfi'] - pfi_min) / pfi_range) * 100 if pfi_range > 0 else 100

            st.markdown(f"""
            <div class="comparison-row">
                <span style="width: 80px; font-weight: bold;">{row['persona']}</span>
                <div class="bar-container">
                    <div class="bar-fill-linear" style="width: {pct}%;"></div>
                </div>
                <span class="linear-value" style="width: 60px; text-align: right;">{row['pfi']:.3f}</span>
            </div>
            """, unsafe_allow_html=True)

    page_divider()

    # === DIMENSIONAL STABILITY - WITH dB ===
    st.markdown("### Dimensional Stability Analysis")
    st.caption("Mean drift rates across 6 identity dimensions (from S7 Run 005)")

    dim_scale = st.radio(
        "Drift Scale:",
        ["📊 Linear", "📈 dB Scale"],
        horizontal=True,
        key="dim_scale"
    )

    dim_use_db = "dB" in dim_scale

    dim_df = pd.DataFrame(DIMENSION_DATA)
    dim_df['drift_dB'] = dim_df['mean_drift'].apply(lambda x: to_db(x, 0.1))  # Reference 0.1 for drift

    # Compact dimension display
    for _, row in dim_df.iterrows():
        stability_class = f"stability-{row['stability'].lower().replace(' ', '-')}"

        if dim_use_db:
            drift_display = f"{to_db(row['mean_drift'], 0.1):.1f} dB"
        else:
            drift_display = f"{row['mean_drift']:.3f}"

        col1, col2, col3 = st.columns([3, 2, 1])
        with col1:
            st.markdown(f"**{row['dimension']}**")
        with col2:
            st.markdown(f"`{drift_display}`")
        with col3:
            st.markdown(f"<span class='{stability_class}'>{row['stability']}</span>", unsafe_allow_html=True)

    page_divider()

    # === EXPERIMENT STATUS - Compact ===
    st.markdown("### Experiment Status")

    exp_col1, exp_col2, exp_col3 = st.columns(3)

    with exp_col1:
        st.markdown("**EXP1** — Single-Persona")
        st.success("✅ Complete")
        st.caption("Ziggy baseline, 15 responses")

    with exp_col2:
        st.markdown("**EXP2** — Cross-Persona")
        st.success("✅ Complete")
        st.caption("σ² = 0.000869, 5 personas")

    with exp_col3:
        st.markdown("**EXP3** — Human Validation")
        st.warning("⏳ Ready")
        st.caption("Awaiting human raters")

    page_divider()

    # === dB EXPLANATION ===
    with st.expander("📖 Understanding dB Scale", expanded=False):
        st.markdown("""
        ### Why Use Decibels for Identity Metrics?

        **The Problem:** PFI values are clustered between 0.867 and 0.905 — a difference of only 0.038 in linear terms. This makes visual comparison nearly impossible.

        **The Solution:** Convert to decibels (dB), a logarithmic scale that spreads out closely-spaced values.

        **Formula:** `dB = 20 × log₁₀(value / reference)`

        **For PFI (reference = 1.0):**
        | Persona | Linear PFI | dB Value | Δ from Best |
        |---------|------------|----------|-------------|
        | Ziggy   | 0.905      | -0.87 dB | 0.00 dB     |
        | Nova    | 0.890      | -1.01 dB | -0.14 dB    |
        | Claude  | 0.887      | -1.04 dB | -0.17 dB    |
        | Grok    | 0.880      | -1.11 dB | -0.24 dB    |
        | Gemini  | 0.867      | -1.24 dB | -0.37 dB    |

        Now we can see: Gemini is **0.37 dB** below Ziggy — a meaningful, visible difference!

        **Interpretation:**
        - **0 dB** = perfect fidelity (PFI = 1.0)
        - **Negative dB** = below perfect (all real values)
        - **Closer to 0** = better fidelity
        - **Each 3 dB** ≈ 2× difference in power
        """)

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
    render()
