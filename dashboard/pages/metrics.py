"""
METRICS PAGE — Metrics & Comparison Dashboard

Visualizes PFI, σ², and comparison matrices across architectures/personas.
"""

import streamlit as st
import pandas as pd
from config import PATHS, SETTINGS
from utils import ledger_card, page_divider

LEDGER_COLORS = SETTINGS['colors']

def render():
    """Render the Metrics & Comparison page."""
    st.title("📊 Metrics & Comparison Dashboard")

    st.markdown("This page visualizes PFI, σ², and comparison matrices across architectures/personas.")

    # TODO: Wire to real experiment data
    example_data = {
        "Persona": ["Ziggy", "Nova", "Claude", "Grok", "Gemini"],
        "Mean PFI": [0.905, 0.890, 0.887, 0.880, 0.867],
    }
    df = pd.DataFrame(example_data)

    ledger_card("Persona Fidelity Snapshot (EXP2)", body_md=df.to_markdown(index=False), badge="METRICS")

    st.bar_chart(df.set_index("Persona"))

    page_divider()

    st.info("🔧 Hook this page to EXPERIMENT_2 results, EXPERIMENT_3 analysis, and comparison matrices.")


if __name__ == "__main__":
    render()  # Can test page standalone
