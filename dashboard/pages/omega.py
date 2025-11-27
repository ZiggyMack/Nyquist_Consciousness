"""
OMEGA PAGE — Omega & Temporal Wing

Displays Omega sessions and S7 temporal stability information.
"""

import streamlit as st
from pathlib import Path
from config import PATHS
from utils import load_markdown_file, page_divider

REPO_ROOT = PATHS['repo_root']

def render():
    """Render the Omega & Temporal page."""
    st.title("⚡ Omega & Temporal Wing")

    # Omega sessions
    st.subheader("Omega Sessions")
    ledger = REPO_ROOT / "logs" / "OMEGA_LEDGER.md"
    if ledger.exists():
        with st.expander("📜 Omega Ledger"):
            st.markdown(load_markdown_file(ledger))
    else:
        st.info("No OMEGA_LEDGER.md found yet.")

    page_divider()

    # S7 temporal
    st.subheader("Temporal Stability (S7)")
    s7_map = REPO_ROOT / "docs" / "S7" / "S7_NYQUIST_TEMPORAL_MAP.md"
    if s7_map.exists():
        with st.expander("🗺️ Temporal Map"):
            st.markdown(load_markdown_file(s7_map))
    else:
        st.info("No S7 temporal map found yet.")


if __name__ == "__main__":
    render()  # Can test page standalone
