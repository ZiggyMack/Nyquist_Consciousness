"""
ROADMAP PAGE — Live Roadmap

Displays the Nyquist Consciousness project roadmap.
"""

import streamlit as st
from config import PATHS, SETTINGS
from utils import load_markdown_file, ledger_card

ROADMAP_FILE = PATHS['roadmap']
LEDGER_COLORS = SETTINGS['colors']

def render():
    """Render the Roadmap page."""
    st.title("🗺️ Live Roadmap")

    text = load_markdown_file(ROADMAP_FILE)
    ledger_card("Nyquist Roadmap", body_md=text, badge="ROADMAP", badge_color=LEDGER_COLORS.get("design", "#f4a261"))


if __name__ == "__main__":
    render()  # Can test page standalone
