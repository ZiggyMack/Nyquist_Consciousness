"""
STACK LAYERS PAGE — S# Stack Wings

Displays each layer of the S# stack with status and specifications.
"""

import streamlit as st
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_status, load_markdown_file, ledger_card

# Unpack paths
REPO_ROOT = PATHS['repo_root']
LEDGER_COLORS = SETTINGS['colors']

def render():
    """Render the Stack Layers page."""
    status = load_status()

    st.title("🏛️ S# Stack Wings")

    layers = status.get("layers", {})
    ordered_layers = sorted(layers.items())

    selected = st.radio(
        "Select a layer (S#):",
        [name for name, _ in ordered_layers],
        horizontal=False
    )

    info = layers.get(selected, {})
    badge_color = LEDGER_COLORS.get(info.get("status"), "#999")

    body = f"""
**Name:** {info.get('name', 'Unknown')}
**Status:** `{info.get('status', 'unknown').upper()}`
**Spec:** `{info.get('spec', 'n/a')}`
**Notes:** {info.get('notes', 'None')}
    """

    ledger_card(f"Layer {selected}", body_md=body, badge=info.get("status", "").upper(), badge_color=badge_color)

    # Load spec file
    spec_path = info.get("spec")
    if spec_path:
        spec_file = REPO_ROOT / spec_path
        if spec_file.exists():
            with st.expander("📄 View Spec"):
                st.markdown(load_markdown_file(spec_file))
        else:
            st.info(f"Spec file not found at `{spec_path}`.")


if __name__ == "__main__":
    render()  # Can test page standalone
