"""
AVLAR PAGE — S9 Cross-Modal Ritual

Displays AVLAR (Audio-Visual-Linguistic Alignment Ritual) documentation and sessions.
"""

import streamlit as st
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_markdown_file, ledger_card

REPO_ROOT = PATHS['repo_root']
LEDGER_COLORS = SETTINGS['colors']

def render():
    """Render the AVLAR page."""
    st.title("🎨 S9 — AVLAR (Cross-Modal Ritual)")

    avlar_readme = REPO_ROOT / "docs" / "S9" / "AVLAR_README.md"
    method = REPO_ROOT / "docs" / "S9" / "AVLAR_METHOD.md"
    quick_ref = REPO_ROOT / "docs" / "S9" / "AVLAR_QUICK_REFERENCE.md"

    if avlar_readme.exists():
        ledger_card("AVLAR Overview", load_markdown_file(avlar_readme), badge="AVLAR", badge_color=LEDGER_COLORS.get("armada", "#2a9d8f"))
    else:
        st.warning("AVLAR_README.md not found in docs/S9/.")

    cols = st.columns(2)
    with cols[0]:
        if method.exists():
            st.markdown("### Method")
            st.markdown(load_markdown_file(method))
    with cols[1]:
        if quick_ref.exists():
            st.markdown("### Quick Reference")
            st.markdown(load_markdown_file(quick_ref))

    # AVLAR session logs
    avlar_logs_dir = REPO_ROOT / "logs" / "avlar"
    if avlar_logs_dir.exists():
        st.subheader("Recent AVLAR Sessions")
        logs = sorted(avlar_logs_dir.glob("*.md"))
        if logs:
            selected = st.selectbox("Select a session log:", [p.name for p in logs])
            path = avlar_logs_dir / selected
            with st.expander(selected):
                st.markdown(load_markdown_file(path))
        else:
            st.info("No AVLAR session logs found in logs/avlar/.")
    else:
        st.info("No logs/avlar/ directory found yet.")


if __name__ == "__main__":
    render()  # Can test page standalone
