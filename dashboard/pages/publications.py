"""
PUBLICATIONS PAGE — Publications & White Papers

Displays publication drafts and white papers from the paper/ directory.
"""

import streamlit as st
from pathlib import Path
from config import PATHS
from utils import load_markdown_file

REPO_ROOT = PATHS['repo_root']

def render():
    """Render the Publications page."""
    st.title("📄 Publications & White Papers")

    paper_root = REPO_ROOT / "paper"
    if not paper_root.exists():
        st.info("No paper/ directory found yet.")
        return

    st.markdown(f"Paper root: `{paper_root}`")

    for sub in sorted(paper_root.iterdir()):
        if sub.is_dir():
            st.subheader(sub.name)
            md_files = list(sub.glob("*.md"))
            if not md_files:
                st.write("_No markdown files yet._")
            for md in md_files:
                with st.expander(md.name):
                    st.markdown(load_markdown_file(md))


if __name__ == "__main__":
    render()  # Can test page standalone
