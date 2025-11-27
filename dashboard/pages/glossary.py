"""
GLOSSARY PAGE — Glossary

Searchable glossary of terms used in the Nyquist Consciousness project.
"""

import streamlit as st
from config import PATHS
from utils import load_markdown_file, load_glossary_entries, ledger_card

GLOSSARY_FILE = PATHS['glossary']

def render():
    """Render the Glossary page."""
    st.title("📖 Glossary")

    text = load_markdown_file(GLOSSARY_FILE)
    entries = load_glossary_entries(text)

    if not entries:
        st.info("Could not parse glossary entries. Check GLOSSARY.md format.")
        st.markdown(text)
        return

    query = st.text_input("🔍 Search term:")
    filtered = entries
    if query:
        filtered = [e for e in entries if query.lower() in e["term"].lower()]

    for entry in filtered:
        ledger_card(entry["term"], body_md=entry["definition"])


if __name__ == "__main__":
    render()  # Can test page standalone
