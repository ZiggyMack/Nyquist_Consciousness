"""
NYQUIST CONSCIOUSNESS DASHBOARD — SHARED UTILITIES

Shared functions used across multiple dashboard pages.
"""

import json
import re
import streamlit as st
from pathlib import Path
from config import PATHS

# Unpack paths
REPO_ROOT = PATHS['repo_root']
PERSONAS_DIR = PATHS['personas_dir']

# ========== DATA LOADERS ==========

@st.cache_data(ttl=60)
def load_status():
    """Load NYQUIST_STATUS.json."""
    status_file = PATHS['status_file']
    if status_file.exists():
        with open(status_file, "r", encoding="utf-8") as f:
            return json.load(f)
    else:
        st.warning(f"STATUS_FILE not found at: {status_file}")
    return {}

@st.cache_data
def load_personas():
    """Load all persona markdown files."""
    personas = []
    if not PERSONAS_DIR.exists():
        return personas

    for path in sorted(PERSONAS_DIR.glob("*.md")):
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()
        title = None
        for line in lines:
            if line.startswith("# "):
                title = line.lstrip("# ").strip()
                break
        personas.append({
            "name": title or path.stem,
            "path": path,
            "preview": "\n".join(lines[:50])
        })
    return personas

@st.cache_data
def load_markdown_file(file_path):
    """Load and return markdown file contents."""
    try:
        return Path(file_path).read_text(encoding="utf-8")
    except Exception as e:
        return f"_Error loading file: {e}_"

def load_publication_status():
    """Load publication_status.json."""
    pub_file = REPO_ROOT / "publication_status.json"
    if pub_file.exists():
        return json.loads(pub_file.read_text(encoding="utf-8"))
    return {}

def load_glossary_entries(text):
    """Parse glossary markdown into term/definition pairs."""
    entries = []
    current_term = None
    current_lines = []

    for line in text.splitlines():
        if line.startswith("## "):
            if current_term:
                entries.append({
                    "term": current_term,
                    "definition": "\n".join(current_lines).strip()
                })
            current_term = line.lstrip("# ").strip()
            current_lines = []
        else:
            current_lines.append(line)

    if current_term:
        entries.append({
            "term": current_term,
            "definition": "\n".join(current_lines).strip()
        })

    return entries

# ========== UI COMPONENTS ==========

def page_divider():
    """Visual page turn separator."""
    st.markdown('<div class="page-divider"></div>', unsafe_allow_html=True)

def ledger_card(title, body_md="", badge="", badge_color="#999"):
    """
    Render a card with ledger-like styling.

    Args:
        title: Card header title
        body_md: Markdown content for card body
        badge: Optional badge text
        badge_color: Badge background color
    """
    badge_html = ""
    if badge:
        badge_html = f'<span style="background: {badge_color}; color: white; padding: 2px 8px; border-radius: 4px; font-size: 0.7rem; margin-left: 10px;">{badge}</span>'

    # Card header with HTML styling
    st.markdown(f"""
    <div style="background: linear-gradient(135deg, #1a1a1a, #2a2a2a);
                border: 2px solid {badge_color};
                border-radius: 8px;
                padding: 20px;
                margin: 15px 0;">
        <h3 style="color: {badge_color}; margin: 0 0 15px 0;">
            {title} {badge_html}
        </h3>
    </div>
    """, unsafe_allow_html=True)

    # Render body_md as proper Streamlit markdown (not in HTML)
    if body_md:
        st.markdown(body_md)

    # Add spacing
    st.markdown("---")
