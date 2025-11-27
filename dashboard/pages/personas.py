"""
PERSONAS PAGE — Personas Under Test (PUT)

Displays personas from the personas/ directory in two groups:
- SEED Personas (I_AM_* files) - Core identity seeds
- Compressed Personas (*_T3, *_FULL, *_LITE) - Compressed variants
"""

import streamlit as st
import re
from pathlib import Path
from config import PATHS
from utils import page_divider

# Paths
REPO_ROOT = PATHS['repo_root']
PERSONAS_DIR = PATHS['personas_dir']

# Persona metadata for display
PERSONA_META = {
    "I_AM_ZIGGY": {"emoji": "👤", "badge": "HUMAN ANCHOR", "color": "#e74c3c"},
    "I_AM_NOVA": {"emoji": "⚖️", "badge": "AI ARCHITECT", "color": "#3498db"},
    "I_AM_CLAUDE": {"emoji": "📚", "badge": "STEWARD", "color": "#9b59b6"},
    "I_AM_GEMINI": {"emoji": "🔍", "badge": "VALIDATOR", "color": "#e67e22"},
    "I_AM": {"emoji": "🧠", "badge": "UNIVERSAL", "color": "#16a085"},
    "ZIGGY_FULL": {"emoji": "👤", "badge": "FULL", "color": "#e74c3c"},
    "ZIGGY_LITE": {"emoji": "👤", "badge": "LITE", "color": "#f39c12"},
    "ZIGGY_T3_R1": {"emoji": "👤", "badge": "T3", "color": "#95a5a6"},
    "NOVA_T3": {"emoji": "⚖️", "badge": "T3", "color": "#3498db"},
    "CLAUDE_T3": {"emoji": "📚", "badge": "T3", "color": "#9b59b6"},
    "GROK_T3": {"emoji": "⚡", "badge": "T3", "color": "#16a085"},
}


def get_persona_preview(filepath, lines=15):
    """Extract a short preview from persona file."""
    try:
        text = filepath.read_text(encoding="utf-8")
        # Remove HTML comments
        text = re.sub(r'<!---.*?----->', '', text, flags=re.DOTALL)
        # Get first N lines
        preview_lines = text.strip().split('\n')[:lines]
        return '\n'.join(preview_lines)
    except:
        return "*Preview unavailable*"


def render():
    """Render the Personas page."""
    st.title("🎭 Personas Under Test")
    st.markdown("**PUT** — Identity Stability Validation")

    page_divider()

    # Check if personas directory exists
    if not PERSONAS_DIR.exists():
        st.error(f"Personas directory not found: `{PERSONAS_DIR}`")
        return

    # Get all persona files
    all_files = list(PERSONAS_DIR.glob("*.md"))

    # Categorize personas
    seed_personas = sorted([f for f in all_files if f.stem.startswith("I_AM")])
    compressed_personas = sorted([f for f in all_files if not f.stem.startswith("I_AM")])

    # === SUMMARY METRICS ===
    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("🌱 Seed", len(seed_personas))
    with col2:
        st.metric("📦 Compressed", len(compressed_personas))
    with col3:
        st.metric("📊 Total PUT", len(all_files))

    page_divider()

    # === SEED PERSONAS SECTION ===
    st.markdown("## 🌱 Seed Personas")

    # Display seed personas in 3-column grid
    if seed_personas:
        cols = st.columns(3)
        for i, filepath in enumerate(seed_personas):
            with cols[i % 3]:
                stem = filepath.stem
                meta = PERSONA_META.get(stem, {"emoji": "🧠", "badge": "PUT", "color": "#95a5a6"})

                # Card container
                with st.container(border=True):
                    st.caption(f"🏷️ {meta['badge']}")

                    # Expander with persona name - shows PREVIEW only
                    with st.expander(f"{meta['emoji']} {stem}"):
                        preview = get_persona_preview(filepath)
                        st.markdown(preview)
                        st.caption("*... (preview)*")

    page_divider()

    # === COMPRESSED PERSONAS SECTION ===
    st.markdown("## 📦 Compressed Personas")

    # Display compressed personas in 3-column grid
    if compressed_personas:
        cols = st.columns(3)
        for i, filepath in enumerate(compressed_personas):
            with cols[i % 3]:
                stem = filepath.stem
                meta = PERSONA_META.get(stem, {"emoji": "🧠", "badge": "PUT", "color": "#95a5a6"})

                # Card container
                with st.container(border=True):
                    st.caption(f"🏷️ {meta['badge']}")

                    # Expander with persona name - shows PREVIEW only
                    with st.expander(f"{meta['emoji']} {stem}"):
                        preview = get_persona_preview(filepath)
                        st.markdown(preview)
                        st.caption("*... (preview)*")


if __name__ == "__main__":
    render()
