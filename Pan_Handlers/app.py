"""
🍳 PAN HANDLERS — The Grand Hall
Cross-Repo Showcase System

A federation of repos: Nyquist, CFA, and more.
Each tile is a doorway into a different project world.
"""

import streamlit as st
import json
from pathlib import Path

# Import page modules
from pages import home, project_view, roadmap, glossary, about

# ========== CONFIGURATION ==========

APP_ROOT = Path(__file__).parent
MANIFESTS_DIR = APP_ROOT / "manifests"

# Remote manifest URLs (for future cross-repo fetching)
MANIFEST_URLS = [
    # "https://raw.githubusercontent.com/ZiggyMack/Nyquist_Consciousness/main/panhandlers_manifest.json",
    # "https://raw.githubusercontent.com/ZiggyMack/CFA/main/panhandlers_manifest.json",
]


def load_local_manifests():
    """Load all manifests from local manifests/ directory."""
    manifests = []
    if MANIFESTS_DIR.exists():
        for manifest_file in MANIFESTS_DIR.glob("*.json"):
            try:
                with open(manifest_file, 'r', encoding='utf-8') as f:
                    manifests.append(json.load(f))
            except Exception as e:
                st.warning(f"Failed to load {manifest_file.name}: {e}")
    return manifests


def load_projects_json():
    """Load flagship projects from projects.json."""
    projects_file = APP_ROOT / "projects.json"
    if projects_file.exists():
        with open(projects_file, 'r', encoding='utf-8') as f:
            return json.load(f)
    return None


# ========== STYLING ==========

def apply_pan_handlers_css():
    """Apply Pan Handlers visual theme."""
    st.markdown("""
    <style>
    /* Hide default Streamlit elements */
    #MainMenu {visibility: hidden;}
    footer {visibility: hidden;}

    /* Pan Handlers Theme */
    .pan-title {
        font-size: 2.8em;
        font-weight: bold;
        background: linear-gradient(135deg, #00ff41 0%, #2a9d8f 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.2em;
        font-family: 'Georgia', serif;
        letter-spacing: 0.05em;
    }

    .pan-subtitle {
        color: #00ff41;
        font-size: 1.2em;
        margin-bottom: 1em;
        font-family: 'Courier New', monospace;
    }

    .philosophy-banner {
        background: linear-gradient(135deg, rgba(0,255,65,0.1) 0%, rgba(42,157,143,0.1) 100%);
        border: 2px solid #00ff41;
        border-radius: 10px;
        padding: 1em;
        text-align: center;
        font-size: 1.3em;
        font-weight: bold;
        color: #00ff41 !important;
        font-family: 'Courier New', monospace;
        margin-bottom: 1.5em;
    }

    .repo-card {
        background: linear-gradient(135deg, rgba(0,255,65,0.08) 0%, rgba(0,204,51,0.03) 100%);
        border: 2px solid #00ff41;
        border-radius: 12px;
        padding: 1.5em;
        margin-bottom: 1em;
        box-shadow: 0 0 20px rgba(0,255,65,0.2);
        transition: all 0.3s ease;
    }

    .repo-card:hover {
        box-shadow: 0 0 30px rgba(0,255,65,0.4);
        transform: translateY(-2px);
    }

    .repo-card h3 {
        color: #00ff41 !important;
        margin-top: 0;
        font-family: 'Georgia', serif;
    }

    .repo-card p {
        color: #333333 !important;
    }

    .project-card {
        background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.05) 100%);
        border: 2px solid #2a9d8f;
        border-radius: 10px;
        padding: 1.2em;
        margin-bottom: 0.8em;
        box-shadow: 0 0 15px rgba(42,157,143,0.15);
    }

    .project-card h4 {
        color: #2a9d8f !important;
        margin-top: 0;
        margin-bottom: 0.5em;
    }

    .status-badge {
        display: inline-block;
        padding: 0.25em 0.6em;
        border-radius: 12px;
        font-size: 0.8em;
        font-weight: bold;
        margin-left: 0.5em;
    }

    .badge-active {
        background: rgba(0,255,65,0.2);
        color: #00ff41;
        border: 1px solid #00ff41;
    }

    .badge-complete {
        background: rgba(42,157,143,0.2);
        color: #2a9d8f;
        border: 1px solid #2a9d8f;
    }

    .badge-incubating {
        background: rgba(255,215,0,0.2);
        color: #b8860b;
        border: 1px solid #ffd700;
    }

    .badge-archived {
        background: rgba(128,128,128,0.2);
        color: #666666;
        border: 1px solid #999999;
    }

    .section-header {
        color: #00ff41 !important;
        font-size: 1.4em;
        font-weight: bold;
        margin-top: 1.5em;
        margin-bottom: 0.8em;
        font-family: 'Georgia', serif;
        border-bottom: 2px solid #00ff41;
        padding-bottom: 0.3em;
    }

    .footer-text {
        text-align: center;
        color: #00ff41;
        font-family: 'Courier New', monospace;
        margin-top: 2em;
        opacity: 0.8;
    }

    /* Sidebar styling */
    section[data-testid="stSidebar"] {
        background: linear-gradient(180deg, #0a0a0a, #1a1a1a) !important;
    }

    section[data-testid="stSidebar"] * {
        color: #f4f4f4 !important;
    }

    section[data-testid="stSidebar"] h1,
    section[data-testid="stSidebar"] h2,
    section[data-testid="stSidebar"] h3 {
        color: #00ff41 !important;
    }
    </style>
    """, unsafe_allow_html=True)


# ========== PAGE ROUTING ==========

PAGES = {
    "🏛️ Hall of Pan Handlers": home,
    "🔍 Project View": project_view,
    "🗺️ Global Roadmap": roadmap,
    "📖 Glossary": glossary,
    "ℹ️ About": about,
}


# ========== MAIN ==========

def main():
    st.set_page_config(
        page_title="Pan Handlers",
        page_icon="🍳",
        layout="wide",
    )

    apply_pan_handlers_css()

    # Load data
    manifests = load_local_manifests()
    projects_data = load_projects_json()

    # Store in session state for pages to access
    st.session_state['manifests'] = manifests
    st.session_state['projects_data'] = projects_data

    # Sidebar navigation
    with st.sidebar:
        st.markdown("### 🍳 Pan Handlers")
        st.markdown("*The Grand Hall*")
        st.markdown("---")

        page_selection = st.radio(
            "Navigate:",
            list(PAGES.keys()),
            label_visibility="collapsed"
        )

        st.markdown("---")
        st.markdown(f"**Repos Connected:** {len(manifests)}")
        if projects_data:
            st.markdown(f"**Flagship Projects:** {len(projects_data.get('flagship_projects', []))}")

        st.markdown("---")
        st.markdown("*Neither could have done it alone.*")

    # Render selected page
    page_module = PAGES.get(page_selection)
    if page_module and hasattr(page_module, 'render'):
        page_module.render()
    else:
        st.error(f"Page '{page_selection}' not found")


if __name__ == "__main__":
    main()
