"""
NYQUIST CONSCIOUSNESS — MISSION CONTROL DASHBOARD (REFACTORED)

Streamlit app with modular page architecture.
Each page is in its own file for independent development.

Design inspired by Mr. Brute's Ledger with "page-turning" aesthetic.
"""

import streamlit as st
from config import PATHS, SETTINGS
from utils import load_status

# Import page modules
from pages import overview, personas, stackup, AI_ARMADA, metrics, omega, avlar, roadmap, glossary, publications, matrix

# ========== THEME & STYLING ==========

LEDGER_COLORS = SETTINGS['colors']

def apply_custom_css():
    """Apply custom CSS for ledger aesthetic."""
    st.markdown("""
    <style>
    /* Hide default Streamlit menu and footer */
    #MainMenu {visibility: hidden;}
    footer {visibility: hidden;}
    header {visibility: hidden;}

    /* Hide Streamlit's default page navigation in sidebar */
    [data-testid="stSidebarNav"] {display: none !important;}
    section[data-testid="stSidebarNav"] {display: none !important;}

    /* Hide the default file list/navigation */
    [data-testid="collapsedControl"] {display: none !important;}

    /* Hide any default nav links */
    nav[role="navigation"] {display: none !important;}

    /* Sidebar styling - dark background with bright text */
    section[data-testid="stSidebar"] {
        background: linear-gradient(180deg, #0a0a0a, #1a1a1a) !important;
    }

    /* Sidebar text - bright for readability */
    section[data-testid="stSidebar"] * {
        color: #f4f4f4 !important;
    }

    /* Sidebar headers */
    section[data-testid="stSidebar"] h1,
    section[data-testid="stSidebar"] h2,
    section[data-testid="stSidebar"] h3 {
        color: #00ff41 !important;
    }

    /* Radio button labels - bright white */
    section[data-testid="stSidebar"] label {
        color: #ffffff !important;
    }

    /* Main background */
    .main {
        background: linear-gradient(135deg, #0a0a0a, #1a1a1a);
    }

    /* Headers */
    h1, h2, h3 {
        color: #f4f4f4 !important;
        font-family: 'Georgia', serif;
    }

    /* Metric cards */
    [data-testid="stMetricValue"] {
        font-size: 2rem;
        color: #7bc043;
    }

    /* Page divider */
    .page-divider {
        border-top: 3px double #666;
        margin: 30px 0;
        opacity: 0.6;
    }
    </style>
    """, unsafe_allow_html=True)

# ========== PAGE ROUTING ==========

PAGE_MODULES = {
    "Overview": overview,
    "Personas": personas,
    "Stack Layers": stackup,
    "AI Armada": AI_ARMADA,
    "Metrics": metrics,
    "Omega & Temporal": omega,
    "AVLAR": avlar,
    "Roadmap": roadmap,
    "Glossary": glossary,
    "Publications": publications,
    "🟢 The Matrix": matrix,
}

# ========== MAIN ==========

def main():
    st.set_page_config(
        page_title="Nyquist Dashboard",
        page_icon="📜",
        layout="wide",
    )

    apply_custom_css()

    status = load_status()

    with st.sidebar:
        st.markdown("### 📜 Nyquist Ledger")

        page = st.radio(
            "Turn the page:",
            list(PAGE_MODULES.keys()),
        )

        st.markdown("---")

        # Branch info with bright styling
        st.markdown(f"""
<div style="color: #00ff41; font-size: 0.85rem; font-family: 'Courier New', monospace;">
<strong>Branch:</strong> <code style="background: rgba(0,255,65,0.1); padding: 2px 6px; border-radius: 3px;">{status.get('current_branch', 'unknown')}</code><br/>
<strong>Freeze:</strong> <code style="background: rgba(0,255,65,0.1); padding: 2px 6px; border-radius: 3px;">{status.get('freeze', {}).get('branch', 'unknown')}</code>
</div>
        """, unsafe_allow_html=True)

    # Route to selected page module
    page_module = PAGE_MODULES.get(page)
    if page_module and hasattr(page_module, 'render'):
        page_module.render()
    else:
        st.error(f"Page module '{page}' not found or missing render() function")


if __name__ == "__main__":
    main()
