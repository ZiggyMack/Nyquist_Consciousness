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
    """Apply custom CSS for light theme with dark sidebar."""
    st.markdown("""
    <style>
    /* Hide default Streamlit menu and footer */
    #MainMenu {visibility: hidden;}
    footer {visibility: hidden;}
    header {visibility: hidden;}

    /* Hide Streamlit's default page navigation in sidebar */
    [data-testid="stSidebarNav"] {display: none !important;}
    section[data-testid="stSidebarNav"] {display: none !important;}
    nav[role="navigation"] {display: none !important;}

    /* ===== LIGHT THEME FOR MAIN CONTENT ===== */
    .stApp {
        background: #ffffff !important;
    }

    .main .block-container {
        background: #ffffff !important;
    }

    /* ===== ALL TEXT BLACK BY DEFAULT ===== */
    .main, .main * {
        color: #1a1a1a !important;
    }

    /* ===== SIDEBAR - KEEP DARK ===== */
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
        font-weight: bold;
    }

    section[data-testid="stSidebar"] label {
        color: #ffffff !important;
        font-weight: 500;
    }

    section[data-testid="stSidebar"] hr {
        border-color: #00ff41 !important;
        opacity: 0.3;
    }

    /* ===== HEADERS ===== */
    h1, h2, h3, h4, h5, h6 {
        color: #1a1a1a !important;
        font-family: 'Georgia', serif;
        font-weight: bold !important;
    }

    h1 {
        border-bottom: 2px solid #2a9d8f;
        padding-bottom: 0.5rem;
    }

    /* ===== TEXT ELEMENTS ===== */
    p, span, div, li, label {
        color: #333333 !important;
    }

    /* Strong/bold text - teal accent */
    strong, b {
        color: #2a9d8f !important;
    }

    /* Italic/emphasis */
    em, i {
        color: #555555 !important;
    }

    /* Links */
    a {
        color: #2a9d8f !important;
    }

    /* ===== METRIC CARDS ===== */
    [data-testid="stMetricValue"] {
        font-size: 2rem;
        color: #2a9d8f !important;
        font-weight: bold;
    }

    [data-testid="stMetricLabel"] {
        color: #333333 !important;
        font-size: 1rem;
    }

    [data-testid="stMetricDelta"] {
        font-size: 0.875rem;
    }

    /* ===== EXPANDERS ===== */
    [data-testid="stExpander"] {
        background: #f8f9fa !important;
        border: 1px solid #dee2e6 !important;
        border-radius: 8px;
    }

    [data-testid="stExpander"] summary {
        color: #2a9d8f !important;
    }

    [data-testid="stExpander"] * {
        color: #333333 !important;
    }

    /* ===== CODE BLOCKS ===== */
    code {
        background: #f1f3f4 !important;
        color: #d63384 !important;
        padding: 2px 6px;
        border-radius: 3px;
        font-family: 'Courier New', monospace;
    }

    pre {
        background: #f8f9fa !important;
        color: #333333 !important;
    }

    /* ===== TABLES & DATAFRAMES ===== */
    table, [data-testid="stTable"], .stDataFrame {
        color: #333333 !important;
    }

    th {
        background: #2a9d8f !important;
        color: #ffffff !important;
        font-weight: bold;
    }

    td {
        color: #333333 !important;
        border-bottom: 1px solid #dee2e6;
    }

    /* Dataframe specific */
    [data-testid="stDataFrame"] div {
        color: #333333 !important;
    }

    /* ===== BUTTONS ===== */
    .stButton > button {
        background: #2a9d8f !important;
        color: #ffffff !important;
        border: 1px solid #2a9d8f !important;
        border-radius: 8px;
        font-weight: 500;
        transition: all 0.3s ease;
    }

    .stButton > button:hover {
        background: #238b7e !important;
        border-color: #238b7e !important;
        box-shadow: 0 2px 8px rgba(42, 157, 143, 0.3);
    }

    /* ===== CAPTIONS ===== */
    .stCaption, [data-testid="stCaptionContainer"] {
        color: #666666 !important;
    }

    /* ===== PAGE DIVIDER ===== */
    .page-divider {
        border-top: 3px double #dee2e6;
        margin: 30px 0;
        opacity: 0.6;
    }

    /* Horizontal rules */
    hr {
        border-color: #dee2e6 !important;
    }

    /* ===== INPUTS ===== */
    input, textarea, select {
        background: #ffffff !important;
        color: #333333 !important;
        border: 1px solid #ced4da !important;
    }

    /* ===== RADIO BUTTONS ===== */
    [data-testid="stRadio"] label {
        color: #333333 !important;
    }

    /* ===== WARNINGS/INFO/SUCCESS/ERROR ===== */
    .stAlert {
        color: #333333 !important;
    }
    </style>
    """, unsafe_allow_html=True)

# ========== PAGE ROUTING ==========

PAGE_MODULES = {
    "Overview": overview,
    "Personas": personas,
    "Stackup": stackup,
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

        # Quick refresh button
        if st.button("🔄 Refresh", use_container_width=True):
            st.cache_data.clear()
            st.rerun()

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
