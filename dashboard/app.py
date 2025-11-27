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
    """Apply custom CSS for Matrix theme - green on black terminal aesthetic."""
    st.markdown("""
    <style>
    /* ===== MATRIX THEME - GREEN ON BLACK TERMINAL AESTHETIC ===== */

    /* Hide default Streamlit menu and footer */
    #MainMenu {visibility: hidden;}
    footer {visibility: hidden;}
    header {visibility: hidden;}

    /* Hide Streamlit's default page navigation in sidebar */
    [data-testid="stSidebarNav"] {display: none !important;}
    section[data-testid="stSidebarNav"] {display: none !important;}
    nav[role="navigation"] {display: none !important;}

    /* ===== BASE - BLACK BACKGROUND ===== */
    .stApp {
        background-color: #0a0a0a !important;
    }

    .main .block-container {
        background-color: #0a0a0a !important;
    }

    /* ===== ALL TEXT MATRIX GREEN ===== */
    .stApp p, .stApp span, .stApp label, .stApp li,
    .stApp h1, .stApp h2, .stApp h3, .stApp h4, .stApp h5, .stApp h6,
    .stApp div {
        color: #00ff41 !important;
    }

    /* ===== SIDEBAR - DARK WITH GREEN ACCENTS ===== */
    section[data-testid="stSidebar"] {
        background-color: #0d0d0d !important;
    }

    section[data-testid="stSidebar"] * {
        color: #00ff41 !important;
    }

    section[data-testid="stSidebar"] h1,
    section[data-testid="stSidebar"] h2,
    section[data-testid="stSidebar"] h3 {
        color: #00ff41 !important;
        font-weight: bold;
        font-family: 'Courier New', monospace;
    }

    section[data-testid="stSidebar"] label {
        color: #00ff41 !important;
        font-weight: 500;
    }

    section[data-testid="stSidebar"] hr {
        border-color: #00ff41 !important;
        opacity: 0.5;
    }

    section[data-testid="stSidebar"] code {
        background: rgba(0,255,65,0.1) !important;
        color: #00ff41 !important;
    }

    /* ===== HEADERS - MATRIX GREEN WITH MONOSPACE ===== */
    h1, h2, h3, h4, h5, h6 {
        color: #00ff41 !important;
        font-family: 'Courier New', monospace;
        font-weight: bold !important;
    }

    h1 {
        border-bottom: 2px solid #00ff41;
        padding-bottom: 0.5rem;
    }

    /* ===== TEXT ELEMENTS ===== */
    p, span, div, li, label {
        color: #00ff41 !important;
    }

    /* Strong/bold text - bright green */
    strong, b {
        color: #00ff41 !important;
        text-shadow: 0 0 5px rgba(0,255,65,0.5);
    }

    /* Italic/emphasis - dimmer green */
    em, i {
        color: #00cc33 !important;
    }

    /* Links - dimmer green */
    a {
        color: #00cc33 !important;
    }

    a:hover {
        color: #00ff41 !important;
        text-shadow: 0 0 10px rgba(0,255,65,0.5);
    }

    /* ===== METRIC CARDS ===== */
    [data-testid="stMetricValue"] {
        font-size: 2rem;
        color: #00ff41 !important;
        font-weight: bold;
        font-family: 'Courier New', monospace;
    }

    [data-testid="stMetricLabel"] {
        color: #00ff41 !important;
        font-size: 1rem;
    }

    [data-testid="stMetricDelta"] {
        font-size: 0.875rem;
        color: #00cc33 !important;
    }

    /* ===== EXPANDERS - DARK WITH GREEN BORDER ===== */
    [data-testid="stExpander"] {
        background-color: #0d0d0d !important;
        border: 1px solid #00ff41 !important;
        border-radius: 8px;
    }

    [data-testid="stExpander"] summary {
        color: #00ff41 !important;
    }

    [data-testid="stExpander"] * {
        color: #00ff41 !important;
    }

    /* ===== CODE BLOCKS ===== */
    code {
        background: rgba(0,255,65,0.1) !important;
        color: #00ff41 !important;
        padding: 2px 6px;
        border-radius: 3px;
        font-family: 'Courier New', monospace;
    }

    pre {
        background: #0d0d0d !important;
        color: #00ff41 !important;
        border: 1px solid #00ff41;
    }

    /* ===== TABLES & DATAFRAMES ===== */
    table, [data-testid="stTable"], .stDataFrame {
        color: #00ff41 !important;
        background-color: #0d0d0d !important;
    }

    th {
        background: #004d1a !important;
        color: #00ff41 !important;
        font-weight: bold;
        border: 1px solid #00ff41 !important;
    }

    td {
        color: #00ff41 !important;
        border-bottom: 1px solid #00ff41;
        background-color: #0d0d0d !important;
    }

    /* Dataframe specific */
    [data-testid="stDataFrame"] div {
        color: #00ff41 !important;
    }

    [data-testid="stDataFrame"] {
        background-color: #0d0d0d !important;
    }

    /* ===== BUTTONS - DEFAULT STATE ===== */
    .stButton > button {
        background-color: #0d0d0d !important;
        color: #00ff41 !important;
        border: 2px solid #00ff41 !important;
        border-radius: 8px;
        font-weight: 500;
        font-family: 'Courier New', monospace;
        transition: all 0.3s ease;
    }

    /* ===== BUTTONS - HOVER STATE (dark green bg, white text) ===== */
    .stButton > button:hover {
        background-color: #004d1a !important;
        color: #ffffff !important;
        border: 2px solid #00ff41 !important;
        box-shadow: 0 0 15px rgba(0,255,65,0.4);
    }

    /* ===== CAPTIONS ===== */
    .stCaption, [data-testid="stCaptionContainer"] {
        color: #00cc33 !important;
    }

    /* ===== PAGE DIVIDER ===== */
    .page-divider {
        border-top: 2px solid #00ff41;
        margin: 30px 0;
        opacity: 0.6;
    }

    /* Horizontal rules */
    hr {
        border-color: #00ff41 !important;
    }

    /* ===== INPUTS ===== */
    input, textarea, select {
        background-color: #0d0d0d !important;
        color: #00ff41 !important;
        border: 1px solid #00ff41 !important;
    }

    /* ===== RADIO BUTTONS ===== */
    [data-testid="stRadio"] label {
        color: #00ff41 !important;
    }

    [data-testid="stRadio"] label span {
        color: #00ff41 !important;
    }

    /* ===== WARNINGS/INFO/SUCCESS/ERROR ===== */
    .stAlert {
        background-color: #0d0d0d !important;
        color: #00ff41 !important;
        border: 1px solid #00ff41 !important;
    }

    /* ===== PROGRESS BAR ===== */
    .stProgress > div > div {
        background-color: #00ff41 !important;
    }

    /* ===== SELECTBOX ===== */
    [data-testid="stSelectbox"] {
        color: #00ff41 !important;
    }

    [data-testid="stSelectbox"] > div {
        background-color: #0d0d0d !important;
        border: 1px solid #00ff41 !important;
    }

    /* ===== PORTAL CARDS WITH GLOW EFFECT ===== */
    .portal-card {
        background: linear-gradient(135deg, rgba(0,255,65,0.1) 0%, rgba(0,204,51,0.05) 100%);
        border: 2px solid #00ff41;
        border-radius: 10px;
        box-shadow: 0 0 20px rgba(0,255,65,0.3);
    }

    /* ===== TABS ===== */
    .stTabs [data-baseweb="tab-list"] {
        background-color: #0d0d0d;
        border-bottom: 2px solid #00ff41;
    }

    .stTabs [data-baseweb="tab"] {
        color: #00ff41 !important;
        background-color: #0d0d0d;
    }

    .stTabs [aria-selected="true"] {
        background-color: #004d1a !important;
        color: #00ff41 !important;
    }

    /* ===== PLOTLY CHARTS - TRANSPARENT BACKGROUND ===== */
    .js-plotly-plot .plotly .main-svg {
        background: transparent !important;
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
    "OMEGA NOVA": omega,
    "AVLAR": avlar,
    "Roadmap": roadmap,
    "Glossary": glossary,
    "Publications": publications,
}

# Matrix is special - accessed via dedicated button, not radio
MATRIX_MODULE = matrix

# ========== MAIN ==========

def main():
    st.set_page_config(
        page_title="Nyquist Dashboard",
        page_icon="📜",
        layout="wide",
    )

    apply_custom_css()

    status = load_status()

    # Initialize Matrix state
    if 'show_matrix' not in st.session_state:
        st.session_state.show_matrix = False

    # Track the previous page to detect radio changes
    if 'prev_page' not in st.session_state:
        st.session_state.prev_page = "Overview"

    with st.sidebar:
        st.markdown("### 📜 Nyquist Ledger")

        page = st.radio(
            "Turn the page:",
            list(PAGE_MODULES.keys()),
        )

        # If user clicked a different radio option, exit Matrix view
        if page != st.session_state.prev_page:
            st.session_state.show_matrix = False
            st.session_state.prev_page = page

        st.markdown("---")

        # Branch info - compact with inline code
        st.markdown(f"**Branch:** `{status.get('current_branch', 'unknown')}`")
        st.markdown(f"**Freeze:** `{status.get('freeze', {}).get('branch', 'unknown')}`")

        st.markdown("")  # Small spacer

        # Matrix portal button
        if st.button("🟢 Enter The Matrix", key="matrix_btn", type="secondary", use_container_width=True):
            st.session_state.show_matrix = True
            st.rerun()

    # Route to Matrix or selected page
    if st.session_state.show_matrix:
        MATRIX_MODULE.render()
    else:
        page_module = PAGE_MODULES.get(page)
        if page_module and hasattr(page_module, 'render'):
            page_module.render()
        else:
            st.error(f"Page module '{page}' not found or missing render() function")


if __name__ == "__main__":
    main()
