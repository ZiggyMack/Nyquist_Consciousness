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
from pages import overview, personas, stackup, AI_ARMADA, tests, metrics, omega, avlar, roadmap, glossary, publications, matrix, faq, unknown

# ========== THEME & STYLING ==========

LEDGER_COLORS = SETTINGS['colors']

def apply_custom_css():
    """Apply custom CSS for light theme with dark sidebar."""
    st.markdown("""
    <style>
    /* Hide default Streamlit menu and footer */
    #MainMenu {visibility: hidden;}
    footer {visibility: hidden;}

    /* Hide header content on desktop but keep sidebar collapse control visible */
    @media (min-width: 768px) {
        /* Don't hide entire header - it contains sidebar collapse control */
        /* header {visibility: hidden;} */
        header [data-testid="stHeader"] {
            background: transparent !important;
        }
        /* Hide header decorations but keep functional elements */
        header [data-testid="stToolbar"] {
            visibility: hidden;
        }
    }

    /* On mobile, style the header but keep hamburger menu functional */
    @media (max-width: 767px) {
        header {
            background: #0a0a0a !important;
        }
        header [data-testid="stHeader"] {
            background: #0a0a0a !important;
        }
        /* Style the hamburger button for visibility */
        button[kind="header"] {
            color: #00ff41 !important;
        }
        [data-testid="collapsedControl"] {
            color: #00ff41 !important;
        }
    }

    /* Hide Streamlit's default page navigation in sidebar */
    [data-testid="stSidebarNav"] {display: none !important;}
    section[data-testid="stSidebarNav"] {display: none !important;}
    /* Don't hide all nav - keep sidebar collapse control visible */
    /* nav[role="navigation"] {display: none !important;} */

    /* Keep sidebar collapse/expand button visible and styled */
    [data-testid="collapsedControl"] {
        display: flex !important;
        visibility: visible !important;
        position: fixed !important;
        left: 0 !important;
        top: 50% !important;
        z-index: 999999 !important;
        background: #1a1a1a !important;
        border-radius: 0 8px 8px 0 !important;
        padding: 8px 4px !important;
    }

    button[data-testid="baseButton-headerNoPadding"] {
        display: block !important;
        visibility: visible !important;
    }

    /* Style the collapse/expand arrow */
    [data-testid="collapsedControl"] svg {
        color: #00ff41 !important;
        width: 24px !important;
        height: 24px !important;
    }

    /* When sidebar is expanded, position control inside sidebar */
    [data-testid="stSidebar"][aria-expanded="true"] [data-testid="collapsedControl"] {
        position: relative !important;
        left: auto !important;
        top: auto !important;
        background: transparent !important;
    }

    /* ===== LIGHT THEME FOR MAIN CONTENT ===== */
    .stApp {
        background: #ffffff !important;
    }

    .main .block-container {
        background: #ffffff !important;
    }

    /* ===== ALL TEXT BLACK BY DEFAULT (MAIN CONTENT ONLY) ===== */
    .main .block-container, .main .block-container * {
        color: #1a1a1a !important;
    }

    /* ===== SIDEBAR - KEEP DARK AND VISIBLE ===== */
    section[data-testid="stSidebar"] {
        background: linear-gradient(180deg, #0a0a0a, #1a1a1a) !important;
        display: block !important;
        visibility: visible !important;
    }

    section[data-testid="stSidebar"] > div {
        display: block !important;
        visibility: visible !important;
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
        margin: 0.5rem 0 !important;
    }

    section[data-testid="stSidebar"] code {
        background: rgba(255,255,255,0.1) !important;
        color: #00ff41 !important;
    }

    /* Matrix button special styling */
    section[data-testid="stSidebar"] button[kind="secondary"] {
        background: transparent !important;
        border: 1px solid #00ff41 !important;
        color: #00ff41 !important;
    }
    section[data-testid="stSidebar"] button[kind="secondary"]:hover {
        background: rgba(0,255,65,0.2) !important;
        border: 1px solid #00ff41 !important;
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
        white-space: pre !important;
    }

    /* ===== ASCII ART CONTAINERS (Personas page) ===== */
    /* Light theme for ASCII art - clean and readable */
    .ascii-container {
        background: linear-gradient(135deg, #f8f9fa 0%, #e9ecef 100%) !important;
        overflow-x: auto !important;
    }
    .ascii-container pre {
        background: transparent !important;
        color: #264653 !important;
        white-space: pre !important;
        font-family: 'Courier New', Consolas, monospace !important;
        font-size: 0.7em !important;
        line-height: 1.15 !important;
        overflow-x: auto !important;
    }
    .ascii-container * {
        color: #264653 !important;
    }
    .ascii-title {
        color: #2a9d8f !important;
    }

    /* ===== ENSURE FOOTER VISIBLE ===== */
    .main .block-container {
        padding-bottom: 5rem !important;
    }

    /* ===== TABLES & DATAFRAMES ===== */
    table, [data-testid="stTable"], .stDataFrame {
        color: #333333 !important;
        background: #ffffff !important;
    }

    th {
        background: #2a9d8f !important;
        color: #ffffff !important;
        font-weight: bold;
    }

    td {
        color: #333333 !important;
        background: #ffffff !important;
        border-bottom: 1px solid #dee2e6;
    }

    /* Dataframe specific - force light theme */
    [data-testid="stDataFrame"] {
        background: #ffffff !important;
    }

    [data-testid="stDataFrame"] div {
        color: #333333 !important;
        background: transparent !important;
    }

    [data-testid="stDataFrame"] [data-testid="StyledDataFrameDataCells"],
    [data-testid="stDataFrame"] [data-testid="StyledDataFrameHeaderCell"] {
        background: #ffffff !important;
        color: #333333 !important;
    }

    /* Pandas styler dataframes */
    .stDataFrame iframe {
        background: #ffffff !important;
    }

    /* Glide Data Grid (Streamlit's dataframe component) - force light theme */
    [data-testid="stDataFrame"] > div {
        background: #ffffff !important;
    }

    /* Target the canvas and surrounding elements */
    .dvn-scroller {
        background: #ffffff !important;
    }

    /* Glide data grid cells */
    .gdg-cell {
        background: #ffffff !important;
        color: #333333 !important;
    }

    /* Override any dark theme variables that might be set */
    :root {
        --gdg-bg-cell: #ffffff !important;
        --gdg-bg-header: #2a9d8f !important;
        --gdg-text-dark: #333333 !important;
        --gdg-text-header: #ffffff !important;
        --gdg-bg-cell-medium: #f8f9fa !important;
    }

    /* Multiselect pills/tags - keep teal theme */
    [data-baseweb="tag"] {
        background: #2a9d8f !important;
        color: #ffffff !important;
    }

    [data-baseweb="tag"] span {
        color: #ffffff !important;
    }

    /* Multiselect input container */
    .stMultiSelect [data-baseweb="select"] > div {
        background: #ffffff !important;
    }

    .stMultiSelect [data-baseweb="input"] {
        background: #ffffff !important;
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

    /* ===== SELECTBOX / DROPDOWN ===== */
    /* Main selectbox container */
    .stSelectbox [data-baseweb="select"] {
        background: #ffffff !important;
    }

    .stSelectbox [data-baseweb="select"] > div {
        background: #ffffff !important;
        border: 1px solid #ced4da !important;
    }

    /* Selectbox selected value text */
    .stSelectbox [data-baseweb="select"] span {
        color: #333333 !important;
    }

    /* Dropdown menu (the popup list) */
    [data-baseweb="popover"] {
        background: #ffffff !important;
    }

    [data-baseweb="menu"] {
        background: #ffffff !important;
    }

    /* Dropdown menu items */
    [data-baseweb="menu"] li {
        background: #ffffff !important;
        color: #333333 !important;
    }

    [data-baseweb="menu"] li:hover {
        background: #f0f0f0 !important;
    }

    /* Selected/highlighted item in dropdown */
    [data-baseweb="menu"] li[aria-selected="true"] {
        background: #e8f4f2 !important;
        color: #2a9d8f !important;
    }

    /* Dropdown option text */
    [data-baseweb="menu"] [role="option"] {
        color: #333333 !important;
    }

    [data-baseweb="menu"] [role="option"]:hover {
        background: #f0f0f0 !important;
    }

    /* ===== RADIO BUTTONS ===== */
    [data-testid="stRadio"] label {
        color: #333333 !important;
    }

    /* ===== WARNINGS/INFO/SUCCESS/ERROR ===== */
    .stAlert {
        color: #333333 !important;
    }

    /* ===== TABS ===== */
    /* Tab button text - make sure it's readable */
    .stTabs [data-baseweb="tab-list"] {
        gap: 8px;
    }

    .stTabs [data-baseweb="tab"] {
        background: #f8f9fa !important;
        border-radius: 4px 4px 0 0;
        border: 1px solid #dee2e6 !important;
        border-bottom: none !important;
        padding: 8px 16px !important;
    }

    .stTabs [data-baseweb="tab"] p {
        color: #333333 !important;
        font-weight: 500;
    }

    /* Active tab styling */
    .stTabs [aria-selected="true"] {
        background: #ffffff !important;
        border-color: #2a9d8f !important;
        border-bottom: 2px solid #ffffff !important;
    }

    .stTabs [aria-selected="true"] p {
        color: #2a9d8f !important;
        font-weight: 600;
    }

    /* Tab panel content area */
    .stTabs [data-baseweb="tab-panel"] {
        background: #ffffff !important;
        border: 1px solid #dee2e6 !important;
        border-top: none !important;
        padding: 16px !important;
        border-radius: 0 0 4px 4px;
    }
    </style>
    """, unsafe_allow_html=True)

# ========== PAGE ROUTING ==========

PAGE_MODULES = {
    "Overview": overview,
    "Personas": personas,
    "Stackup": stackup,
    "AI Armada": AI_ARMADA,
    "Tests": tests,
    "Metrics": metrics,
    "OMEGA NOVA": omega,
    "AVLAR": avlar,
    "Roadmap": roadmap,
    "Glossary": glossary,
    "Publications": publications,
    "FAQ": faq,
    "The Unknown": unknown,
}

# Matrix is special - accessed via dedicated button, not radio
MATRIX_MODULE = matrix

# ========== MAIN ==========

def main():
    st.set_page_config(
        page_title="Nyquist Dashboard",
        page_icon="🛰️",
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

        # Branch info - compact single block for tight spacing
        branch = status.get('current_branch', 'unknown')
        freeze = status.get('freeze', {}).get('branch', 'unknown')
        st.markdown(f"""
        <div style="line-height: 1.4; margin: 0;">
            <div style="margin: 0;"><strong>Branch:</strong> <code>{branch}</code></div>
            <div style="margin: 0;"><strong>Freeze:</strong> <code>{freeze}</code></div>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("---")

        # Matrix portal button
        if st.button("🟢 Enter The Matrix", key="matrix_btn", type="secondary"):
            st.session_state.show_matrix = True
            # Use st.rerun() if available (newer Streamlit), else st.experimental_rerun()
            if hasattr(st, 'rerun'):
                st.rerun()
            else:
                st.experimental_rerun()

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
