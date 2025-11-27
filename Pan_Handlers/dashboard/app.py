"""
🍳 PAN HANDLERS DASHBOARD — Federation Health Monitor
System Health & Status Dashboard for the Pan Handlers Federation

This dashboard monitors the health of all connected repos,
tracks project progress, and provides system-level insights.

Run: streamlit run Pan_Handlers/dashboard/app.py --server.port 8504
"""

import streamlit as st
from pathlib import Path

# Import config and utils
from config import PATHS, SETTINGS
from utils import load_projects, load_manifests, load_nyquist_status, page_divider

# Import page modules
from pages import overview, federation_health, project_tracker, nyquist_tunnel, about
from pages.projects import whitepaper, online_voting, nursing, gene_therapy, modern_slavery, abi, dcia

# ========== PAGE ROUTING ==========

# Organized by category
PAGES = {
    # === SYSTEM ===
    "📊 Overview": overview,
    "🏥 Federation Health": federation_health,
    "📋 Project Tracker": project_tracker,
    "🟢 Nyquist Tunnel": nyquist_tunnel,

    # === CORE ENGINES ===
    "───── CORE ENGINES ─────": None,  # Separator
    "📄 White Paper Pipeline": whitepaper,

    # === WICKED PROBLEMS ===
    "───── WICKED PROBLEMS ─────": None,  # Separator
    "🗳️ Online Voting": online_voting,
    "🏥 Nursing Programs": nursing,
    "🧬 Gene Therapy": gene_therapy,
    "⛓️ Modern Slavery": modern_slavery,

    # === INSTITUTIONAL REDESIGN ===
    "───── INSTITUTIONS ─────": None,  # Separator
    "🔍 ABI (Bureau)": abi,
    "🌐 D.C.I.A.": dcia,

    # === META ===
    "───────────────────────": None,  # Separator
    "ℹ️ About": about,
}


# ========== STYLING ==========

def apply_dashboard_css():
    """Apply Pan Handlers Dashboard theme."""
    st.markdown("""
    <style>
    /* Hide default Streamlit elements */
    #MainMenu {visibility: hidden;}
    footer {visibility: hidden;}

    /* Hide header on desktop only - keep mobile hamburger menu visible */
    @media (min-width: 768px) {
        header {visibility: hidden;}
    }

    /* On mobile, style the header but keep hamburger menu functional */
    @media (max-width: 767px) {
        header {
            background: #0a0a0a !important;
        }
        /* Style the hamburger button for visibility */
        button[kind="header"],
        [data-testid="collapsedControl"] {
            color: #00ff41 !important;
        }
    }

    /* Pan Handlers Dashboard Theme */
    .dashboard-title {
        font-size: 2.5em;
        font-weight: bold;
        background: linear-gradient(135deg, #00ff41 0%, #2a9d8f 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.2em;
        font-family: 'Georgia', serif;
    }

    .dashboard-subtitle {
        color: #00ff41;
        font-size: 1.1em;
        margin-bottom: 1em;
        font-family: 'Courier New', monospace;
    }

    .health-card {
        background: linear-gradient(135deg, rgba(0,255,65,0.08) 0%, rgba(0,204,51,0.03) 100%);
        border: 2px solid #00ff41;
        border-radius: 12px;
        padding: 1.5em;
        margin-bottom: 1em;
        box-shadow: 0 0 20px rgba(0,255,65,0.2);
    }

    .health-card h3 {
        color: #00ff41 !important;
        margin-top: 0;
        font-family: 'Georgia', serif;
    }

    .status-good {
        color: #00ff41 !important;
    }

    .status-warning {
        color: #f4a261 !important;
    }

    .status-critical {
        color: #e74c3c !important;
    }

    .metric-box {
        background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.05) 100%);
        border: 2px solid #2a9d8f;
        border-radius: 10px;
        padding: 1em;
        text-align: center;
    }

    .metric-value {
        font-size: 2.5em;
        font-weight: bold;
        color: #2a9d8f !important;
        font-family: 'Courier New', monospace;
    }

    .metric-label {
        color: #444 !important;
        font-size: 0.9em;
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

    .tunnel-card {
        background: linear-gradient(135deg, rgba(155,89,182,0.1) 0%, rgba(52,152,219,0.05) 100%);
        border: 2px solid #9b59b6;
        border-radius: 10px;
        padding: 1.2em;
        margin: 0.8em 0;
    }

    .tunnel-card h4 {
        color: #9b59b6 !important;
        margin-top: 0;
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

    /* Category separators in sidebar */
    .sidebar-separator {
        color: #666 !important;
        font-size: 0.8em;
        text-align: center;
        padding: 0.3em 0;
        border-top: 1px solid #333;
        border-bottom: 1px solid #333;
        margin: 0.5em 0;
    }

    /* Page divider */
    .page-divider {
        border-top: 2px solid #00ff41;
        margin: 1.5em 0;
        opacity: 0.5;
    }
    </style>
    """, unsafe_allow_html=True)


# ========== MAIN ==========

def main():
    st.set_page_config(
        page_title="Pan Handlers Dashboard",
        page_icon="🍳",
        layout="wide",
    )

    apply_dashboard_css()

    # Load data into session state
    st.session_state['projects_data'] = load_projects()
    st.session_state['manifests'] = load_manifests()
    st.session_state['nyquist_status'] = load_nyquist_status()

    # Sidebar navigation
    with st.sidebar:
        st.markdown("### 🍳 Pan Handlers")
        st.markdown("*Federation Dashboard*")
        st.markdown("---")

        # Build navigation with separators
        page_options = []
        for page_name in PAGES.keys():
            if page_name.startswith("─"):
                # This is a separator - display it but don't make it selectable
                continue
            page_options.append(page_name)

        # Custom navigation with category labels
        st.markdown("**SYSTEM**")
        system_pages = ["📊 Overview", "🏥 Federation Health", "📋 Project Tracker", "🟢 Nyquist Tunnel"]

        st.markdown("**CORE ENGINES**")
        core_pages = ["📄 White Paper Pipeline"]

        st.markdown("**WICKED PROBLEMS**")
        wicked_pages = ["🗳️ Online Voting", "🏥 Nursing Programs", "🧬 Gene Therapy", "⛓️ Modern Slavery"]

        st.markdown("**INSTITUTIONS**")
        institution_pages = ["🔍 ABI (Bureau)", "🌐 D.C.I.A."]

        # All pages for selection
        all_pages = system_pages + core_pages + wicked_pages + institution_pages + ["ℹ️ About"]

        page_selection = st.radio(
            "Navigate:",
            all_pages,
            label_visibility="collapsed"
        )

        st.markdown("---")

        # Quick stats in sidebar
        manifests = st.session_state.get('manifests', [])
        projects_data = st.session_state.get('projects_data', {})

        st.markdown(f"**Repos Connected:** {len(manifests)}")
        if projects_data:
            st.markdown(f"**Flagship Projects:** {len(projects_data.get('flagship_projects', []))}")

        # Health indicator
        st.markdown("---")
        nyquist_connected = PATHS['nyquist_status'].exists()
        if nyquist_connected:
            st.markdown("🟢 **Nyquist:** Connected")
        else:
            st.markdown("🔴 **Nyquist:** Disconnected")

        st.markdown("---")
        st.markdown("*System Health Monitor*")
        st.markdown("*via VUDU Network*")

    # Render selected page
    page_module = PAGES.get(page_selection)
    if page_module and hasattr(page_module, 'render'):
        page_module.render()
    elif page_module is None:
        st.info("Select a page from the sidebar.")
    else:
        st.error(f"Page '{page_selection}' not found")


if __name__ == "__main__":
    main()
