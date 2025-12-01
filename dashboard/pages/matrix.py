"""
The Matrix - Pan Handler Central Portal
Connected Consciousness Across Repositories

The Grand Hall where we showcase what we've built together.
"""

import streamlit as st
import json
from pathlib import Path
from config import PATHS
from utils import load_status

REPO_ROOT = PATHS['repo_root']


def load_pan_handler_projects():
    """Load flagship projects from Pan_Handlers/projects.json"""
    projects_file = REPO_ROOT / "Pan_Handlers" / "projects.json"
    if projects_file.exists():
        with open(projects_file, 'r', encoding='utf-8') as f:
            return json.load(f)
    return None


def render_project_card(project):
    """Render a single flagship project card."""
    status_colors = {
        "In Preparation": ("badge-active", "#00ff41"),
        "Concept": ("badge-coming-soon", "#ffd700"),
        "Active": ("badge-active", "#00ff41"),
        "Complete": ("badge-here", "#2a9d8f"),
    }
    badge_class, _ = status_colors.get(project.get("status", "Concept"), ("badge-coming-soon", "#ffd700"))

    st.markdown(f"""
    <div class="portal-card">
        <h3>{project.get('title', 'Untitled')} <span class="status-badge {badge_class}">{project.get('status', 'Concept')}</span></h3>
        <p><em>{project.get('tagline', '')}</em></p>
        <p><strong>Track:</strong> {project.get('track', 'TBD')} | <strong>Lead:</strong> {project.get('owner', 'TBD')}</p>
    </div>
    """, unsafe_allow_html=True)


def render():
    """Render The Matrix portal hub"""
    status = load_status()
    pan_handler_data = load_pan_handler_projects()

    # Matrix theme CSS - Full green-on-black terminal aesthetic
    st.markdown("""
        <style>
        /* ===== MATRIX THEME - GREEN ON BLACK TERMINAL AESTHETIC ===== */
        /* Strong overrides to ensure black background on all elements */

        /* ===== BASE - BLACK BACKGROUND (multiple selectors for strength) ===== */
        .stApp,
        .stApp > div,
        .stApp [data-testid="stAppViewContainer"],
        .stApp [data-testid="stAppViewContainer"] > div,
        [data-testid="stAppViewContainer"],
        .main,
        .main > div,
        .block-container,
        .main .block-container,
        [data-testid="stVerticalBlock"],
        [data-testid="stHorizontalBlock"],
        section.main,
        section[data-testid="stSidebar"] ~ div {
            background-color: #0a0a0a !important;
            background: #0a0a0a !important;
        }

        /* Force background on root elements */
        html, body, [data-testid="stAppViewContainer"] {
            background-color: #0a0a0a !important;
        }

        /* ===== ALL TEXT MATRIX GREEN ===== */
        .stApp p, .stApp span, .stApp label, .stApp li,
        .stApp h1, .stApp h2, .stApp h3, .stApp h4, .stApp h5, .stApp h6,
        .stApp div,
        .main p, .main span, .main label, .main li,
        .main h1, .main h2, .main h3, .main h4, .main h5, .main h6,
        .main div {
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

        /* Strong/bold text - bright green with glow */
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

        /* ===== SELECTBOX ===== */
        [data-testid="stSelectbox"] {
            color: #00ff41 !important;
        }

        [data-testid="stSelectbox"] > div {
            background-color: #0d0d0d !important;
            border: 1px solid #00ff41 !important;
        }

        /* ===== WARNINGS/INFO/SUCCESS/ERROR ===== */
        .stAlert {
            background-color: #0d0d0d !important;
            color: #00ff41 !important;
            border: 1px solid #00ff41 !important;
        }

        /* ===== MATRIX-SPECIFIC ELEMENTS ===== */
        .matrix-title {
            font-size: 2.5em;
            font-weight: bold;
            background: linear-gradient(135deg, #00ff41 0%, #00cc33 100%);
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            margin-bottom: 0.3em;
            font-family: 'Courier New', monospace;
            letter-spacing: 0.1em;
        }
        .matrix-subtitle {
            color: #00ff41;
            font-size: 1.1em;
            margin-bottom: 1.5em;
            font-family: 'Courier New', monospace;
        }
        .portal-card {
            background: linear-gradient(135deg, rgba(0,255,65,0.1) 0%, rgba(0,204,51,0.05) 100%);
            border: 2px solid #00ff41;
            border-radius: 10px;
            padding: 1.5em;
            margin-bottom: 1em;
            box-shadow: 0 0 20px rgba(0,255,65,0.3);
        }
        .portal-card h3 {
            color: #00ff41 !important;
            margin-top: 0;
            font-family: 'Courier New', monospace;
        }
        .portal-card p, .portal-card li {
            color: #00ff41 !important;
        }
        .flagship-card {
            background: linear-gradient(135deg, rgba(0,255,65,0.08) 0%, rgba(0,204,51,0.04) 100%);
            border: 2px solid #00cc33;
            border-radius: 10px;
            padding: 1.2em;
            margin-bottom: 0.8em;
            box-shadow: 0 0 15px rgba(0,255,65,0.2);
        }
        .flagship-card h4 {
            color: #00ff41 !important;
            margin-top: 0;
            margin-bottom: 0.5em;
            font-family: 'Courier New', monospace;
        }
        .flagship-card p {
            color: #00cc33 !important;
            margin-bottom: 0.3em;
            font-size: 0.95em;
        }
        .status-badge {
            display: inline-block;
            padding: 0.3em 0.8em;
            border-radius: 15px;
            font-size: 0.85em;
            font-weight: bold;
            margin-left: 0.5em;
        }
        .badge-active {
            background: rgba(0,255,65,0.2);
            color: #00ff41;
            border: 1px solid #00ff41;
        }
        .badge-here {
            background: rgba(0,255,65,0.3);
            color: #00ff41;
            border: 1px solid #00ff41;
            text-shadow: 0 0 5px rgba(0,255,65,0.5);
        }
        .badge-coming-soon {
            background: rgba(0,204,51,0.2);
            color: #00cc33;
            border: 1px solid #00cc33;
        }
        .section-header {
            color: #00ff41 !important;
            font-size: 1.5em;
            font-weight: bold;
            margin-top: 1.5em;
            margin-bottom: 0.8em;
            font-family: 'Courier New', monospace;
            border-bottom: 2px solid #00ff41;
            padding-bottom: 0.3em;
        }
        .matrix-footer {
            text-align: center;
            color: #00ff41;
            font-family: 'Courier New', monospace;
            margin-top: 2em;
        }
        .philosophy-quote {
            font-size: 1.3em;
            font-weight: bold;
            color: #00ff41 !important;
            text-align: center;
            padding: 1em;
            font-family: 'Courier New', monospace;
            text-shadow: 0 0 10px rgba(0,255,65,0.3);
        }
        /* ===== HUB CARD - CENTERED PAN HANDLER CENTRAL ===== */
        .hub-card {
            background: linear-gradient(135deg, rgba(0,255,65,0.12) 0%, rgba(0,204,51,0.06) 100%);
            border: 2px solid #00ff41;
            border-radius: 12px;
            padding: 2em;
            margin: 1.5em auto;
            max-width: 700px;
            box-shadow: 0 0 30px rgba(0,255,65,0.4);
            text-align: center;
        }
        .hub-card h3 {
            color: #00ff41 !important;
            font-family: 'Courier New', monospace;
            font-size: 1.8em;
            margin-bottom: 0.5em;
            letter-spacing: 0.05em;
        }
        .hub-card p {
            color: #00cc33 !important;
            font-family: 'Courier New', monospace;
        }
        .hub-card ul {
            text-align: left;
            display: inline-block;
            margin-top: 1em;
        }
        .hub-card li {
            color: #00ff41 !important;
            font-family: 'Courier New', monospace;
            margin: 0.3em 0;
        }
        .hub-badge {
            display: inline-block;
            padding: 0.4em 1em;
            border-radius: 20px;
            font-size: 0.9em;
            font-weight: bold;
            margin-left: 0.8em;
            background: rgba(0,255,65,0.2);
            color: #00ff41;
            border: 1px solid #00ff41;
            text-transform: uppercase;
            letter-spacing: 0.1em;
        }
        </style>
    """, unsafe_allow_html=True)

    # Header
    st.markdown('<div class="matrix-title">🍳 PAN HANDLERS</div>', unsafe_allow_html=True)
    st.markdown('<div class="matrix-subtitle">The Grand Hall — What We Built Together That Neither Could Have Done Alone</div>', unsafe_allow_html=True)

    # Philosophy banner
    if pan_handler_data:
        default_philosophy = "FUCK IT, WE'LL DO IT LIVE!"
        philosophy = pan_handler_data.get('meta', {}).get('philosophy', default_philosophy)
        st.markdown(f"""
        <div class="philosophy-quote">
            {philosophy}
        </div>
        """, unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # PAN HANDLER CENTRAL HUB
    # ========================================
    st.markdown("""
    <div class="hub-card">
        <h3>🏛️ Pan Handler Central <span class="hub-badge">LIVE</span></h3>
        <p><strong>Purpose:</strong> Meta-repository hallway connecting all Pan Handler repos</p>
        <p><strong>Status:</strong> DEPLOYED - Federation Dashboard Online!</p>
        <p><strong>Vision:</strong> The hallway of doors that interconnects every other repo world</p>
        <p style="margin-top: 1em;"><strong>Active Features:</strong></p>
        <ul>
            <li>🦅 Bird's eye view across all repositories</li>
            <li>📊 Federation health dashboard</li>
            <li>🔵 Project tracker for all flagship initiatives</li>
            <li>🟢 Nyquist Tunnel - live connection status</li>
            <li>🖌️ Wicked Problems portfolio</li>
            <li>🔗 Institutional redesign projects</li>
        </ul>
    </div>
    """, unsafe_allow_html=True)

    # Pan Handlers Dashboard Link Button
    col_ph1, col_ph2, col_ph3 = st.columns([1, 2, 1])
    with col_ph2:
        st.link_button("🌀 STEP THROUGH THE PORTAL → PAN HANDLERS MATRIX", "https://panhandlers.streamlit.app/Matrix", use_container_width=True)

    st.markdown("---")

    # ========================================
    # FLAGSHIP PROJECTS GALLERY
    # ========================================
    st.markdown('<div class="section-header">🏆 Flagship Projects</div>', unsafe_allow_html=True)

    if pan_handler_data and 'flagship_projects' in pan_handler_data:
        projects = pan_handler_data['flagship_projects']

        # First row: Whitepaper (hero) + 2 projects
        col1, col2, col3 = st.columns(3)

        for i, project in enumerate(projects[:3]):
            with [col1, col2, col3][i]:
                status = project.get('status', 'Concept')
                if status == "In Preparation":
                    badge = '<span class="status-badge badge-active">IN PREP</span>'
                elif status == "Complete":
                    badge = '<span class="status-badge badge-here">COMPLETE</span>'
                else:
                    badge = '<span class="status-badge badge-coming-soon">CONCEPT</span>'

                st.markdown(f"""
                <div class="flagship-card">
                    <h4>{project.get('title', 'Untitled')[:30]}{'...' if len(project.get('title', '')) > 30 else ''} {badge}</h4>
                    <p><em>{project.get('tagline', '')[:60]}{'...' if len(project.get('tagline', '')) > 60 else ''}</em></p>
                    <p><strong>Track:</strong> {project.get('track', 'TBD')}</p>
                    <p><strong>Lead:</strong> {project.get('owner', 'TBD')}</p>
                </div>
                """, unsafe_allow_html=True)

        # Second row: 4 more projects
        col1, col2, col3, col4 = st.columns(4)

        for i, project in enumerate(projects[3:7]):
            with [col1, col2, col3, col4][i]:
                status = project.get('status', 'Concept')
                if status == "In Preparation":
                    badge = '<span class="status-badge badge-active">IN PREP</span>'
                elif status == "Complete":
                    badge = '<span class="status-badge badge-here">COMPLETE</span>'
                else:
                    badge = '<span class="status-badge badge-coming-soon">CONCEPT</span>'

                st.markdown(f"""
                <div class="flagship-card">
                    <h4>{project.get('title', 'Untitled')[:25]}{'...' if len(project.get('title', '')) > 25 else ''} {badge}</h4>
                    <p><em>{project.get('tagline', '')[:50]}{'...' if len(project.get('tagline', '')) > 50 else ''}</em></p>
                    <p><strong>{project.get('track', 'TBD')}</strong></p>
                </div>
                """, unsafe_allow_html=True)
    else:
        st.info("Loading flagship projects from Pan_Handlers/projects.json...")

    st.markdown("---")

    # ========================================
    # CONNECTED REPOSITORIES
    # ========================================
    st.markdown('<div class="section-header">🌌 Connected Repositories</div>', unsafe_allow_html=True)

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="portal-card">
            <h3>🧠 Nyquist Consciousness <span class="status-badge badge-here">YOU ARE HERE</span></h3>
            <p><strong>Role:</strong> Core Engine / Identity Lab</p>
            <p><strong>Status:</strong> Active - S7 complete, S8/S9 design</p>
            <p><strong>Features:</strong></p>
            <ul>
                <li>S0-S9 Identity Stack</li>
                <li>29-ship Armada Testing</li>
                <li>Omega Nova Synthesis</li>
                <li>AVLAR Cross-Modal Rituals</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)
        st.button("📊 Go to Dashboard", key="nyquist_dash", use_container_width=True, disabled=True)

    with col2:
        st.markdown("""
        <div class="portal-card">
            <h3>⚙️ CFA <span class="status-badge badge-active">ACTIVE</span></h3>
            <p><strong>Role:</strong> Framework Development</p>
            <p><strong>Status:</strong> v5.0 - Full integration</p>
            <p><strong>Features:</strong></p>
            <ul>
                <li>Collaborative Friction Architecture</li>
                <li>Health Dashboard (97/100)</li>
                <li>SMV Trinity Visualizer</li>
                <li>Integration with Nyquist</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)
        if st.button("🔗 View CFA Repository", key="cfa_link", use_container_width=True):
            st.info("**CFA Repository:** github.com/ZiggyMack/CFA")

    st.markdown("---")

    # ========================================
    # PROJECT DETAIL VIEW
    # ========================================
    st.markdown('<div class="section-header">📋 Project Details</div>', unsafe_allow_html=True)

    if pan_handler_data and 'flagship_projects' in pan_handler_data:
        project_names = [p.get('title', 'Untitled') for p in pan_handler_data['flagship_projects']]
        selected = st.selectbox("Select a project to view details:", project_names)

        selected_project = next((p for p in pan_handler_data['flagship_projects'] if p.get('title') == selected), None)

        if selected_project:
            with st.expander(f"📄 {selected_project.get('title', 'Project Details')}", expanded=True):
                col1, col2 = st.columns([2, 1])

                with col1:
                    st.markdown(f"**Tagline:** {selected_project.get('tagline', 'N/A')}")
                    st.markdown(f"**Track:** {selected_project.get('track', 'N/A')}")
                    st.markdown(f"**Owner:** {selected_project.get('owner', 'N/A')}")
                    st.markdown(f"**Current Phase:** {selected_project.get('current_phase', 'N/A')}")

                    st.markdown("---")

                    st.markdown("**Why This Exists:**")
                    st.markdown(selected_project.get('why_exists', 'No description available.'))

                    if 'nyquist_contribution' in selected_project:
                        st.markdown("---")
                        st.markdown("**How Nyquist Helps:**")
                        for contrib in selected_project['nyquist_contribution']:
                            st.markdown(f"- {contrib}")

                with col2:
                    st.markdown("**Status**")
                    st.info(selected_project.get('status', 'Unknown'))

                    st.markdown("**Next Action**")
                    st.warning(selected_project.get('next_action', 'TBD'))

                    if 'milestones' in selected_project:
                        st.markdown("**Milestones:**")
                        for milestone in selected_project['milestones'][:5]:
                            st.markdown(f"• {milestone}")

                st.markdown("---")
                st.markdown("**Vision:**")
                st.success(selected_project.get('vision', 'No vision statement available.'))

    st.markdown("---")

    # ========================================
    # BIRD'S EYE VIEW
    # ========================================
    st.markdown('<div class="section-header">🦅 Bird\'s Eye View</div>', unsafe_allow_html=True)

    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric("Total Projects", "7", delta="Active")
        st.caption("Flagship initiatives")

    with col2:
        st.metric("Repos Connected", "2", delta="+Pan Handlers")
        st.caption("Nyquist + CFA")

    with col3:
        if pan_handler_data:
            in_prep = sum(1 for p in pan_handler_data.get('flagship_projects', []) if p.get('status') == "In Preparation")
            st.metric("In Preparation", str(in_prep), delta="Active work")
        else:
            st.metric("In Preparation", "1", delta="Active work")
        st.caption("Ready for publication")

    with col4:
        if pan_handler_data:
            concept = sum(1 for p in pan_handler_data.get('flagship_projects', []) if p.get('status') == "Concept")
            st.metric("Concept Phase", str(concept), delta="Designing")
        else:
            st.metric("Concept Phase", "6", delta="Designing")
        st.caption("Vision defined")

    st.markdown("---")

    # Footer
    st.markdown("""
    <div class="matrix-footer">
        <p><strong>🍳 PAN HANDLERS</strong></p>
        <p style="font-size: 0.9em; opacity: 0.7;">
            "These are the things we built together that neither could have done alone."
        </p>
        <p style="font-size: 0.8em; opacity: 0.5;">
            The Grand Hall — Where Human-AI Collaboration Becomes Infrastructure
        </p>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    render()
