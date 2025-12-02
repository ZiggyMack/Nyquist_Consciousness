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
    # Uses triple-specificity selectors to override app.py light theme
    st.markdown("""
        <style>
        /* ===== MATRIX THEME OVERRIDE ===== */
        /* Triple specificity to beat app.py's ".main .block-container *" rule */

        /* ===== BASE - BLACK BACKGROUND ===== */
        .stApp .main .block-container,
        .stApp .main .block-container > div,
        .stApp [data-testid="stAppViewContainer"],
        .stApp [data-testid="stVerticalBlock"],
        .stApp [data-testid="stHorizontalBlock"],
        .main .block-container,
        .main .block-container > div {
            background-color: #0a0a0a !important;
            background: #0a0a0a !important;
        }

        /* Force background on root elements */
        html, body, [data-testid="stAppViewContainer"] {
            background-color: #0a0a0a !important;
        }

        /* ===== ALL TEXT MATRIX GREEN - TRIPLE SPECIFICITY ===== */
        /* This beats ".main .block-container *" by using more specific selectors */
        .stApp .main .block-container p,
        .stApp .main .block-container span,
        .stApp .main .block-container label,
        .stApp .main .block-container li,
        .stApp .main .block-container h1,
        .stApp .main .block-container h2,
        .stApp .main .block-container h3,
        .stApp .main .block-container h4,
        .stApp .main .block-container h5,
        .stApp .main .block-container h6,
        .stApp .main .block-container div,
        .stApp .main .block-container strong,
        .stApp .main .block-container b,
        .stApp .main .block-container em,
        .stApp .main .block-container i,
        .stApp .main .block-container a {
            color: #00ff41 !important;
        }

        /* Even more specific for nested elements */
        .stApp .main .block-container * {
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

        /* Selectbox dropdown - dark theme override */
        [data-testid="stSelectbox"] [data-baseweb="select"],
        [data-testid="stSelectbox"] [data-baseweb="select"] > div,
        [data-testid="stSelectbox"] [data-baseweb="select"] input {
            background-color: #0d0d0d !important;
            color: #00ff41 !important;
        }

        /* The actual dropdown value display */
        [data-baseweb="select"] > div:first-child {
            background-color: #0d0d0d !important;
            border-color: #00ff41 !important;
        }

        [data-baseweb="select"] span,
        [data-baseweb="select"] div[class*="valueContainer"] span {
            color: #00ff41 !important;
        }

        /* Dropdown menu when open - GLOBAL selectors for portal-rendered menus */
        /* Using #1a1a1a (lighter gray) for dropdown background for contrast */
        [data-baseweb="popover"],
        [data-baseweb="menu"],
        [data-baseweb="popover"] *,
        [data-baseweb="menu"] *,
        div[data-baseweb="popover"],
        div[data-baseweb="menu"],
        ul[role="listbox"],
        ul[role="listbox"] li,
        ul[role="listbox"] li * {
            background-color: #1a1a1a !important;
            color: #00ff41 !important;
        }

        /* Target the actual listbox container */
        [data-baseweb="popover"] > div,
        [data-baseweb="popover"] > div > div,
        [data-baseweb="popover"] ul,
        [data-baseweb="popover"] li {
            background-color: #1a1a1a !important;
            color: #00ff41 !important;
        }

        ul[role="listbox"] li:hover,
        [data-baseweb="popover"] li:hover {
            background-color: #003311 !important;
        }

        /* Selected option highlight */
        ul[role="listbox"] li[aria-selected="true"],
        [data-baseweb="popover"] li[aria-selected="true"] {
            background-color: #002a0d !important;
        }

        /* Force dropdown background globally */
        [data-floating-ui-portal] {
            background-color: transparent !important;
        }

        [data-floating-ui-portal] > div {
            background-color: #1a1a1a !important;
            border: 1px solid #00ff41 !important;
            border-radius: 8px !important;
        }

        [data-floating-ui-portal] ul,
        [data-floating-ui-portal] li {
            background-color: #1a1a1a !important;
            color: #00ff41 !important;
        }

        [data-floating-ui-portal] li:hover {
            background-color: #003311 !important;
        }

        /* ===== WARNINGS/INFO/SUCCESS/ERROR ===== */
        .stAlert {
            background-color: #0d0d0d !important;
            color: #00ff41 !important;
            border: 1px solid #00ff41 !important;
        }

        /* ===== MATRIX-SPECIFIC ELEMENTS ===== */
        .stApp .main .block-container .matrix-title,
        .main .block-container .matrix-title {
            font-size: 2.5em;
            font-weight: bold;
            color: #00ff41 !important;
            -webkit-text-fill-color: #00ff41 !important;
            text-shadow: 0 0 20px rgba(0,255,65,0.6), 0 0 40px rgba(0,255,65,0.3);
            margin-bottom: 0.3em;
            font-family: 'Courier New', monospace;
            letter-spacing: 0.1em;
        }
        .stApp .main .block-container .matrix-subtitle,
        .main .block-container .matrix-subtitle {
            color: #00ff41 !important;
            font-size: 1.1em;
            margin-bottom: 1.5em;
            font-family: 'Courier New', monospace;
        }
        /* Portal cards - triple specificity to beat app.py */
        .stApp .main .block-container .portal-card,
        .main .block-container .portal-card {
            background: linear-gradient(135deg, rgba(0,255,65,0.1) 0%, rgba(0,204,51,0.05) 100%) !important;
            border: 2px solid #00ff41;
            border-radius: 10px;
            padding: 1.5em;
            margin-bottom: 1em;
            box-shadow: 0 0 20px rgba(0,255,65,0.3);
        }
        .stApp .main .block-container .portal-card h3,
        .main .block-container .portal-card h3 {
            color: #00ff41 !important;
            margin-top: 0;
            font-family: 'Courier New', monospace;
        }
        .stApp .main .block-container .portal-card p,
        .stApp .main .block-container .portal-card li,
        .stApp .main .block-container .portal-card strong,
        .stApp .main .block-container .portal-card em,
        .stApp .main .block-container .portal-card span,
        .main .block-container .portal-card p,
        .main .block-container .portal-card li,
        .main .block-container .portal-card strong,
        .main .block-container .portal-card em,
        .main .block-container .portal-card span {
            color: #00ff41 !important;
        }
        /* Flagship cards - triple specificity */
        .stApp .main .block-container .flagship-card,
        .main .block-container .flagship-card {
            background: linear-gradient(135deg, rgba(0,255,65,0.08) 0%, rgba(0,204,51,0.04) 100%) !important;
            border: 2px solid #00cc33;
            border-radius: 10px;
            padding: 1.2em;
            margin-bottom: 0.8em;
            box-shadow: 0 0 15px rgba(0,255,65,0.2);
        }
        .stApp .main .block-container .flagship-card h4,
        .main .block-container .flagship-card h4 {
            color: #00ff41 !important;
            margin-top: 0;
            margin-bottom: 0.5em;
            font-family: 'Courier New', monospace;
        }
        .stApp .main .block-container .flagship-card p,
        .stApp .main .block-container .flagship-card strong,
        .stApp .main .block-container .flagship-card em,
        .stApp .main .block-container .flagship-card span,
        .main .block-container .flagship-card p,
        .main .block-container .flagship-card strong,
        .main .block-container .flagship-card em,
        .main .block-container .flagship-card span {
            color: #00cc33 !important;
            margin-bottom: 0.3em;
            font-size: 0.95em;
        }
        /* Status badges - with specificity */
        .stApp .main .block-container .status-badge,
        .main .block-container .status-badge {
            display: inline-block;
            padding: 0.3em 0.8em;
            border-radius: 15px;
            font-size: 0.85em;
            font-weight: bold;
            margin-left: 0.5em;
        }
        .stApp .main .block-container .badge-active,
        .main .block-container .badge-active {
            background: rgba(0,255,65,0.2) !important;
            color: #00ff41 !important;
            border: 1px solid #00ff41;
        }
        .stApp .main .block-container .badge-here,
        .main .block-container .badge-here {
            background: rgba(0,255,65,0.3) !important;
            color: #00ff41 !important;
            border: 1px solid #00ff41;
            text-shadow: 0 0 5px rgba(0,255,65,0.5);
        }
        .stApp .main .block-container .badge-coming-soon,
        .main .block-container .badge-coming-soon {
            background: rgba(0,204,51,0.2) !important;
            color: #00cc33 !important;
            border: 1px solid #00cc33;
        }
        .stApp .main .block-container .section-header,
        .main .block-container .section-header {
            color: #00ff41 !important;
            font-size: 1.5em;
            font-weight: bold;
            margin-top: 1.5em;
            margin-bottom: 0.8em;
            font-family: 'Courier New', monospace;
            border-bottom: 2px solid #00ff41;
            padding-bottom: 0.3em;
        }
        .stApp .main .block-container .matrix-footer,
        .stApp .main .block-container .matrix-footer p,
        .main .block-container .matrix-footer,
        .main .block-container .matrix-footer p {
            text-align: center;
            color: #00ff41 !important;
            font-family: 'Courier New', monospace;
            margin-top: 2em;
        }
        .stApp .main .block-container .philosophy-quote,
        .main .block-container .philosophy-quote {
            font-size: 1.3em;
            font-weight: bold;
            color: #00ff41 !important;
            text-align: center;
            padding: 1em;
            font-family: 'Courier New', monospace;
            text-shadow: 0 0 10px rgba(0,255,65,0.3);
        }
        /* ===== HUB CARD - CENTERED PAN HANDLER CENTRAL ===== */
        .stApp .main .block-container .hub-card,
        .main .block-container .hub-card {
            background: linear-gradient(135deg, rgba(0,255,65,0.12) 0%, rgba(0,204,51,0.06) 100%) !important;
            border: 2px solid #00ff41;
            border-radius: 12px;
            padding: 2em;
            margin: 1.5em auto;
            max-width: 700px;
            box-shadow: 0 0 30px rgba(0,255,65,0.4);
            text-align: center;
        }
        .stApp .main .block-container .hub-card h3,
        .main .block-container .hub-card h3 {
            color: #00ff41 !important;
            font-family: 'Courier New', monospace;
            font-size: 1.8em;
            margin-bottom: 0.5em;
            letter-spacing: 0.05em;
        }
        .stApp .main .block-container .hub-card p,
        .stApp .main .block-container .hub-card strong,
        .stApp .main .block-container .hub-card em,
        .stApp .main .block-container .hub-card span,
        .main .block-container .hub-card p,
        .main .block-container .hub-card strong,
        .main .block-container .hub-card em,
        .main .block-container .hub-card span {
            color: #00cc33 !important;
            font-family: 'Courier New', monospace;
        }
        .stApp .main .block-container .hub-card ul,
        .main .block-container .hub-card ul {
            text-align: left;
            display: inline-block;
            margin-top: 1em;
        }
        .stApp .main .block-container .hub-card li,
        .main .block-container .hub-card li {
            color: #00ff41 !important;
            font-family: 'Courier New', monospace;
            margin: 0.3em 0;
        }
        /* ===== NEON SIGNS - TRANSIT HUB STYLE ===== */
        /* Note: @keyframes animations stripped by Streamlit Cloud */
        /* Using hover transitions as fallback for interactive glow */

        /* Base neon animation - kept for local development */
        @keyframes neonGlow {
            0%, 100% { filter: brightness(1) drop-shadow(0 0 3px currentColor); }
            50% { filter: brightness(1.2) drop-shadow(0 0 8px currentColor) drop-shadow(0 0 15px currentColor); }
        }

        @keyframes neonFlicker {
            0%, 19.999%, 22%, 62.999%, 64%, 64.999%, 70%, 100% { opacity: 1; }
            20%, 21.999%, 63%, 63.999%, 65%, 69.999% { opacity: 0.4; }
        }

        @keyframes hologramScan {
            0% { background-position: 0% 0%; }
            100% { background-position: 0% 100%; }
        }

        /* LIVE - Hot pink/magenta neon */
        .stApp .main .block-container .neon-live,
        .main .block-container .neon-live {
            display: inline-block;
            padding: 0.3em 0.7em;
            font-size: 0.85em;
            font-weight: bold;
            font-family: 'Courier New', monospace;
            text-transform: uppercase;
            letter-spacing: 0.2em;
            color: #ff00ff !important;
            background: transparent;
            border: 2px solid #ff00ff;
            border-radius: 3px;
            text-shadow:
                0 0 5px #ff00ff,
                0 0 10px #ff00ff,
                0 0 20px #ff00ff,
                0 0 40px #ff00ff;
            box-shadow:
                0 0 5px #ff00ff,
                0 0 10px rgba(255,0,255,0.5),
                inset 0 0 10px rgba(255,0,255,0.1);
            animation: neonGlow 2s ease-in-out infinite, neonFlicker 4s linear infinite;
            position: relative;
            transition: all 0.3s ease;
        }

        .stApp .main .block-container .neon-live:hover,
        .main .block-container .neon-live:hover {
            box-shadow: 0 0 15px #ff00ff, 0 0 30px #ff00ff, 0 0 45px rgba(255,0,255,0.7);
            transform: scale(1.05);
        }

        /* YOU ARE HERE - Warm amber/gold beacon */
        .stApp .main .block-container .neon-here,
        .main .block-container .neon-here {
            display: inline-block;
            padding: 0.3em 0.7em;
            font-size: 0.8em;
            font-weight: bold;
            font-family: 'Courier New', monospace;
            text-transform: uppercase;
            letter-spacing: 0.15em;
            color: #ffcc00 !important;
            background: rgba(255,200,0,0.1);
            border: 2px solid #ffcc00;
            border-radius: 3px;
            text-shadow:
                0 0 5px #ffcc00,
                0 0 10px #ffaa00,
                0 0 20px #ff8800;
            box-shadow:
                0 0 10px rgba(255,200,0,0.5),
                0 0 20px rgba(255,170,0,0.3),
                inset 0 0 10px rgba(255,200,0,0.1);
            animation: neonGlow 2s ease-in-out infinite;
            transition: all 0.3s ease;
        }

        .stApp .main .block-container .neon-here:hover,
        .main .block-container .neon-here:hover {
            box-shadow: 0 0 15px #ffcc00, 0 0 30px #ffaa00, 0 0 45px rgba(255,170,0,0.7);
            transform: scale(1.05);
        }

        /* ACTIVE - Electric blue */
        .stApp .main .block-container .neon-active,
        .main .block-container .neon-active {
            display: inline-block;
            padding: 0.3em 0.7em;
            font-size: 0.85em;
            font-weight: bold;
            font-family: 'Courier New', monospace;
            text-transform: uppercase;
            letter-spacing: 0.15em;
            color: #00aaff !important;
            background: transparent;
            border: 2px solid #00aaff;
            border-radius: 3px;
            text-shadow:
                0 0 5px #00aaff,
                0 0 10px #00aaff,
                0 0 20px #00aaff;
            box-shadow:
                0 0 8px rgba(0,170,255,0.6),
                inset 0 0 10px rgba(0,170,255,0.1);
            animation: neonGlow 2.5s ease-in-out infinite;
            transition: all 0.3s ease;
        }

        .stApp .main .block-container .neon-active:hover,
        .main .block-container .neon-active:hover {
            box-shadow: 0 0 15px #00aaff, 0 0 30px #00aaff, 0 0 45px rgba(0,170,255,0.7);
            transform: scale(1.05);
        }

        /* Hub badge alias for backwards compat */
        .stApp .main .block-container .hub-badge,
        .main .block-container .hub-badge {
            display: inline-block;
            padding: 0.3em 0.7em;
            font-size: 0.85em;
            font-weight: bold;
            font-family: 'Courier New', monospace;
            text-transform: uppercase;
            letter-spacing: 0.2em;
            color: #ff00ff !important;
            background: transparent;
            border: 2px solid #ff00ff;
            border-radius: 3px;
            text-shadow: 0 0 5px #ff00ff, 0 0 10px #ff00ff, 0 0 20px #ff00ff;
            box-shadow: 0 0 5px #ff00ff, 0 0 10px rgba(255,0,255,0.5);
            animation: neonGlow 2s ease-in-out infinite, neonFlicker 4s linear infinite;
            transition: all 0.3s ease;
        }

        .stApp .main .block-container .hub-badge:hover,
        .main .block-container .hub-badge:hover {
            box-shadow: 0 0 15px #ff00ff, 0 0 30px #ff00ff, 0 0 45px rgba(255,0,255,0.7);
            transform: scale(1.05);
        }

        /* ===== INLINE ELEMENT HOVER EFFECTS ===== */
        /* For elements using inline styles - hover via parent selectors */

        /* Jump button hover - enhanced glow */
        .stApp .main .block-container a[href*="pan-handlers"],
        .main .block-container a[href*="pan-handlers"] {
            transition: all 0.3s ease !important;
        }

        .stApp .main .block-container a[href*="pan-handlers"]:hover,
        .main .block-container a[href*="pan-handlers"]:hover {
            box-shadow: 0 0 30px #ff00ff, 0 0 50px #ff00ff, 0 0 70px rgba(255,0,255,0.6) !important;
            transform: scale(1.08) !important;
        }

        /* Portal ring hover - spin faster */
        .stApp .main .block-container .portal-ring:hover,
        .main .block-container .portal-ring:hover {
            box-shadow: 0 0 50px rgba(0,255,65,0.9), inset 0 0 40px rgba(0,255,65,0.3);
        }

        /* Feature tags hover */
        .stApp .main .block-container .feature-tag:hover,
        .main .block-container .feature-tag:hover {
            background: rgba(0,255,65,0.25);
            box-shadow: 0 0 10px rgba(0,255,65,0.4);
            transform: scale(1.05);
        }

        /* ===== TRANSIT HUB THEME ===== */

        /* Platform Gate - Main transit cards */
        @keyframes tunnelPerspective {
            0%, 100% { transform: perspective(500px) rotateX(2deg); }
            50% { transform: perspective(500px) rotateX(-1deg); }
        }

        @keyframes dataStream {
            0% { background-position: 0% 0%; }
            100% { background-position: 100% 100%; }
        }

        .stApp .main .block-container .platform-gate,
        .main .block-container .platform-gate {
            background:
                linear-gradient(135deg, rgba(0,30,0,0.95) 0%, rgba(0,50,20,0.9) 100%),
                repeating-linear-gradient(0deg, transparent, transparent 2px, rgba(0,255,65,0.03) 2px, rgba(0,255,65,0.03) 4px);
            border: 2px solid #00ff41;
            border-radius: 15px;
            padding: 1.5em;
            margin: 1em 0;
            position: relative;
            overflow: hidden;
            box-shadow:
                0 0 30px rgba(0,255,65,0.15),
                inset 0 0 50px rgba(0,255,65,0.05),
                inset 0 -30px 60px rgba(0,0,0,0.3);
        }

        /* Scan line effect */
        .stApp .main .block-container .platform-gate::before,
        .main .block-container .platform-gate::before {
            content: '';
            position: absolute;
            top: 0; left: 0; right: 0;
            height: 3px;
            background: linear-gradient(90deg, transparent, #00ff41, transparent);
            animation: dataStream 3s linear infinite;
        }

        /* Platform header bar */
        .stApp .main .block-container .platform-header,
        .main .block-container .platform-header {
            display: flex;
            align-items: center;
            justify-content: space-between;
            padding-bottom: 1em;
            border-bottom: 1px solid rgba(0,255,65,0.3);
            margin-bottom: 1em;
        }

        .stApp .main .block-container .platform-id,
        .main .block-container .platform-id {
            font-family: 'Courier New', monospace;
            font-size: 0.8em;
            color: #00cc33 !important;
            background: rgba(0,255,65,0.1);
            padding: 0.3em 0.8em;
            border-radius: 4px;
            border: 1px solid rgba(0,255,65,0.3);
        }

        /* Tunnel entrance effect for cards */
        .stApp .main .block-container .tunnel-card,
        .main .block-container .tunnel-card {
            background:
                radial-gradient(ellipse at center, rgba(0,50,20,0.9) 0%, rgba(0,20,10,0.95) 60%, rgba(0,10,5,1) 100%);
            border: 3px solid #00ff41;
            border-radius: 50% / 10%;
            padding: 2em;
            margin: 1em 0;
            position: relative;
            text-align: center;
            box-shadow:
                0 0 40px rgba(0,255,65,0.3),
                inset 0 0 80px rgba(0,255,65,0.1),
                inset 0 0 120px rgba(0,0,0,0.5);
            animation: tunnelPerspective 6s ease-in-out infinite;
        }

        /* Departure board style */
        .stApp .main .block-container .departure-board,
        .main .block-container .departure-board {
            background: linear-gradient(180deg, #0a0a0a 0%, #151515 100%);
            border: 3px solid #333;
            border-radius: 10px;
            padding: 1em;
            font-family: 'Courier New', monospace;
            box-shadow:
                inset 0 0 20px rgba(0,0,0,0.8),
                0 5px 20px rgba(0,0,0,0.5);
        }

        .stApp .main .block-container .departure-row,
        .main .block-container .departure-row {
            display: flex;
            align-items: center;
            padding: 0.8em;
            border-bottom: 1px solid #222;
            transition: background 0.3s;
        }

        .stApp .main .block-container .departure-row:hover,
        .main .block-container .departure-row:hover {
            background: rgba(0,255,65,0.05);
        }

        .stApp .main .block-container .departure-dest,
        .main .block-container .departure-dest {
            flex: 2;
            color: #ffaa00 !important;
            font-weight: bold;
            text-shadow: 0 0 10px rgba(255,170,0,0.5);
        }

        .stApp .main .block-container .departure-status,
        .main .block-container .departure-status {
            flex: 1;
            text-align: center;
        }

        .stApp .main .block-container .departure-platform,
        .main .block-container .departure-platform {
            flex: 0.5;
            text-align: right;
            color: #00ff41 !important;
            font-size: 1.2em;
            font-weight: bold;
        }

        /* Station connector lines */
        .stApp .main .block-container .station-connector,
        .main .block-container .station-connector {
            position: relative;
            padding: 2em 0;
        }

        .stApp .main .block-container .station-connector::before,
        .main .block-container .station-connector::before {
            content: '';
            position: absolute;
            left: 50%;
            top: 0;
            bottom: 0;
            width: 4px;
            background: linear-gradient(180deg, transparent, #00ff41, #00ff41, transparent);
            box-shadow: 0 0 15px rgba(0,255,65,0.5);
        }

        .stApp .main .block-container .station-node,
        .main .block-container .station-node {
            position: relative;
            z-index: 1;
            background: #0a0a0a;
            border: 3px solid #00ff41;
            border-radius: 50%;
            width: 20px;
            height: 20px;
            margin: 0 auto;
            box-shadow: 0 0 15px rgba(0,255,65,0.5);
        }

        /* ===== MIRROR CARDS - Through the Looking Glass ===== */
        .stApp .main .block-container .mirror-card,
        .main .block-container .mirror-card {
            background:
                linear-gradient(135deg, rgba(0,30,0,0.95) 0%, rgba(0,50,20,0.9) 100%);
            border: 2px solid #00ff41;
            border-radius: 15px;
            padding: 1.5em;
            position: relative;
            overflow: hidden;
            box-shadow:
                0 0 30px rgba(0,255,65,0.15),
                inset 0 0 50px rgba(0,255,65,0.05);
        }

        /* Left mirror - normal orientation */
        .stApp .main .block-container .mirror-left,
        .main .block-container .mirror-left {
            border-left: 4px solid #00ffff;
            border-right: 1px solid rgba(0,255,65,0.3);
        }

        /* Right mirror - reflected/flipped styling */
        .stApp .main .block-container .mirror-right,
        .main .block-container .mirror-right {
            border-right: 4px solid #00ffff;
            border-left: 1px solid rgba(0,255,65,0.3);
            text-align: right;
        }

        .stApp .main .block-container .mirror-right .feature-grid,
        .main .block-container .mirror-right .feature-grid {
            justify-content: flex-end;
        }

        .stApp .main .block-container .mirror-right .mirror-header,
        .main .block-container .mirror-right .mirror-header {
            flex-direction: row-reverse;
        }

        /* Mirror header with badge positioning */
        .stApp .main .block-container .mirror-header,
        .main .block-container .mirror-header {
            display: flex;
            justify-content: space-between;
            align-items: flex-start;
            margin-bottom: 1em;
        }

        /* Corner badge positioning */
        .stApp .main .block-container .corner-badge,
        .main .block-container .corner-badge {
            position: absolute;
            top: 0.8em;
            right: 0.8em;
        }

        .stApp .main .block-container .mirror-left .corner-badge,
        .main .block-container .mirror-left .corner-badge {
            right: 0.8em;
            left: auto;
        }

        .stApp .main .block-container .mirror-right .corner-badge,
        .main .block-container .mirror-right .corner-badge {
            left: 0.8em;
            right: auto;
        }

        /* Reflection label - gold/amber like a brass nameplate */
        .stApp .main .block-container .neon-reflection,
        .main .block-container .neon-reflection {
            display: inline-block;
            padding: 0.3em 0.7em;
            font-size: 0.8em;
            font-weight: bold;
            font-family: 'Courier New', monospace;
            text-transform: uppercase;
            letter-spacing: 0.15em;
            color: #ffd700 !important;
            background: rgba(255,215,0,0.1);
            border: 1px solid #ffd700;
            border-radius: 3px;
            text-shadow: 0 0 5px rgba(255,215,0,0.5);
            box-shadow: 0 0 8px rgba(255,215,0,0.3);
        }

        /* Mirror reflection shimmer effect */
        .stApp .main .block-container .mirror-card::after,
        .main .block-container .mirror-card::after {
            content: '';
            position: absolute;
            top: 0;
            left: -100%;
            width: 50%;
            height: 100%;
            background: linear-gradient(
                90deg,
                transparent,
                rgba(0,255,255,0.05),
                transparent
            );
            animation: mirrorShimmer 4s ease-in-out infinite;
        }

        @keyframes mirrorShimmer {
            0%, 100% { left: -100%; }
            50% { left: 150%; }
        }

        /* ===== ORIGIN CARD - Current Location ===== */
        .stApp .main .block-container .origin-card,
        .main .block-container .origin-card {
            background: linear-gradient(135deg, rgba(0,30,0,0.95) 0%, rgba(0,50,20,0.9) 100%);
            border: 2px solid #00ff41;
            border-radius: 15px 0 0 15px;
            padding: 0.8em 1.5em 1.5em 1.5em;
            padding-right: 2em;
            position: relative;
            overflow: visible;
            box-shadow: 0 0 30px rgba(0,255,65,0.15);
            min-height: 380px;
            height: 380px;
            display: flex;
            flex-direction: column;
            text-align: center;
        }

        /* The KEY - protruding connector from origin card */
        .stApp .main .block-container .origin-card::after,
        .main .block-container .origin-card::after {
            content: '';
            position: absolute;
            right: -20px;
            top: 50%;
            transform: translateY(-50%);
            width: 40px;
            height: 60px;
            background: linear-gradient(90deg, rgba(0,50,20,0.95) 0%, rgba(0,80,30,0.9) 100%);
            border: 2px solid #00ff41;
            border-left: none;
            border-radius: 0 30px 30px 0;
            box-shadow: 0 0 20px rgba(0,255,65,0.3);
            z-index: 10;
        }

        /* Energy pulse traveling through the key */
        @keyframes keyPulse {
            0%, 100% { box-shadow: 0 0 10px rgba(0,255,65,0.3), inset 0 0 10px rgba(0,255,65,0.1); }
            50% { box-shadow: 0 0 25px rgba(0,255,65,0.6), 0 0 40px rgba(0,255,65,0.3), inset 0 0 20px rgba(0,255,65,0.2); }
        }

        .stApp .main .block-container .origin-card::before,
        .main .block-container .origin-card::before {
            content: '⚡';
            position: absolute;
            right: -10px;
            top: 50%;
            transform: translateY(-50%);
            font-size: 1.2em;
            z-index: 20;
            animation: keyPulse 2s ease-in-out infinite;
            filter: drop-shadow(0 0 5px #00ff41);
        }

        .stApp .main .block-container .origin-header,
        .main .block-container .origin-header {
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 0.5em;
            margin-bottom: 0.5em;
        }

        .stApp .main .block-container .origin-marker,
        .main .block-container .origin-marker {
            font-size: 1.2em;
        }

        .stApp .main .block-container .origin-stats,
        .main .block-container .origin-stats {
            display: flex;
            justify-content: center;
            gap: 1em;
            margin: 1em 0;
        }

        .stApp .main .block-container .origin-stat,
        .main .block-container .origin-stat {
            background: rgba(0,255,65,0.1);
            border: 1px solid rgba(0,255,65,0.3);
            border-radius: 8px;
            padding: 0.5em 1em;
            text-align: center;
            flex: 1;
        }

        .stApp .main .block-container .stat-value,
        .main .block-container .stat-value {
            display: block;
            font-size: 1.2em;
            font-weight: bold;
            color: #00ff41 !important;
        }

        .stApp .main .block-container .stat-label,
        .main .block-container .stat-label {
            display: block;
            font-size: 0.7em;
            color: #00cc33 !important;
            text-transform: uppercase;
            letter-spacing: 0.1em;
        }

        /* ===== PORTAL DESTINATION - Jump Target ===== */
        .stApp .main .block-container .portal-destination,
        .main .block-container .portal-destination {
            background: linear-gradient(135deg, rgba(40,0,40,0.95) 0%, rgba(20,0,30,0.9) 100%);
            border: 3px solid #ff00ff;
            border-radius: 0 15px 15px 0;
            padding: 0.8em 1.5em 1.5em 1.5em;
            padding-left: 2.5em;
            position: relative;
            overflow: visible;
            box-shadow:
                0 0 40px rgba(255,0,255,0.2),
                inset 0 0 60px rgba(255,0,255,0.05);
            min-height: 380px;
            height: 380px;
        }

        /* The KEYHOLE - receiving socket on portal card */
        .stApp .main .block-container .portal-destination::after,
        .main .block-container .portal-destination::after {
            content: '';
            position: absolute;
            left: -22px;
            top: 50%;
            transform: translateY(-50%);
            width: 44px;
            height: 64px;
            background: linear-gradient(90deg, rgba(60,0,60,0.9) 0%, rgba(40,0,40,0.95) 100%);
            border: 3px solid #ff00ff;
            border-right: none;
            border-radius: 32px 0 0 32px;
            box-shadow: 0 0 20px rgba(255,0,255,0.4), inset 0 0 15px rgba(255,0,255,0.2);
            z-index: 5;
        }

        @keyframes keyholeGlow {
            0%, 100% { opacity: 0.5; }
            50% { opacity: 1; }
        }

        .stApp .main .block-container .portal-header,
        .main .block-container .portal-header {
            text-align: center;
            margin-bottom: 0.5em;
        }

        .stApp .main .block-container .portal-visual,
        .main .block-container .portal-visual {
            display: flex;
            justify-content: center;
            align-items: center;
            margin: 1em 0;
        }

        .stApp .main .block-container .portal-btn-large,
        .main .block-container .portal-btn-large {
            display: inline-block;
            background: linear-gradient(135deg, #ff00ff 0%, #cc00cc 100%);
            color: #ffffff !important;
            padding: 0.8em 2em;
            border-radius: 30px;
            font-weight: bold;
            font-family: 'Courier New', monospace;
            text-decoration: none;
            font-size: 1em;
            transition: all 0.3s ease;
            box-shadow: 0 0 20px rgba(255,0,255,0.5);
            text-shadow: 0 0 10px rgba(255,255,255,0.5);
        }

        .stApp .main .block-container .portal-btn-large:hover,
        .main .block-container .portal-btn-large:hover {
            background: linear-gradient(135deg, #ff44ff 0%, #ff00ff 100%);
            box-shadow: 0 0 40px rgba(255,0,255,0.8), 0 0 60px rgba(255,0,255,0.4);
            transform: scale(1.05);
        }

        /* ===== PORTAL CHAMBER - UNIFIED HUB + GATEWAY ===== */
        @keyframes portalSpin {
            0% { transform: rotate(0deg); }
            100% { transform: rotate(360deg); }
        }

        @keyframes portalPulse {
            0%, 100% {
                box-shadow: 0 0 30px rgba(0,255,65,0.4), inset 0 0 30px rgba(0,255,65,0.1);
                transform: scale(1);
            }
            50% {
                box-shadow: 0 0 60px rgba(0,255,65,0.8), 0 0 100px rgba(0,255,65,0.4), inset 0 0 50px rgba(0,255,65,0.2);
                transform: scale(1.02);
            }
        }

        @keyframes beamFlow {
            0% { background-position: 0% 50%; }
            100% { background-position: 200% 50%; }
        }

        @keyframes beamPulse {
            0%, 100% { opacity: 0.3; left: 0%; }
            50% { opacity: 1; }
            100% { left: 100%; }
        }

        .stApp .main .block-container .portal-chamber,
        .main .block-container .portal-chamber {
            background: linear-gradient(135deg, rgba(0,20,0,0.95) 0%, rgba(0,40,0,0.9) 50%, rgba(0,20,0,0.95) 100%) !important;
            border: 2px solid #00ff41;
            border-radius: 20px;
            padding: 1.5em;
            margin: 1em 0;
            box-shadow: 0 0 40px rgba(0,255,65,0.2), inset 0 0 60px rgba(0,255,65,0.05);
        }

        .stApp .main .block-container .chamber-content,
        .main .block-container .chamber-content {
            display: flex;
            align-items: center;
            justify-content: space-between;
            gap: 1em;
            flex-wrap: wrap;
        }

        /* Left: Hub Info */
        .stApp .main .block-container .chamber-hub,
        .main .block-container .chamber-hub {
            flex: 1 1 55%;
            min-width: 280px;
            padding-right: 1em;
        }

        .stApp .main .block-container .chamber-hub h3,
        .main .block-container .chamber-hub h3 {
            color: #00ff41 !important;
            font-family: 'Courier New', monospace !important;
            font-size: 1.3em;
            margin-bottom: 0.5em;
            text-shadow: 0 0 10px rgba(0,255,65,0.5);
        }

        .stApp .main .block-container .chamber-hub p,
        .main .block-container .chamber-hub p {
            color: #00cc33 !important;
            font-family: 'Courier New', monospace !important;
            font-size: 0.9em;
            margin: 0.3em 0;
        }

        .stApp .main .block-container .feature-grid,
        .main .block-container .feature-grid {
            display: flex;
            flex-wrap: wrap;
            justify-content: center;
            gap: 0.4em;
            margin-top: 0.8em;
        }

        .stApp .main .block-container .feature-tag,
        .main .block-container .feature-tag {
            background: rgba(0,255,65,0.1);
            border: 1px solid rgba(0,255,65,0.3);
            border-radius: 15px;
            padding: 0.3em 0.7em;
            font-size: 0.75em;
            color: #00ff41 !important;
            font-family: 'Courier New', monospace;
            white-space: nowrap;
        }

        /* Center: Connection Beam */
        .stApp .main .block-container .portal-beam,
        .main .block-container .portal-beam {
            flex: 0 0 60px;
            display: flex;
            align-items: center;
            justify-content: center;
            position: relative;
            height: 120px;
        }

        .stApp .main .block-container .beam-line,
        .main .block-container .beam-line {
            width: 4px;
            height: 100%;
            background: linear-gradient(180deg, transparent, #00ff41, #00ff88, #00ff41, transparent);
            background-size: 100% 200%;
            animation: beamFlow 2s linear infinite;
            border-radius: 2px;
            box-shadow: 0 0 10px rgba(0,255,65,0.5);
        }

        .stApp .main .block-container .beam-pulse,
        .main .block-container .beam-pulse {
            position: absolute;
            width: 12px;
            height: 12px;
            background: #00ff41;
            border-radius: 50%;
            animation: beamPulse 1.5s ease-in-out infinite;
            box-shadow: 0 0 20px rgba(0,255,65,0.8);
        }

        /* Right: Portal Gateway */
        .stApp .main .block-container .chamber-portal,
        .main .block-container .chamber-portal {
            flex: 0 0 150px;
            display: flex;
            flex-direction: column;
            align-items: center;
            text-align: center;
        }

        .stApp .main .block-container .portal-ring,
        .main .block-container .portal-ring {
            width: 100px;
            height: 100px;
            border-radius: 50%;
            border: 3px solid #00ff41;
            display: flex;
            align-items: center;
            justify-content: center;
            position: relative;
            animation: portalPulse 3s ease-in-out infinite;
            background: radial-gradient(circle, rgba(0,255,65,0.1) 0%, transparent 70%);
        }

        .stApp .main .block-container .portal-ring::before,
        .main .block-container .portal-ring::before {
            content: '';
            position: absolute;
            width: 120%;
            height: 120%;
            border: 2px dashed rgba(0,255,65,0.3);
            border-radius: 50%;
            animation: portalSpin 8s linear infinite;
        }

        .stApp .main .block-container .portal-inner,
        .main .block-container .portal-inner {
            width: 70px;
            height: 70px;
            border-radius: 50%;
            background: radial-gradient(circle, rgba(0,80,30,0.9) 0%, rgba(0,40,15,0.95) 100%);
            display: flex;
            align-items: center;
            justify-content: center;
            border: 2px solid rgba(0,255,65,0.5);
        }

        .stApp .main .block-container .portal-icon,
        .main .block-container .portal-icon {
            font-size: 2em;
            animation: portalSpin 4s linear infinite reverse;
        }

        .stApp .main .block-container .portal-btn,
        .main .block-container .portal-btn {
            display: inline-block;
            background: linear-gradient(135deg, #00ff41 0%, #00cc33 100%);
            color: #0a0a0a !important;
            padding: 0.6em 1.2em;
            border-radius: 25px;
            font-weight: bold;
            font-family: 'Courier New', monospace;
            text-decoration: none;
            font-size: 0.9em;
            margin-top: 0.8em;
            transition: all 0.3s ease;
            box-shadow: 0 0 15px rgba(0,255,65,0.5);
        }

        .stApp .main .block-container .portal-btn:hover,
        .main .block-container .portal-btn:hover {
            background: linear-gradient(135deg, #00ff88 0%, #00ff41 100%);
            box-shadow: 0 0 30px rgba(0,255,65,0.8), 0 0 50px rgba(0,255,65,0.4);
            transform: scale(1.1);
        }

        /* Portal icon hover - spins on interaction */
        .stApp .main .block-container .portal-icon,
        .main .block-container .portal-icon {
            transition: transform 0.5s ease;
        }

        .stApp .main .block-container .portal-icon:hover,
        .main .block-container .portal-icon:hover {
            transform: rotate(180deg);
        }

        .stApp .main .block-container .portal-status,
        .main .block-container .portal-status {
            color: #00ff41 !important;
            font-family: 'Courier New', monospace !important;
            font-size: 0.7em;
            margin-top: 0.5em;
            opacity: 0.8;
        }

        /* Mobile: Stack vertically */
        @media (max-width: 600px) {
            .stApp .main .block-container .chamber-content,
            .main .block-container .chamber-content {
                flex-direction: column;
                text-align: center;
            }
            .stApp .main .block-container .chamber-hub,
            .main .block-container .chamber-hub {
                padding-right: 0;
            }
            .stApp .main .block-container .portal-beam,
            .main .block-container .portal-beam {
                height: 40px;
                width: 100%;
            }
            .stApp .main .block-container .beam-line,
            .main .block-container .beam-line {
                width: 100%;
                height: 4px;
                background: linear-gradient(90deg, transparent, #00ff41, #00ff88, #00ff41, transparent);
            }
        }
        </style>
    """, unsafe_allow_html=True)

    # ══════════════════════════════════════════════════════════════
    # TRANSIT HUB HEADER
    # ══════════════════════════════════════════════════════════════
    st.markdown("""
    <div class="tunnel-card">
        <h1 style="font-size: 2.2em; margin: 0; letter-spacing: 0.1em;">🚉 DIMENSIONAL TRANSIT HUB</h1>
        <p style="font-size: 1.1em; margin: 0.5em 0;">Pan Handler Central Station</p>
        <p style="font-size: 0.85em; opacity: 0.7;">Where Projects Travel Between Worlds</p>
    </div>
    """, unsafe_allow_html=True)

    # Philosophy banner (inline styles for Streamlit Cloud)
    if pan_handler_data:
        default_philosophy = "FUCK IT, WE'LL DO IT LIVE!"
        philosophy = pan_handler_data.get('meta', {}).get('philosophy', default_philosophy)
        st.markdown(f"""
        <div style="text-align: center; padding: 1em; margin: 1em 0;
                    background: linear-gradient(90deg, transparent 0%, rgba(0,255,65,0.1) 50%, transparent 100%);
                    border-top: 1px solid rgba(0,255,65,0.3); border-bottom: 1px solid rgba(0,255,65,0.3);">
            <span style="font-family: 'Courier New', monospace; font-size: 1.1em; color: #00ff41 !important;
                        letter-spacing: 0.05em;">{philosophy}</span>
        </div>
        """, unsafe_allow_html=True)

    # ══════════════════════════════════════════════════════════════
    # SECTION 1: DEPARTURE BOARD - Connected Platforms
    # ══════════════════════════════════════════════════════════════
    st.markdown("""
    <div style="background: linear-gradient(180deg, rgba(0,255,65,0.15) 0%, rgba(0,255,65,0.05) 100%);
                border: 2px solid #00ff41; border-radius: 10px 10px 0 0; padding: 0.8em 1.2em; margin-top: 1em;">
        <div style="display: flex; justify-content: space-between; align-items: center;">
            <h2 style="margin: 0; color: #00ff41 !important;">📡 CONNECTED PLATFORMS</h2>
            <span style="background: rgba(0,0,0,0.5); border: 1px solid #00ff41; border-radius: 4px;
                        padding: 0.3em 0.8em; font-family: 'Courier New', monospace; font-size: 0.9em;
                        color: #00ff41 !important; letter-spacing: 0.1em;">GATE A</span>
        </div>
    </div>
    """, unsafe_allow_html=True)

    # Two-panel layout with KEY-KEYHOLE connector in center
    # Using 3 columns: Origin (wide) | Connector (narrow) | Portal (wide)
    col1, col_connector, col2 = st.columns([10, 1, 10])

    with col1:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(0,30,0,0.95) 0%, rgba(0,50,20,0.9) 100%);
                    border: 3px solid #00ff41; border-right: none; border-radius: 15px 0 0 15px;
                    padding: 1.5em; padding-right: 1em; box-shadow: 0 0 20px #00ff41; height: 420px;">
            <div style="text-align: center; margin-bottom: 0.5em;">
                <span style="display: inline-block; padding: 0.3em 0.8em; font-size: 0.8em; font-weight: bold;
                            font-family: 'Courier New', monospace; text-transform: uppercase; letter-spacing: 0.15em;
                            color: #ffdd44 !important; background: rgba(255,204,0,0.2); border: 3px solid #ffcc00;
                            border-radius: 3px; box-shadow: 0 0 12px #ffcc00;">CURRENT LOCATION</span>
            </div>
            <h2 style="margin: 0.3em 0; font-size: 1.6em; text-align: center; color: #00ff41 !important;">📡 Nyquist Consciousness</h2>
            <p style="font-size: 0.95em; opacity: 0.8; margin-bottom: 1em; text-align: center; color: #00cc33 !important;">Core Engine / Identity Lab</p>
            <div style="display: flex; justify-content: center; gap: 1em; margin: 1em 0;">
                <div style="background: rgba(0,255,65,0.1); border: 1px solid rgba(0,255,65,0.3);
                            border-radius: 8px; padding: 0.5em 1em; text-align: center; flex: 1;">
                    <span style="display: block; font-size: 1.2em; font-weight: bold; color: #00ff41 !important;">S7</span>
                    <span style="display: block; font-size: 0.7em; color: #00cc33 !important; text-transform: uppercase;">Complete</span>
                </div>
                <div style="background: rgba(0,255,65,0.1); border: 1px solid rgba(0,255,65,0.3);
                            border-radius: 8px; padding: 0.5em 1em; text-align: center; flex: 1;">
                    <span style="display: block; font-size: 1.2em; font-weight: bold; color: #00ff41 !important;">S8/S9</span>
                    <span style="display: block; font-size: 0.7em; color: #00cc33 !important; text-transform: uppercase;">Design</span>
                </div>
                <div style="background: rgba(0,255,65,0.1); border: 1px solid rgba(0,255,65,0.3);
                            border-radius: 8px; padding: 0.5em 1em; text-align: center; flex: 1;">
                    <span style="display: block; font-size: 1.2em; font-weight: bold; color: #00ff41 !important;">29</span>
                    <span style="display: block; font-size: 0.7em; color: #00cc33 !important; text-transform: uppercase;">Ships</span>
                </div>
            </div>
            <div style="display: flex; flex-wrap: wrap; justify-content: center; gap: 0.5em; margin-top: 1em;">
                <span style="background: rgba(0,255,65,0.15); border: 1px solid #00ff41; border-radius: 12px;
                            padding: 0.3em 0.8em; font-size: 0.75em; color: #00ff41 !important;">S0-S9 Stack</span>
                <span style="background: rgba(0,255,65,0.15); border: 1px solid #00ff41; border-radius: 12px;
                            padding: 0.3em 0.8em; font-size: 0.75em; color: #00ff41 !important;">AI Armada</span>
                <span style="background: rgba(0,255,65,0.15); border: 1px solid #00ff41; border-radius: 12px;
                            padding: 0.3em 0.8em; font-size: 0.75em; color: #00ff41 !important;">Omega Nova</span>
                <span style="background: rgba(0,255,65,0.15); border: 1px solid #00ff41; border-radius: 12px;
                            padding: 0.3em 0.8em; font-size: 0.75em; color: #00ff41 !important;">AVLAR</span>
            </div>
        </div>
        """, unsafe_allow_html=True)

    with col_connector:
        st.markdown("""
        <div style="display: flex; flex-direction: column; justify-content: center; align-items: center;
                    height: 420px; position: relative;">
            <div style="width: 50px; height: 70px; position: relative; display: flex; align-items: center; justify-content: center;">
                <div style="position: absolute; left: 0; width: 28px; height: 50px;
                            background: linear-gradient(90deg, rgba(0,50,20,0.95) 0%, rgba(0,80,30,0.9) 100%);
                            border: 2px solid #00ff41; border-left: none;
                            border-radius: 0 25px 25px 0;
                            box-shadow: 0 0 15px rgba(0,255,65,0.5);"></div>
                <div style="position: absolute; right: 0; width: 28px; height: 54px;
                            background: linear-gradient(90deg, rgba(60,0,60,0.9) 0%, rgba(40,0,40,0.95) 100%);
                            border: 2px solid #ff00ff; border-right: none;
                            border-radius: 27px 0 0 27px;
                            box-shadow: 0 0 15px rgba(255,0,255,0.5);"></div>
                <span style="position: relative; z-index: 10; font-size: 1.3em;
                            filter: drop-shadow(0 0 8px #00ff41) drop-shadow(0 0 8px #ff00ff);">⚡</span>
            </div>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(40,0,40,0.95) 0%, rgba(20,0,30,0.9) 100%);
                    border: 4px solid #ff00ff; border-left: none; border-radius: 0 15px 15px 0;
                    padding: 1.5em; padding-left: 1em; box-shadow: 0 0 25px #ff00ff;
                    height: 420px;">
            <div style="text-align: center; margin-bottom: 0.5em;">
                <span style="display: inline-block; padding: 0.3em 0.8em; font-size: 0.85em; font-weight: bold;
                            font-family: 'Courier New', monospace; text-transform: uppercase; letter-spacing: 0.15em;
                            color: #ff66ff !important; background: rgba(255,0,255,0.25); border: 3px solid #ff00ff;
                            border-radius: 3px; box-shadow: 0 0 15px #ff00ff;
                            transition: all 0.3s ease;">LIVE PORTAL</span>
            </div>
            <h2 style="margin: 0.3em 0; text-align: center; font-size: 1.6em; color: #ff00ff !important;">🏛️ Pan Handler Central</h2>
            <p style="text-align: center; font-size: 0.85em; opacity: 0.7; margin-bottom: 1em; color: #cc66cc !important;">Federation Hub — All Worlds Connect</p>
            <div style="display: flex; justify-content: center; align-items: center; margin: 1.5em 0;">
                <div style="width: 120px; height: 120px; border-radius: 50%; border: 4px solid #ff00ff;
                            box-shadow: 0 0 25px #ff00ff;
                            display: flex; justify-content: center; align-items: center;
                            background: radial-gradient(circle, rgba(255,0,255,0.3) 0%, rgba(40,0,40,0.8) 70%);">
                    <div style="width: 80px; height: 80px; border-radius: 50%; border: 3px solid #ff66ff;
                                display: flex; justify-content: center; align-items: center;
                                box-shadow: 0 0 15px #ff00ff;
                                background: radial-gradient(circle, rgba(255,0,255,0.4) 0%, transparent 70%);">
                        <span style="font-size: 2.5em;">🌀</span>
                    </div>
                </div>
            </div>
            <div style="text-align: center; margin-top: 1em;">
                <a href="https://pan-handlers.streamlit.app/" target="_blank"
                   style="display: inline-block; padding: 0.8em 2em; background: linear-gradient(135deg, #ff00ff 0%, #cc00cc 100%);
                          color: white !important; text-decoration: none; font-weight: bold; font-size: 1.1em;
                          border-radius: 25px; border: 3px solid #ff66ff;
                          box-shadow: 0 0 20px #ff00ff;">
                    🚀 JUMP TO HUB 🚀
                </a>
            </div>
        </div>
        """, unsafe_allow_html=True)

    # ══════════════════════════════════════════════════════════════
    # SECTION 2: DEPARTURES BOARD - Flagship Projects
    # ══════════════════════════════════════════════════════════════
    st.markdown("""
    <div style="background: linear-gradient(180deg, rgba(0,255,65,0.15) 0%, rgba(0,255,65,0.05) 100%);
                border: 2px solid #00ff41; border-radius: 10px 10px 0 0; padding: 0.8em 1.2em; margin-top: 2em;">
        <div style="display: flex; justify-content: space-between; align-items: center;">
            <h2 style="margin: 0; color: #00ff41 !important;">🚀 DEPARTURES — Flagship Projects</h2>
            <span style="background: rgba(0,0,0,0.5); border: 1px solid #00ff41; border-radius: 4px;
                        padding: 0.3em 0.8em; font-family: 'Courier New', monospace; font-size: 0.9em;
                        color: #00ff41 !important; letter-spacing: 0.1em;">GATE B</span>
        </div>
    </div>
    """, unsafe_allow_html=True)

    if pan_handler_data and 'flagship_projects' in pan_handler_data:
        projects = pan_handler_data['flagship_projects']

        # Departure board style (inline)
        st.markdown("""
        <div style="background: rgba(0,0,0,0.3); border: 1px solid rgba(0,255,65,0.3);
                    border-top: none; border-radius: 0 0 10px 10px; padding: 0.5em;">
        """, unsafe_allow_html=True)

        # Header row with column labels
        st.markdown("""
        <div style="display: flex; align-items: center; background: rgba(0,255,65,0.08);
                    border-bottom: 2px solid #00ff41; padding: 0.5em 0.8em;">
            <span style="flex: 2; color: #00ff41 !important; font-weight: bold; font-size: 0.9em; text-transform: uppercase; letter-spacing: 0.1em;">DESTINATION</span>
            <span style="flex: 1; text-align: center; color: #00ff41 !important; font-weight: bold; font-size: 0.9em; text-transform: uppercase; letter-spacing: 0.1em;">STATUS</span>
            <span style="flex: 1; color: #00ff41 !important; font-weight: bold; font-size: 0.9em; text-transform: uppercase; letter-spacing: 0.1em;">TRACK</span>
            <span style="flex: 0.5; text-align: right; color: #00ff41 !important; font-weight: bold; font-size: 0.9em; text-transform: uppercase; letter-spacing: 0.1em;">SYNC</span>
        </div>
        """, unsafe_allow_html=True)

        # CFA as first entry - connected repo
        st.markdown("""
        <div style="display: flex; align-items: center; padding: 0.6em 0.8em;
                    background: rgba(0,170,255,0.05); border-left: 3px solid #00aaff;
                    border-bottom: 1px solid rgba(0,255,65,0.15);">
            <span style="flex: 2; color: #00aaff !important; font-weight: bold;">⚙️ CFA Framework</span>
            <span style="flex: 1; text-align: center;">
                <span style="display: inline-block; padding: 0.2em 0.6em; font-size: 0.75em; font-weight: bold;
                            color: #00aaff !important; background: rgba(0,170,255,0.15); border: 1px solid #00aaff;
                            border-radius: 3px;">LINKED</span>
            </span>
            <span style="flex: 1; color: #888; font-size: 0.85em;">Framework / v5.0</span>
            <span style="flex: 0.5; text-align: right; color: #00aaff !important;">⚡</span>
        </div>
        """, unsafe_allow_html=True)

        # Sync level tooltip descriptions
        sync_tooltips = {
            1: "Solo - One aligned mind can execute",
            2: "Pair - Two aligned minds can execute",
            3: "Squad - Small team, tight sync required",
            4: "Squad - Small team, tight sync required",
            5: "Coalition - Cross-functional groups needed",
            6: "Coalition - Multiple stakeholders required",
            7: "Movement - Multiple orgs, mass coordination",
            8: "Movement - Mass coordination required",
            9: "Civilization - Systemic change, generational alignment"
        }

        for project in projects[:7]:
            status = project.get('status', 'Concept')
            if status == "In Preparation":
                status_badge = '''<span style="display: inline-block; padding: 0.2em 0.6em; font-size: 0.75em; font-weight: bold;
                                            color: #00aaff !important; background: rgba(0,170,255,0.15); border: 1px solid #00aaff;
                                            border-radius: 3px; text-shadow: 0 0 5px rgba(0,170,255,0.5);">BOARDING</span>'''
            elif status == "Complete":
                status_badge = '''<span style="display: inline-block; padding: 0.2em 0.6em; font-size: 0.75em; font-weight: bold;
                                            color: #ffcc00 !important; background: rgba(255,204,0,0.15); border: 1px solid #ffcc00;
                                            border-radius: 3px; text-shadow: 0 0 5px rgba(255,204,0,0.5);">ARRIVED</span>'''
            else:
                status_badge = '<span style="color: #666; border: 1px solid #444; padding: 0.2em 0.5em; border-radius: 3px; font-size: 0.8em;">SCHEDULED</span>'

            track = project.get('track', 'TBD')
            sync_level = project.get('sync_level', 5)  # Default to 5 if not set
            sync_tooltip = sync_tooltips.get(sync_level, f"Sync Level {sync_level}")

            st.markdown(f"""
            <div style="display: flex; align-items: center; padding: 0.6em 0.8em;
                        border-bottom: 1px solid rgba(0,255,65,0.15);">
                <span style="flex: 2; color: #ffaa00 !important; font-weight: bold;">{project.get('title', 'Untitled')[:35]}</span>
                <span style="flex: 1; text-align: center;">{status_badge}</span>
                <span style="flex: 1; color: #888; font-size: 0.85em;">{track}</span>
                <span style="flex: 0.5; text-align: right; color: #00ff41 !important; font-weight: bold;">{sync_level}</span>
            </div>
            """, unsafe_allow_html=True)

        st.markdown('</div>', unsafe_allow_html=True)

        # Sync Level Legend
        st.markdown("""
        <div style="margin-top: 1em; padding: 1em; background: rgba(0,255,65,0.05); border: 1px solid rgba(0,255,65,0.2); border-radius: 8px;">
            <div style="display: flex; align-items: center; gap: 0.5em; margin-bottom: 0.8em;">
                <span style="color: #00ff41 !important; font-weight: bold; font-size: 0.9em;">SYNC LEVEL</span>
                <span style="color: #00cc33 !important; font-size: 0.8em; opacity: 0.8;">— Collaborative Resonance Required for Manifestation</span>
            </div>
            <div style="display: flex; flex-wrap: wrap; gap: 0.8em; font-size: 0.75em; font-family: 'Courier New', monospace;">
                <span style="color: #888;"><span style="color: #00ff41; font-weight: bold;">1-2</span> Solo/Pair</span>
                <span style="color: #888;"><span style="color: #00ff41; font-weight: bold;">3-4</span> Squad</span>
                <span style="color: #888;"><span style="color: #00ff41; font-weight: bold;">5-6</span> Coalition</span>
                <span style="color: #888;"><span style="color: #ffd700; font-weight: bold;">7-8</span> Movement</span>
                <span style="color: #888;"><span style="color: #ff00ff; font-weight: bold;">9</span> Civilization</span>
            </div>
        </div>
        """, unsafe_allow_html=True)
    else:
        st.info("Loading departures from Pan_Handlers/projects.json...")

    # ══════════════════════════════════════════════════════════════
    # SECTION 3: PROJECT DETAILS (Collapsible)
    # ══════════════════════════════════════════════════════════════
    with st.expander("📋 PROJECT MANIFEST — Detailed View", expanded=False):
        if pan_handler_data and 'flagship_projects' in pan_handler_data:
            project_names = [p.get('title', 'Untitled') for p in pan_handler_data['flagship_projects']]
            selected = st.selectbox("Select destination:", project_names)

            selected_project = next((p for p in pan_handler_data['flagship_projects'] if p.get('title') == selected), None)

            if selected_project:
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

    # ══════════════════════════════════════════════════════════════
    # SECTION 4: STATION STATISTICS
    # ══════════════════════════════════════════════════════════════
    st.markdown("""
    <div class="platform-gate">
        <div class="platform-header">
            <h2 style="margin: 0;">📊 STATION METRICS</h2>
            <span class="platform-id">CONTROL</span>
        </div>
    </div>
    """, unsafe_allow_html=True)

    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric("Total Departures", "7", delta="Active")
        st.caption("Flagship initiatives")

    with col2:
        st.metric("Platforms Connected", "3", delta="All Systems")
        st.caption("Nyquist + CFA + Pan Handlers")

    with col3:
        if pan_handler_data:
            in_prep = sum(1 for p in pan_handler_data.get('flagship_projects', []) if p.get('status') == "In Preparation")
            st.metric("Now Boarding", str(in_prep), delta="Active")
        else:
            st.metric("Now Boarding", "1", delta="Active")
        st.caption("In preparation")

    with col4:
        if pan_handler_data:
            concept = sum(1 for p in pan_handler_data.get('flagship_projects', []) if p.get('status') == "Concept")
            st.metric("Scheduled", str(concept), delta="Queued")
        else:
            st.metric("Scheduled", "6", delta="Queued")
        st.caption("Concept phase")

    # ══════════════════════════════════════════════════════════════
    # FOOTER
    # ══════════════════════════════════════════════════════════════
    st.markdown("""
    <div class="matrix-footer">
        <p><strong>🚉 PAN HANDLER TRANSIT HUB</strong></p>
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
