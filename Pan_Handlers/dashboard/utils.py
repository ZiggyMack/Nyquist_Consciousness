"""
PAN HANDLERS DASHBOARD — SHARED UTILITIES

Shared functions used across multiple dashboard pages.
"""

import json
import streamlit as st
from pathlib import Path
from config import PATHS, SETTINGS

# Unpack paths
PAN_HANDLERS_ROOT = PATHS['pan_handlers_root']
REPO_ROOT = PATHS['repo_root']

# ========== DATA LOADERS ==========

@st.cache_data(ttl=60)
def load_projects():
    """Load flagship projects from projects.json."""
    projects_file = PATHS['projects_file']
    if projects_file.exists():
        with open(projects_file, "r", encoding="utf-8") as f:
            return json.load(f)
    else:
        st.warning(f"projects.json not found at: {projects_file}")
    return {}


@st.cache_data(ttl=60)
def load_manifests():
    """Load all manifests from manifests/ directory."""
    manifests = []
    manifests_dir = PATHS['manifests_dir']
    if manifests_dir.exists():
        for manifest_file in manifests_dir.glob("*.json"):
            try:
                with open(manifest_file, 'r', encoding='utf-8') as f:
                    manifests.append(json.load(f))
            except Exception as e:
                st.warning(f"Failed to load {manifest_file.name}: {e}")
    return manifests


@st.cache_data(ttl=60)
def load_nyquist_status():
    """Load Nyquist Consciousness status for Matrix integration."""
    status_file = PATHS['nyquist_status']
    if status_file.exists():
        with open(status_file, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


@st.cache_data(ttl=60)
def load_publication_status():
    """Load publication status from Nyquist."""
    pub_file = PATHS['publication_status']
    if pub_file.exists():
        with open(pub_file, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


@st.cache_data
def load_markdown_file(file_path):
    """Load and return markdown file contents."""
    try:
        return Path(file_path).read_text(encoding="utf-8")
    except Exception as e:
        return f"_Error loading file: {e}_"


# ========== STATUS HELPERS ==========

def get_status_badge(status):
    """Return HTML for status badge."""
    colors = SETTINGS['colors']
    badges = {
        "Active": f'<span class="status-badge" style="background: rgba(0,255,65,0.2); color: {colors["active"]}; border: 1px solid {colors["active"]};">ACTIVE</span>',
        "Complete": f'<span class="status-badge" style="background: rgba(42,157,143,0.2); color: {colors["complete"]}; border: 1px solid {colors["complete"]};">COMPLETE</span>',
        "Incubating": f'<span class="status-badge" style="background: rgba(255,215,0,0.2); color: #b8860b; border: 1px solid {colors["incubating"]};">INCUBATING</span>',
        "Concept": f'<span class="status-badge" style="background: rgba(244,162,97,0.2); color: {colors["concept"]}; border: 1px solid {colors["concept"]};">CONCEPT</span>',
        "Archived": f'<span class="status-badge" style="background: rgba(102,102,102,0.2); color: {colors["archived"]}; border: 1px solid {colors["archived"]};">ARCHIVED</span>',
        "In Progress": f'<span class="status-badge" style="background: rgba(0,255,65,0.2); color: {colors["active"]}; border: 1px solid {colors["active"]};">IN PROGRESS</span>',
        "In Preparation": f'<span class="status-badge" style="background: rgba(244,162,97,0.2); color: {colors["concept"]}; border: 1px solid {colors["concept"]};">IN PREP</span>',
    }
    return badges.get(status, f'<span class="status-badge">{status}</span>')


def get_track_color(track):
    """Get color for project track."""
    track_colors = {
        'Research / Theory': '#9b59b6',
        'Education / Healthcare': '#3498db',
        'Governance / Democracy': '#e74c3c',
        'Intelligence / Governance': '#2a9d8f',
        'Biomedical Research': '#27ae60',
        'Justice / Social Systems': '#f4a261',
    }
    return track_colors.get(track, '#666666')


# ========== UI COMPONENTS ==========

def page_divider():
    """Visual page divider with Pan Handlers styling."""
    st.markdown("""
    <div style="border-top: 2px solid #00ff41; margin: 1.5em 0; opacity: 0.5;"></div>
    """, unsafe_allow_html=True)


def section_header(title, emoji=""):
    """Render a styled section header."""
    st.markdown(f"""
    <div style="color: #00ff41; font-size: 1.4em; font-weight: bold;
                margin-top: 1.5em; margin-bottom: 0.8em;
                font-family: 'Georgia', serif;
                border-bottom: 2px solid #00ff41;
                padding-bottom: 0.3em;">
        {emoji} {title}
    </div>
    """, unsafe_allow_html=True)


def project_card(project, compact=False):
    """Render a project card."""
    badge = get_status_badge(project.get('status', 'Concept'))
    track_color = get_track_color(project.get('track', ''))

    if compact:
        st.markdown(f"""
        <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.05) 100%);
                    border: 2px solid {track_color}; border-radius: 10px;
                    padding: 1em; margin-bottom: 0.8em;">
            <h4 style="color: {track_color}; margin: 0 0 0.3em 0;">
                {project.get('title', 'Untitled')[:28]}{'...' if len(project.get('title', '')) > 28 else ''} {badge}
            </h4>
            <p style="color: #555; font-style: italic; font-size: 0.9em; margin: 0;">
                {project.get('tagline', '')[:55]}{'...' if len(project.get('tagline', '')) > 55 else ''}
            </p>
            <p style="color: #888; font-size: 0.85em; margin: 0.3em 0 0 0;">
                <strong>{project.get('track', 'TBD')}</strong>
            </p>
        </div>
        """, unsafe_allow_html=True)
    else:
        st.markdown(f"""
        <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.05) 100%);
                    border: 2px solid {track_color}; border-radius: 10px;
                    padding: 1.2em; margin-bottom: 0.8em;
                    box-shadow: 0 0 15px rgba(42,157,143,0.15);">
            <h4 style="color: {track_color}; margin-top: 0; margin-bottom: 0.5em;">
                {project.get('title', 'Untitled')} {badge}
            </h4>
            <p style="color: #555; font-style: italic;">{project.get('tagline', '')}</p>
            <p style="color: #444;"><strong>Track:</strong> {project.get('track', 'TBD')}</p>
            <p style="color: #444;"><strong>Lead:</strong> {project.get('owner', 'TBD')}</p>
        </div>
        """, unsafe_allow_html=True)


def repo_card(manifest):
    """Render a repository card."""
    badge = get_status_badge(manifest.get('status', 'Unknown'))
    tags_html = " ".join([f'<code style="background: rgba(0,255,65,0.2); color: #00ff41; padding: 2px 6px; border-radius: 3px; font-size: 0.8em;">{tag}</code>' for tag in manifest.get('tags', [])[:4]])

    st.markdown(f"""
    <div style="background: linear-gradient(135deg, rgba(0,255,65,0.08) 0%, rgba(0,204,51,0.03) 100%);
                border: 2px solid #00ff41; border-radius: 12px;
                padding: 1.5em; margin-bottom: 1em;
                box-shadow: 0 0 20px rgba(0,255,65,0.2);">
        <h3 style="color: #00ff41; margin-top: 0; font-family: 'Georgia', serif;">
            {manifest.get('display_name', manifest.get('repo', 'Unknown'))} {badge}
        </h3>
        <p style="color: #444;"><strong>Role:</strong> {manifest.get('role', 'N/A')}</p>
        <p style="color: #444;"><strong>Owner:</strong> {manifest.get('owner', 'N/A')}</p>
        <p style="color: #555;">{manifest.get('summary', 'No description.')[:150]}{'...' if len(manifest.get('summary', '')) > 150 else ''}</p>
        <p>{tags_html}</p>
    </div>
    """, unsafe_allow_html=True)


# ========== STATISTICS ==========

def get_project_stats(projects_data):
    """Calculate statistics from projects data."""
    if not projects_data:
        return {}

    projects = projects_data.get('flagship_projects', [])
    stats = {
        'total': len(projects),
        'active': sum(1 for p in projects if p.get('status') in ['Active', 'In Progress']),
        'in_prep': sum(1 for p in projects if p.get('status') == 'In Preparation'),
        'concept': sum(1 for p in projects if p.get('status') == 'Concept'),
        'by_track': {},
    }

    for p in projects:
        track = p.get('track', 'Unknown')
        stats['by_track'][track] = stats['by_track'].get(track, 0) + 1

    return stats


def get_nyquist_integration_stats():
    """Get stats about Nyquist integration for Matrix page."""
    stats = {}

    # Check if Nyquist paths exist
    stats['nyquist_connected'] = PATHS['nyquist_status'].exists()

    # Get S7 Armada stats if available
    s7_dir = PATHS['s7_armada_dir']
    if s7_dir.exists():
        armada_results = list(s7_dir.glob("armada_results/*.json"))
        stats['armada_runs'] = len(armada_results)
    else:
        stats['armada_runs'] = 0

    # Publication status
    pub_status = load_publication_status()
    if pub_status:
        pubs = pub_status.get('publications', {})
        stats['workshop_ready'] = pubs.get('workshop', {}).get('completion', 0)
        stats['arxiv_progress'] = pubs.get('arxiv', {}).get('completion', 0)
    else:
        stats['workshop_ready'] = 0
        stats['arxiv_progress'] = 0

    return stats
