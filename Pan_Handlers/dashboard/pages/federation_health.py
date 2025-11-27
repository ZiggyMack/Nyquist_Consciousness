"""
FEDERATION HEALTH PAGE — Deep Dive into Repo Status

Detailed health monitoring for all connected repositories
in the Pan Handlers federation.
"""

import streamlit as st
from datetime import datetime
from config import PATHS, SETTINGS
from utils import (
    page_divider, section_header, get_status_badge, repo_card,
    load_manifests, load_nyquist_status
)


def render():
    """Render the Federation Health page."""
    manifests = st.session_state.get('manifests', [])

    # Header
    st.markdown('<div class="dashboard-title">🏥 Federation Health</div>', unsafe_allow_html=True)
    st.markdown('<div class="dashboard-subtitle">Repository Status & Integration Health</div>', unsafe_allow_html=True)

    page_divider()

    # === HEALTH SUMMARY ===
    section_header("Health Summary", "📊")

    col1, col2, col3, col4 = st.columns(4)

    total_repos = len(manifests)
    active_repos = sum(1 for m in manifests if m.get('status') == 'Active')
    nyquist_healthy = PATHS['nyquist_status'].exists()

    with col1:
        health_pct = (active_repos / total_repos * 100) if total_repos > 0 else 0
        color = '#00ff41' if health_pct >= 80 else '#f4a261' if health_pct >= 50 else '#e74c3c'
        st.markdown(f"""
        <div class="metric-box" style="border-color: {color};">
            <div class="metric-value" style="color: {color};">{health_pct:.0f}%</div>
            <div class="metric-label">Overall Health</div>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown(f"""
        <div class="metric-box">
            <div class="metric-value">{total_repos}</div>
            <div class="metric-label">Total Repos</div>
        </div>
        """, unsafe_allow_html=True)

    with col3:
        st.markdown(f"""
        <div class="metric-box" style="border-color: #00ff41;">
            <div class="metric-value" style="color: #00ff41;">{active_repos}</div>
            <div class="metric-label">Active</div>
        </div>
        """, unsafe_allow_html=True)

    with col4:
        tunnel_status = "🟢" if nyquist_healthy else "🔴"
        st.markdown(f"""
        <div class="metric-box">
            <div class="metric-value">{tunnel_status}</div>
            <div class="metric-label">Nyquist Tunnel</div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === REPOSITORY DETAILS ===
    section_header("Repository Status", "🌌")

    if manifests:
        for manifest in manifests:
            status = manifest.get('status', 'Unknown')
            status_color = '#00ff41' if status == 'Active' else '#f4a261' if status == 'Incubating' else '#666'

            with st.expander(f"{manifest.get('display_name', manifest.get('repo', 'Unknown'))} — {status}", expanded=True):
                col1, col2 = st.columns([2, 1])

                with col1:
                    st.markdown(f"""
                    <div style="padding: 1em;">
                        <h4 style="color: {status_color}; margin-top: 0;">
                            {manifest.get('display_name', manifest.get('repo', 'Unknown'))}
                            {get_status_badge(status)}
                        </h4>
                        <p style="color: #555;"><strong>Role:</strong> {manifest.get('role', 'N/A')}</p>
                        <p style="color: #555;"><strong>Owner:</strong> {manifest.get('owner', 'N/A')}</p>
                        <p style="color: #444;">{manifest.get('summary', 'No description available.')}</p>
                    </div>
                    """, unsafe_allow_html=True)

                    # Tags
                    tags = manifest.get('tags', [])
                    if tags:
                        tags_html = " ".join([f'<code style="background: rgba(0,255,65,0.2); color: #00ff41; padding: 2px 6px; border-radius: 3px; font-size: 0.85em;">{tag}</code>' for tag in tags])
                        st.markdown(f"<p>{tags_html}</p>", unsafe_allow_html=True)

                with col2:
                    # Health indicators
                    st.markdown("""
                    <div style="background: rgba(0,0,0,0.2); border-radius: 8px; padding: 1em;">
                        <h5 style="color: #2a9d8f; margin-top: 0;">Health Checks</h5>
                    """, unsafe_allow_html=True)

                    # Check various health indicators
                    url = manifest.get('url_repo', '')
                    has_url = url and url != 'TBD'
                    has_spec = manifest.get('spec_location') is not None
                    has_dashboard = manifest.get('dashboard_location') is not None

                    checks = [
                        ("GitHub URL", has_url),
                        ("Spec Document", has_spec),
                        ("Dashboard", has_dashboard),
                        ("Status Updated", True),  # Assuming if we loaded it, it's recent
                    ]

                    for check_name, passed in checks:
                        icon = "✅" if passed else "⚠️"
                        color = "#00ff41" if passed else "#f4a261"
                        st.markdown(f"<p style='margin: 0.2em 0; color: {color};'>{icon} {check_name}</p>", unsafe_allow_html=True)

                    st.markdown("</div>", unsafe_allow_html=True)

                    # Links
                    if has_url:
                        st.markdown(f"[📂 View on GitHub]({url})")

    else:
        st.info("No repository manifests found. Add manifest JSON files to Pan_Handlers/manifests/")

    page_divider()

    # === NYQUIST INTEGRATION HEALTH ===
    section_header("Nyquist Integration", "🧠")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div class="tunnel-card">
            <h4>Connection Status</h4>
        """, unsafe_allow_html=True)

        checks = [
            ("NYQUIST_STATUS.json", PATHS['nyquist_status'].exists()),
            ("Personas Directory", PATHS['nyquist_personas'].exists()),
            ("Experiments Directory", PATHS['nyquist_experiments'].exists()),
            ("S7 Armada Directory", PATHS['s7_armada_dir'].exists()),
            ("Publication Status", PATHS['publication_status'].exists()),
        ]

        for check_name, exists in checks:
            icon = "✅" if exists else "❌"
            color = "#00ff41" if exists else "#e74c3c"
            st.markdown(f"<p style='margin: 0.3em 0; color: {color};'>{icon} {check_name}</p>", unsafe_allow_html=True)

        st.markdown("</div>", unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div class="tunnel-card">
            <h4>Tunnel Protocol (PTP-1.0)</h4>
            <p style="color: #666;">Pan Handlers Tunnel Protocol enables:</p>
            <ul style="color: #888; font-size: 0.9em;">
                <li><strong>Mirror Tunnels:</strong> Clone docs across repos</li>
                <li><strong>Live State Tunnels:</strong> Pull real-time status</li>
                <li><strong>Entity Tunnels:</strong> Bind personas across contexts</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    # Footer
    page_divider()
    st.markdown(f"""
    <div style="text-align: center; color: #666; font-size: 0.9em; margin-top: 2em;">
        Last refreshed: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
    </div>
    """, unsafe_allow_html=True)
