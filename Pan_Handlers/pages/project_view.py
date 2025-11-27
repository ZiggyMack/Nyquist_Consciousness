"""
Project View - Detailed view of a single repository
Shows repo summary, pillars, and all projects.
"""

import streamlit as st


def get_status_badge(status):
    """Return HTML for status badge."""
    badges = {
        "Active": '<span class="status-badge badge-active">ACTIVE</span>',
        "Complete": '<span class="status-badge badge-complete">COMPLETE</span>',
        "Incubating": '<span class="status-badge badge-incubating">INCUBATING</span>',
        "In Progress": '<span class="status-badge badge-active">IN PROGRESS</span>',
        "Ready to Run": '<span class="status-badge badge-active">READY</span>',
        "Planned": '<span class="status-badge badge-incubating">PLANNED</span>',
    }
    return badges.get(status, f'<span class="status-badge">{status}</span>')


def render():
    """Render the Project View page."""
    manifests = st.session_state.get('manifests', [])

    st.markdown('<div class="pan-title">🔍 Project View</div>', unsafe_allow_html=True)
    st.markdown('<div class="pan-subtitle">Explore a Repository in Detail</div>', unsafe_allow_html=True)

    if not manifests:
        st.warning("No repositories loaded. Add manifests to Pan_Handlers/manifests/")
        return

    # Repository selector
    repo_names = [m.get('display_name', m.get('repo', 'Unknown')) for m in manifests]
    selected_name = st.selectbox("Select Repository:", repo_names)

    # Find selected manifest
    selected_manifest = next((m for m in manifests if m.get('display_name', m.get('repo')) == selected_name), None)

    if not selected_manifest:
        st.error("Repository not found")
        return

    st.markdown("---")

    # ========================================
    # REPOSITORY OVERVIEW
    # ========================================
    col1, col2 = st.columns([2, 1])

    with col1:
        badge = get_status_badge(selected_manifest.get('status', 'Unknown'))
        st.markdown(f"## {selected_manifest.get('display_name', 'Unknown')} {badge}", unsafe_allow_html=True)
        st.markdown(f"**Role:** {selected_manifest.get('role', 'N/A')}")
        st.markdown(f"**Owner:** {selected_manifest.get('owner', 'N/A')}")
        st.markdown(f"**Last Updated:** {selected_manifest.get('last_updated', 'N/A')}")

        st.markdown("---")

        st.markdown("### Summary")
        st.markdown(selected_manifest.get('summary', 'No description available.'))

        # Tags
        tags = selected_manifest.get('tags', [])
        if tags:
            st.markdown("**Tags:** " + " ".join([f"`{tag}`" for tag in tags]))

    with col2:
        st.markdown("### Links")

        url_repo = selected_manifest.get('url_repo', '')
        url_dashboard = selected_manifest.get('url_dashboard', '')

        if url_repo and url_repo != 'TBD':
            st.markdown(f"📂 [GitHub Repository]({url_repo})")

        if url_dashboard and url_dashboard != 'TBD':
            st.markdown(f"📊 [Dashboard]({url_dashboard})")

        # Contact
        contact = selected_manifest.get('contact', {})
        if contact:
            st.markdown("### Contact")
            st.markdown(f"**Primary:** {contact.get('primary', 'N/A')}")

    st.markdown("---")

    # ========================================
    # PILLARS
    # ========================================
    pillars = selected_manifest.get('pillars', {})
    if pillars:
        st.markdown('<div class="section-header">🏛️ Pillars</div>', unsafe_allow_html=True)

        col1, col2, col3 = st.columns(3)

        with col1:
            st.markdown("**Purpose**")
            st.info(pillars.get('purpose', 'N/A'))

        with col2:
            st.markdown("**Methods**")
            st.info(pillars.get('methods', 'N/A'))

        with col3:
            st.markdown("**Outputs**")
            st.info(pillars.get('outputs', 'N/A'))

        st.markdown("---")

    # ========================================
    # PROJECTS
    # ========================================
    projects = selected_manifest.get('projects', [])

    if projects:
        st.markdown('<div class="section-header">📋 Projects</div>', unsafe_allow_html=True)

        for project in projects:
            with st.expander(f"**{project.get('title', 'Untitled')}** — {project.get('type', 'Project')}", expanded=False):
                col1, col2 = st.columns([2, 1])

                with col1:
                    st.markdown(f"**Summary:** {project.get('summary', 'No description.')}")

                    links = project.get('links', {})
                    if any(links.values()):
                        st.markdown("**Links:**")
                        if links.get('docs'):
                            st.markdown(f"- 📄 Docs: `{links['docs']}`")
                        if links.get('paper'):
                            st.markdown(f"- 📝 Paper: `{links['paper']}`")
                        if links.get('dashboard'):
                            st.markdown(f"- 📊 Dashboard: `{links['dashboard']}`")

                with col2:
                    st.markdown("**Status**")
                    st.markdown(get_status_badge(project.get('status', 'Unknown')), unsafe_allow_html=True)

                    st.markdown("**Type**")
                    st.markdown(f"`{project.get('type', 'N/A')}`")
    else:
        st.info("No projects defined in this repository's manifest.")
