"""
Hall of Pan Handlers - Main Gallery
Shows all participating repos as "rooms" in the hall.
"""

import streamlit as st


def get_status_badge(status):
    """Return HTML for status badge."""
    badges = {
        "Active": '<span class="status-badge badge-active">ACTIVE</span>',
        "Complete": '<span class="status-badge badge-complete">COMPLETE</span>',
        "Incubating": '<span class="status-badge badge-incubating">INCUBATING</span>',
        "Archived": '<span class="status-badge badge-archived">ARCHIVED</span>',
        "In Progress": '<span class="status-badge badge-active">IN PROGRESS</span>',
        "In Preparation": '<span class="status-badge badge-active">IN PREP</span>',
        "Concept": '<span class="status-badge badge-incubating">CONCEPT</span>',
    }
    return badges.get(status, f'<span class="status-badge">{status}</span>')


def render():
    """Render the Hall of Pan Handlers."""
    manifests = st.session_state.get('manifests', [])
    projects_data = st.session_state.get('projects_data', {})

    # Header
    st.markdown('<div class="pan-title">🍳 Pan Handlers</div>', unsafe_allow_html=True)
    st.markdown('<div class="pan-subtitle">The Halls of Our Shared Work — A Federation of Human-AI Collaboration</div>', unsafe_allow_html=True)

    # Philosophy banner
    philosophy = "FUCK IT, WE'LL DO IT LIVE! — Building better systems without waiting for institutions."
    if projects_data and 'meta' in projects_data:
        philosophy = projects_data['meta'].get('philosophy', philosophy)

    st.markdown(f'<div class="philosophy-banner">{philosophy}</div>', unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # CONNECTED REPOSITORIES
    # ========================================
    st.markdown('<div class="section-header">🌌 Connected Repositories</div>', unsafe_allow_html=True)

    if manifests:
        cols = st.columns(len(manifests))
        for i, manifest in enumerate(manifests):
            with cols[i]:
                badge = get_status_badge(manifest.get('status', 'Unknown'))
                tags_html = " ".join([f'<code>{tag}</code>' for tag in manifest.get('tags', [])[:4]])

                st.markdown(f"""
                <div class="repo-card">
                    <h3>{manifest.get('display_name', manifest.get('repo', 'Unknown'))} {badge}</h3>
                    <p><strong>Role:</strong> {manifest.get('role', 'N/A')}</p>
                    <p><strong>Owner:</strong> {manifest.get('owner', 'N/A')}</p>
                    <p>{manifest.get('summary', 'No description.')[:150]}{'...' if len(manifest.get('summary', '')) > 150 else ''}</p>
                    <p>{tags_html}</p>
                </div>
                """, unsafe_allow_html=True)

                col1, col2 = st.columns(2)
                with col1:
                    if st.button(f"🔍 Details", key=f"details_{manifest.get('repo')}"):
                        st.session_state['selected_repo'] = manifest.get('repo')
                        st.info("Navigate to 'Project View' in sidebar to see details")
                with col2:
                    url = manifest.get('url_repo', '')
                    if url and url != 'TBD':
                        st.markdown(f"[📂 GitHub]({url})")
    else:
        st.info("No repository manifests loaded. Add manifests to Pan_Handlers/manifests/")

    st.markdown("---")

    # ========================================
    # FLAGSHIP PROJECTS GALLERY
    # ========================================
    st.markdown('<div class="section-header">🏆 Flagship Projects</div>', unsafe_allow_html=True)

    if projects_data and 'flagship_projects' in projects_data:
        projects = projects_data['flagship_projects']

        # First row: Top 3 projects
        col1, col2, col3 = st.columns(3)
        for i, project in enumerate(projects[:3]):
            with [col1, col2, col3][i]:
                badge = get_status_badge(project.get('status', 'Concept'))
                st.markdown(f"""
                <div class="project-card">
                    <h4>{project.get('title', 'Untitled')[:35]}{'...' if len(project.get('title', '')) > 35 else ''} {badge}</h4>
                    <p><em>{project.get('tagline', '')[:70]}{'...' if len(project.get('tagline', '')) > 70 else ''}</em></p>
                    <p><strong>Track:</strong> {project.get('track', 'TBD')}</p>
                    <p><strong>Lead:</strong> {project.get('owner', 'TBD')}</p>
                </div>
                """, unsafe_allow_html=True)

        # Second row: Remaining projects
        if len(projects) > 3:
            remaining = projects[3:7]
            cols = st.columns(len(remaining))
            for i, project in enumerate(remaining):
                with cols[i]:
                    badge = get_status_badge(project.get('status', 'Concept'))
                    st.markdown(f"""
                    <div class="project-card">
                        <h4>{project.get('title', 'Untitled')[:28]}{'...' if len(project.get('title', '')) > 28 else ''} {badge}</h4>
                        <p><em>{project.get('tagline', '')[:55]}{'...' if len(project.get('tagline', '')) > 55 else ''}</em></p>
                        <p><strong>{project.get('track', 'TBD')}</strong></p>
                    </div>
                    """, unsafe_allow_html=True)
    else:
        st.info("No flagship projects loaded from projects.json")

    st.markdown("---")

    # ========================================
    # QUICK STATS
    # ========================================
    st.markdown('<div class="section-header">🦅 Bird\'s Eye View</div>', unsafe_allow_html=True)

    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric("Repos Connected", len(manifests))

    with col2:
        if projects_data:
            st.metric("Flagship Projects", len(projects_data.get('flagship_projects', [])))
        else:
            st.metric("Flagship Projects", 0)

    with col3:
        active_count = sum(1 for m in manifests if m.get('status') == 'Active')
        st.metric("Active Repos", active_count)

    with col4:
        if projects_data:
            in_progress = sum(1 for p in projects_data.get('flagship_projects', [])
                            if p.get('status') in ['In Preparation', 'In Progress'])
            st.metric("In Progress", in_progress)
        else:
            st.metric("In Progress", 0)

    # Footer
    st.markdown("---")
    st.markdown("""
    <div class="footer-text">
        <p><strong>🍳 PAN HANDLERS</strong></p>
        <p>"These are the things we built together that neither could have done alone."</p>
    </div>
    """, unsafe_allow_html=True)
