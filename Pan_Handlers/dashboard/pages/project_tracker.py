"""
PROJECT TRACKER PAGE — Flagship Project Monitoring

Track progress, milestones, and health of all flagship projects
in the Pan Handlers federation.
"""

import streamlit as st
from config import PATHS, SETTINGS
from utils import (
    page_divider, section_header, get_status_badge, project_card,
    get_track_color, get_project_stats
)


def render():
    """Render the Project Tracker page."""
    projects_data = st.session_state.get('projects_data', {})

    # Header
    st.markdown('<div class="dashboard-title">📋 Project Tracker</div>', unsafe_allow_html=True)
    st.markdown('<div class="dashboard-subtitle">Flagship Project Progress & Milestones</div>', unsafe_allow_html=True)

    page_divider()

    if not projects_data or 'flagship_projects' not in projects_data:
        st.warning("No project data found. Check projects.json file.")
        return

    projects = projects_data['flagship_projects']
    stats = get_project_stats(projects_data)

    # === QUICK STATS ===
    col1, col2, col3, col4, col5 = st.columns(5)

    with col1:
        st.metric("Total Projects", stats.get('total', 0))
    with col2:
        st.metric("Active", stats.get('active', 0), delta="In Progress")
    with col3:
        st.metric("In Prep", stats.get('in_prep', 0))
    with col4:
        st.metric("Concept", stats.get('concept', 0))
    with col5:
        # Calculate completion rate (projects with milestones that are done)
        completion = sum(1 for p in projects if p.get('status') in ['Complete', 'Active']) / len(projects) * 100 if projects else 0
        st.metric("Progress Rate", f"{completion:.0f}%")

    page_divider()

    # === FILTER CONTROLS ===
    col1, col2 = st.columns([1, 2])

    with col1:
        status_filter = st.selectbox(
            "Filter by Status:",
            ["All", "In Preparation", "In Progress", "Active", "Concept", "Complete"]
        )

    with col2:
        track_filter = st.selectbox(
            "Filter by Track:",
            ["All"] + list(stats.get('by_track', {}).keys())
        )

    page_divider()

    # === PROJECT CARDS ===
    section_header("Flagship Projects", "🏆")

    # Filter projects
    filtered = projects
    if status_filter != "All":
        filtered = [p for p in filtered if p.get('status') == status_filter]
    if track_filter != "All":
        filtered = [p for p in filtered if p.get('track') == track_filter]

    if not filtered:
        st.info("No projects match the selected filters.")
    else:
        for project in filtered:
            track_color = get_track_color(project.get('track', ''))
            badge = get_status_badge(project.get('status', 'Concept'))

            with st.expander(f"{project.get('title', 'Untitled')} — {project.get('status', 'Unknown')}", expanded=False):
                col1, col2 = st.columns([2, 1])

                with col1:
                    st.markdown(f"""
                    <div style="padding: 0.5em;">
                        <h3 style="color: {track_color}; margin-top: 0;">
                            {project.get('title', 'Untitled')} {badge}
                        </h3>
                        <p style="color: #555; font-style: italic; font-size: 1.1em;">
                            "{project.get('tagline', '')}"
                        </p>
                        <p style="color: #444;"><strong>Track:</strong> {project.get('track', 'TBD')}</p>
                        <p style="color: #444;"><strong>Lead:</strong> {project.get('owner', 'TBD')}</p>
                        <p style="color: #444;"><strong>Current Phase:</strong> {project.get('current_phase', 'N/A')}</p>
                    </div>
                    """, unsafe_allow_html=True)

                    # Summary
                    st.markdown("**Summary:**")
                    st.markdown(project.get('summary', 'No summary available.'))

                    # Why it exists
                    if project.get('why_exists'):
                        st.markdown("**Why It Exists:**")
                        st.markdown(project.get('why_exists'))

                with col2:
                    # Milestones
                    st.markdown("""
                    <div style="background: rgba(0,0,0,0.2); border-radius: 8px; padding: 1em;">
                        <h5 style="color: #2a9d8f; margin-top: 0;">Milestones</h5>
                    """, unsafe_allow_html=True)

                    milestones = project.get('milestones', [])
                    if milestones:
                        for m in milestones[:6]:  # Show first 6
                            st.markdown(f"<p style='margin: 0.2em 0; font-size: 0.9em; color: #444;'>{m}</p>", unsafe_allow_html=True)
                        if len(milestones) > 6:
                            st.markdown(f"<p style='color: #888; font-size: 0.85em;'>+{len(milestones) - 6} more...</p>", unsafe_allow_html=True)
                    else:
                        st.markdown("<p style='color: #888; font-size: 0.9em;'>No milestones defined</p>", unsafe_allow_html=True)

                    st.markdown("</div>", unsafe_allow_html=True)

                    # Next Action
                    if project.get('next_action'):
                        st.markdown(f"""
                        <div style="background: rgba(244,162,97,0.1); border: 1px solid #f4a261;
                                    border-radius: 8px; padding: 0.8em; margin-top: 1em;">
                            <h5 style="color: #f4a261; margin: 0 0 0.5em 0;">⏭️ Next Action</h5>
                            <p style="color: #444; margin: 0; font-size: 0.9em;">{project.get('next_action')}</p>
                        </div>
                        """, unsafe_allow_html=True)

                # Nyquist Contribution
                contributions = project.get('nyquist_contribution', [])
                if contributions:
                    st.markdown("---")
                    st.markdown("**Nyquist Framework Contribution:**")
                    for c in contributions:
                        st.markdown(f"- {c}")

                # Vision
                if project.get('vision'):
                    st.markdown("---")
                    st.markdown(f"""
                    <div style="background: linear-gradient(135deg, rgba(155,89,182,0.1) 0%, rgba(52,152,219,0.05) 100%);
                                border-left: 4px solid #9b59b6; padding: 1em; border-radius: 0 8px 8px 0;">
                        <h5 style="color: #9b59b6; margin-top: 0;">🌟 Vision</h5>
                        <p style="color: #444; font-style: italic;">{project.get('vision')}</p>
                    </div>
                    """, unsafe_allow_html=True)

    page_divider()

    # === TRACK DISTRIBUTION ===
    section_header("By Track", "📊")

    track_counts = stats.get('by_track', {})
    if track_counts:
        cols = st.columns(len(track_counts))
        for i, (track, count) in enumerate(sorted(track_counts.items(), key=lambda x: -x[1])):
            with cols[i]:
                color = get_track_color(track)
                st.markdown(f"""
                <div style="background: rgba(0,0,0,0.2); border: 2px solid {color};
                            border-radius: 10px; padding: 1em; text-align: center;">
                    <div style="font-size: 2em; font-weight: bold; color: {color};">{count}</div>
                    <div style="color: #666; font-size: 0.85em;">{track}</div>
                </div>
                """, unsafe_allow_html=True)

    # Footer
    page_divider()
    meta = projects_data.get('meta', {})
    st.markdown(f"""
    <div style="text-align: center; color: #666; font-size: 0.9em; margin-top: 2em;">
        <p>Last updated: {meta.get('last_updated', 'Unknown')}</p>
        <p style="color: #00ff41; font-style: italic;">"{meta.get('philosophy', '')}"</p>
    </div>
    """, unsafe_allow_html=True)
