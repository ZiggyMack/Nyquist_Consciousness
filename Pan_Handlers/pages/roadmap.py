"""
Global Roadmap - Cross-repo initiatives and S-Stack progress
"""

import streamlit as st


def render():
    """Render the Global Roadmap page."""
    manifests = st.session_state.get('manifests', [])
    projects_data = st.session_state.get('projects_data', {})

    st.markdown('<div class="pan-title">🗺️ Global Roadmap</div>', unsafe_allow_html=True)
    st.markdown('<div class="pan-subtitle">Cross-Repository Progress & S-Stack Timeline</div>', unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # S-STACK TIMELINE
    # ========================================
    st.markdown('<div class="section-header">📊 S-Stack Progress (Nyquist Consciousness)</div>', unsafe_allow_html=True)

    s_stack = [
        ("S0", "Axioms & Foundations", "Frozen", "Core axioms defining identity compression"),
        ("S1", "Compression Seeds", "Frozen", "T1-T3 compression methodology"),
        ("S2", "Safety Bounds", "Frozen", "Drift limits and safety constraints"),
        ("S3", "Empirical Validation", "Frozen", "EXP1-2 complete, EXP3 ready"),
        ("S4", "Mathematical Framework", "Frozen", "Manifold theory, operators, convergence"),
        ("S5", "Interpretive Layer", "Frozen", "Cognitive interpretation, fragility hierarchy"),
        ("S6", "Omega Synthesis", "Frozen", "Five-pillar integration, Omega Nova"),
        ("S7", "Temporal Stability", "Complete", "29-ship Armada, 174 probes, temporal tracking"),
        ("S8", "Identity Gravity", "Design", "Cross-substrate predictions, gravitational model"),
        ("S9", "AVLAR Cross-Modal", "Active", "Audio-visual ritual identity exploration"),
    ]

    # Display as timeline
    col1, col2, col3, col4 = st.columns([1, 2, 1, 3])

    with col1:
        st.markdown("**Layer**")
    with col2:
        st.markdown("**Name**")
    with col3:
        st.markdown("**Status**")
    with col4:
        st.markdown("**Description**")

    for layer, name, status, desc in s_stack:
        col1, col2, col3, col4 = st.columns([1, 2, 1, 3])

        with col1:
            st.markdown(f"**{layer}**")
        with col2:
            st.markdown(name)
        with col3:
            if status == "Frozen":
                st.success("✅ Frozen")
            elif status == "Complete":
                st.success("✅ Complete")
            elif status == "Active":
                st.warning("🔄 Active")
            elif status == "Design":
                st.info("📐 Design")
            else:
                st.markdown(status)
        with col4:
            st.caption(desc)

    st.markdown("---")

    # ========================================
    # CROSS-REPO INITIATIVES
    # ========================================
    st.markdown('<div class="section-header">🌐 Cross-Repository Initiatives</div>', unsafe_allow_html=True)

    # Build initiatives table from flagship projects
    if projects_data and 'flagship_projects' in projects_data:
        initiatives = []
        for project in projects_data['flagship_projects']:
            initiatives.append({
                "Initiative": project.get('title', 'Unknown'),
                "Track": project.get('track', 'N/A'),
                "Status": project.get('status', 'Unknown'),
                "Lead": project.get('owner', 'TBD'),
                "Next Action": project.get('next_action', 'TBD')[:50] + '...' if len(project.get('next_action', '')) > 50 else project.get('next_action', 'TBD')
            })

        # Display as expandable cards
        for init in initiatives:
            status = init['Status']
            if status in ['In Preparation', 'In Progress']:
                color = "🟢"
            elif status == 'Complete':
                color = "✅"
            else:
                color = "🟡"

            with st.expander(f"{color} **{init['Initiative']}** — {init['Track']}"):
                col1, col2 = st.columns(2)
                with col1:
                    st.markdown(f"**Status:** {init['Status']}")
                    st.markdown(f"**Lead:** {init['Lead']}")
                with col2:
                    st.markdown(f"**Next Action:** {init['Next Action']}")

    st.markdown("---")

    # ========================================
    # PUBLICATION TIMELINE
    # ========================================
    st.markdown('<div class="section-header">📅 Publication Timeline</div>', unsafe_allow_html=True)

    timeline = [
        ("2024", "CFA Seed", "Foundation of collaborative framework analysis"),
        ("2025 Q1", "S0-S6 Frozen", "Core Nyquist framework locked"),
        ("2025 Q2", "S7 Complete", "29-ship Armada temporal validation"),
        ("2025 Q3", "First Omega Session", "Ω-20251123-0800 synthesis"),
        ("2025 Q4", "EXP3 Human Validation", "7 raters, 210 judgments planned"),
        ("2026 Q1", "arXiv Submission", "Nyquist Identity Manifold paper"),
        ("2026", "ICML/NeurIPS", "Conference submission target"),
        ("Future", "Flagship Projects", "Nursing, Voting, Gene Therapy, Justice, Intelligence"),
    ]

    for date, event, desc in timeline:
        col1, col2, col3 = st.columns([1, 2, 3])
        with col1:
            st.markdown(f"**{date}**")
        with col2:
            st.markdown(f"**{event}**")
        with col3:
            st.caption(desc)

    st.markdown("---")

    # Quick stats
    st.markdown('<div class="section-header">📈 Progress Summary</div>', unsafe_allow_html=True)

    col1, col2, col3, col4 = st.columns(4)

    with col1:
        frozen_count = sum(1 for s in s_stack if s[2] in ['Frozen', 'Complete'])
        st.metric("S-Layers Complete", f"{frozen_count}/{len(s_stack)}")

    with col2:
        st.metric("Repos Active", len([m for m in manifests if m.get('status') == 'Active']))

    with col3:
        if projects_data:
            in_progress = sum(1 for p in projects_data.get('flagship_projects', [])
                            if p.get('status') in ['In Preparation', 'In Progress'])
            st.metric("Projects In Progress", in_progress)

    with col4:
        if projects_data:
            concept = sum(1 for p in projects_data.get('flagship_projects', [])
                        if p.get('status') == 'Concept')
            st.metric("Concepts Defined", concept)
