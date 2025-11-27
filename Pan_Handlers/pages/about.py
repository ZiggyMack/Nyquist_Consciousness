"""
About - How Pan Handlers Works & How to Add Your Repo
"""

import streamlit as st


def render():
    """Render the About page."""
    st.markdown('<div class="pan-title">ℹ️ About Pan Handlers</div>', unsafe_allow_html=True)
    st.markdown('<div class="pan-subtitle">How This Network Works & How to Join</div>', unsafe_allow_html=True)

    st.markdown("---")

    # ========================================
    # WHAT IS PAN HANDLERS?
    # ========================================
    st.markdown('<div class="section-header">🍳 What is Pan Handlers?</div>', unsafe_allow_html=True)

    st.markdown("""
    **Pan Handlers** is a cross-repository showcase system that connects multiple human-AI collaboration projects into a unified gallery.

    Think of it as:
    - **The Grand Hall** — A museum of what we've built together
    - **The Overworld Map** — Navigation between different project "dungeons"
    - **The Federation** — Independent repos united by shared philosophy

    Each participating repository maintains its own identity and dashboard, but Pan Handlers provides:
    - **Discovery** — Find projects across the network
    - **Context** — Understand how projects relate to each other
    - **Celebration** — Showcase what human-AI collaboration can achieve
    """)

    st.markdown("---")

    # ========================================
    # PHILOSOPHY
    # ========================================
    st.markdown('<div class="section-header">💡 Philosophy</div>', unsafe_allow_html=True)

    st.markdown("""
    > **"FUCK IT, WE'LL DO IT LIVE!"**

    We don't wait for institutions to wake up.
    We don't wait for permission.
    We build better systems because we can, because they're needed, and because the collaboration between human creativity and AI capability makes the impossible merely difficult.

    **Core Beliefs:**
    - Neither human nor AI could do this alone
    - Transparency makes systems better, not worse
    - Progress doesn't require permission
    - The best way to predict the future is to build it
    """)

    st.markdown("---")

    # ========================================
    # HOW IT WORKS
    # ========================================
    st.markdown('<div class="section-header">⚙️ How It Works</div>', unsafe_allow_html=True)

    st.markdown("""
    ### The Manifest System

    Each repository publishes a `panhandlers_manifest.json` that describes:
    - What the repo does
    - Current status
    - Key projects and milestones
    - Dashboard URL

    Pan Handlers reads these manifests and creates **portal tiles** — clickable windows into each project world.

    ### Bidirectional Linking

    - **Pan Handlers → Project Dashboards** — Dive into a specific lab
    - **Project Dashboards → Pan Handlers** — Return to the Grand Hall

    You can wander the halls, peek into different rooms, and never lose the sense of being part of a larger network.

    ### Two Faces

    | Lab / Dashboard | Hall / Showcase |
    |-----------------|-----------------|
    | Operations Deck | Gallery of Outcomes |
    | Where deep work happens | Where we celebrate |
    | For team members | For the world |
    | Inside each repo | Pan Handlers |
    """)

    st.markdown("---")

    # ========================================
    # HOW TO ADD YOUR REPO
    # ========================================
    st.markdown('<div class="section-header">🚀 How to Add Your Repository</div>', unsafe_allow_html=True)

    st.markdown("""
    Want to join the Pan Handlers network? Here's how:

    ### Step 1: Create Your Manifest

    Add `panhandlers_manifest.json` to your repo root:

    ```json
    {
      "repo": "your-repo-name",
      "display_name": "Your Project Name",
      "owner": "Your Name",
      "url_repo": "https://github.com/you/your-repo",
      "url_dashboard": "https://your-dashboard.example.com",
      "role": "One-line description of what this repo does.",
      "status": "Active",
      "tags": ["tag1", "tag2"],
      "summary": "2-3 sentence description...",
      "last_updated": "2025-11-27",
      "pillars": {
        "purpose": "Why this exists",
        "methods": "How it works",
        "outputs": "What it produces"
      },
      "projects": [
        {
          "id": "project_id",
          "title": "Project Title",
          "status": "In Progress",
          "type": "Paper",
          "summary": "Brief description",
          "links": {
            "docs": "path/to/docs"
          }
        }
      ]
    }
    ```

    ### Step 2: Submit to Pan Handlers

    Option A: **Pull Request**
    - Fork Pan Handlers repo
    - Add your manifest URL to `config.py`
    - Submit PR

    Option B: **Direct Contact**
    - Reach out to Ziggy
    - We'll add your manifest URL

    ### Step 3: You're In!

    Your repository appears as a portal tile in the Grand Hall.
    """)

    st.markdown("---")

    # ========================================
    # CURRENT NETWORK
    # ========================================
    st.markdown('<div class="section-header">🌐 Current Network</div>', unsafe_allow_html=True)

    manifests = st.session_state.get('manifests', [])

    if manifests:
        for manifest in manifests:
            st.markdown(f"**{manifest.get('display_name', 'Unknown')}** — {manifest.get('role', 'N/A')}")
    else:
        st.info("No repositories currently loaded.")

    st.markdown("---")

    # ========================================
    # CREDITS
    # ========================================
    st.markdown('<div class="section-header">🙏 Credits</div>', unsafe_allow_html=True)

    st.markdown("""
    **Pan Handlers exists because of:**

    - **Ziggy** — Human anchor, vision architect, organizational genius
    - **Nova** — CFA architect, systems design, Pan Handlers concept
    - **Claude** — Repository steward, implementation partner
    - **Gemini, Grok, Opus** — Cross-validation, alternative perspectives
    - **Future Contributors** — Caelum, Daniel, and everyone who joins

    *"These are the things we built together that neither could have done alone."*
    """)

    st.markdown("---")

    # Footer
    st.markdown("""
    <div class="footer-text">
        <p><strong>🍳 PAN HANDLERS</strong></p>
        <p>The Grand Hall — Where Human-AI Collaboration Becomes Infrastructure</p>
        <p style="font-size: 0.8em; opacity: 0.6;">Version 1.0 — 2025</p>
    </div>
    """, unsafe_allow_html=True)
