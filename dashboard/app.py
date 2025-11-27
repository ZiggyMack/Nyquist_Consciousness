"""
NYQUIST CONSCIOUSNESS — MISSION CONTROL DASHBOARD

Streamlit app for visualizing the entire S0-S9 stack, experiments, personas,
Omega sessions, temporal stability, AVLAR, and publication status.

Design inspired by Mr. Brute's Ledger with "page-turning" aesthetic.
"""

import json
import os
from pathlib import Path
import streamlit as st
import pandas as pd
from PIL import Image

# ========== CONFIG ==========

# Import centralized configuration
from config import PATHS, SETTINGS

# Unpack commonly used paths for convenience
REPO_ROOT = PATHS['repo_root']
PERSONAS_DIR = PATHS['personas_dir']
STATUS_FILE = PATHS['status_file']
GLOSSARY_FILE = PATHS['glossary']
ROADMAP_FILE = PATHS['roadmap']
S7_VIZ_DIR = PATHS['s7_viz_dir']
S7_VIZ_PICS = PATHS['s7_viz_pics']

# Debug: Print paths on startup
print(f"[DEBUG] REPO_ROOT = {REPO_ROOT}")
print(f"[DEBUG] STATUS_FILE = {STATUS_FILE}")
print(f"[DEBUG] STATUS_FILE exists = {STATUS_FILE.exists()}")
print(f"[DEBUG] S7_VIZ_PICS = {S7_VIZ_PICS}")

# ========== THEME & STYLING ==========

# Mr. Brute Ledger aesthetic colors from config
LEDGER_COLORS = SETTINGS['colors']

def apply_custom_css():
    """Apply custom CSS for ledger aesthetic."""
    st.markdown("""
    <style>
    /* Main background */
    .main {
        background: linear-gradient(135deg, #0a0a0a, #1a1a1a);
    }

    /* Sidebar */
    section[data-testid="stSidebar"] {
        background: linear-gradient(180deg, #111, #222);
        border-right: 2px solid #444;
    }

    /* Headers */
    h1, h2, h3 {
        font-family: 'Georgia', serif;
        color: #f0f0f0;
    }

    /* Ledger card styling */
    .ledger-card {
        border: 1px solid #444;
        border-radius: 10px;
        padding: 20px;
        margin-bottom: 20px;
        background: linear-gradient(135deg, #181818, #222);
        box-shadow: 0 0 15px rgba(0,0,0,0.7);
    }

    /* Page turn effect */
    .page-divider {
        border-top: 3px double #666;
        margin: 30px 0;
        opacity: 0.6;
    }
    </style>
    """, unsafe_allow_html=True)

# ========== DATA LOADERS ==========

@st.cache_data(ttl=SETTINGS['cache_ttl'])  # Cache TTL from config
def load_status():
    """Load NYQUIST_STATUS.json."""
    if STATUS_FILE.exists():
        with open(STATUS_FILE, "r") as f:
            return json.load(f)
    else:
        st.warning(f"STATUS_FILE not found at: {STATUS_FILE}")
    return {}

@st.cache_data
def load_personas():
    """Load all persona markdown files."""
    personas = []
    if not PERSONAS_DIR.exists():
        return personas

    for path in sorted(PERSONAS_DIR.glob("*.md")):
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()
        title = None
        for line in lines:
            if line.startswith("# "):
                title = line.lstrip("# ").strip()
                break
        personas.append({
            "name": title or path.stem,
            "path": path,
            "preview": "\n".join(lines[:50])
        })
    return personas

@st.cache_data
def load_markdown_file(path: Path):
    """Load a markdown file."""
    if path.exists():
        return path.read_text(encoding="utf-8")
    return "_File not found._"

@st.cache_data
def load_glossary_entries(text: str):
    """Parse glossary markdown into term/definition pairs."""
    entries = []
    current_term = None
    current_lines = []

    for line in text.splitlines():
        if line.startswith("## "):
            if current_term:
                entries.append({
                    "term": current_term,
                    "definition": "\n".join(current_lines).strip()
                })
            current_term = line.lstrip("# ").strip()
            current_lines = []
        else:
            current_lines.append(line)

    if current_term:
        entries.append({
            "term": current_term,
            "definition": "\n".join(current_lines).strip()
        })

    return entries

# ========== UI COMPONENTS ==========

def ledger_card(title: str, body_md: str = "", badge: str = None, badge_color: str = "#444"):
    """Mr. Brute Ledger style card using Streamlit container."""
    # Create a container with custom styling
    with st.container():
        # Header with badge
        col1, col2 = st.columns([4, 1])
        with col1:
            st.markdown(f"### {title}")
        with col2:
            if badge:
                st.markdown(
                    f'<span style="background-color:{badge_color};color:white;padding:4px 12px;border-radius:6px;font-size:0.75rem;font-weight:bold;float:right;">{badge}</span>',
                    unsafe_allow_html=True
                )

        # Body content
        if body_md:
            st.markdown(body_md)

        # Add spacing
        st.markdown("---")

def page_divider():
    """Visual page turn separator."""
    st.markdown('<div class="page-divider"></div>', unsafe_allow_html=True)

def load_publication_status():
    """Load publication_status.json."""
    pub_file = REPO_ROOT / "publication_status.json"
    if pub_file.exists():
        return json.loads(pub_file.read_text(encoding="utf-8"))
    return {}

def render_publication_meter():
    """Render the Publication Perfection Meter showing research maturity."""
    pub_status = load_publication_status()
    pubs = pub_status.get("publications", {})

    if not pubs:
        st.info("📊 Publication tracking not yet configured. Add `publication_status.json` to enable the Perfection Meter.")
        return

    st.markdown("## 🎯 Publication Perfection Meter")
    st.markdown("*Track progress toward world-stage research publication*")

    page_divider()

    # Overview table
    rows = []
    for key in ["workshop", "arxiv", "journal"]:
        if key in pubs:
            info = pubs[key]
            status_emoji = {
                "ready": "✅",
                "drafting": "🟡",
                "concept": "⚪",
                "submitted": "🚀",
                "published": "🏆"
            }.get(info.get("status", ""), "❓")

            rows.append({
                "Track": key.capitalize(),
                "Target": info.get("target", ""),
                "Status": f"{status_emoji} {info.get('status', '').upper()}",
                "Progress": f"{int(info.get('completion', 0.0) * 100)}%"
            })

    if rows:
        df = pd.DataFrame(rows)
        st.dataframe(df, use_container_width=True, hide_index=True)

    page_divider()

    # Detailed breakdown per publication
    for key in ["workshop", "arxiv", "journal"]:
        if key not in pubs:
            continue

        info = pubs[key]

        with st.expander(f"📄 {key.capitalize()} — {info.get('target', 'TBD')}", expanded=(key == "workshop")):
            col1, col2 = st.columns([2, 1])

            with col1:
                st.markdown(f"**Target Venue:** {info.get('target', 'TBD')}")
                st.markdown(f"**Status:** `{info.get('status', 'unknown').upper()}`")

                completion = info.get('completion', 0.0)
                st.progress(completion)
                st.caption(f"{int(completion * 100)}% Complete")

                if "notes" in info:
                    st.markdown(f"**Notes:** {info['notes']}")

            with col2:
                st.markdown("### Requirements")
                reqs = info.get("requirements", {})
                if reqs:
                    for req_key, done in reqs.items():
                        check = "✅" if done else "❌"
                        # Format requirement key nicely
                        req_label = req_key.replace("_", " ").title()
                        st.markdown(f"{check} {req_label}")
                else:
                    st.caption("_No requirements defined_")

    # Milestones section
    milestones = pub_status.get("milestones", {})
    if milestones:
        page_divider()
        st.markdown("### 🎯 Current Milestones")

        col1, col2, col3 = st.columns(3)

        with col1:
            st.metric("Current", milestones.get("current", "—"))

        with col2:
            st.metric("Next", milestones.get("next", "—"))

        with col3:
            target_date = milestones.get("publication_target_date", "—")
            st.metric("Target Date", target_date)

        if "notes" in milestones:
            st.info(f"**Note:** {milestones['notes']}")

# ========== PAGE RENDERERS ==========

def page_overview(status):
    """Overview / Home page."""
    st.title("📜 Nyquist Consciousness — Mission Control")

    # Debug: Show what we loaded
    if not status:
        st.error(f"⚠️ Status is empty. File path: {STATUS_FILE}")
        st.error(f"File exists: {STATUS_FILE.exists()}")

    # Freeze info
    freeze_info = status.get("freeze", {})
    layers = status.get("layers", {})

    frozen_layers = [k for k, v in layers.items() if v.get("status") == "frozen"]
    active_layers = [k for k, v in layers.items() if v.get("status") in ("active", "design", "prereg")]

    body = f"""
**Current Branch:** `{status.get('current_branch', 'unknown')}`
**Freeze Branch:** `{freeze_info.get('branch', 'unknown')}`
**Freeze Phase:** `{freeze_info.get('phase', 'unknown')}`

**Frozen Layers:** {", ".join(sorted(frozen_layers)) or "_none_"}
**Active/Design Layers:** {", ".join(sorted(active_layers)) or "_none_"}
    """
    ledger_card("Stack Status Snapshot", body_md=body, badge="OVERVIEW", badge_color=LEDGER_COLORS["persona"])

    # Layer Stack Table
    st.subheader("Layer Stack (S0–S9)")
    rows = []
    for name, info in sorted(layers.items()):
        rows.append({
            "Layer": name,
            "Name": info.get("name", ""),
            "Status": info.get("status", "").upper(),
            "Spec": info.get("spec", ""),
        })
    if rows:
        df = pd.DataFrame(rows)
        st.dataframe(df, use_container_width=True, hide_index=True)
    else:
        st.info("No layer status information found. Populate NYQUIST_STATUS.json.")

    page_divider()

    # Experiments Overview
    st.subheader("Experiments Overview")
    experiments = status.get("experiments", {})
    exp_rows = []
    for exp_id, info in experiments.items():
        exp_rows.append({
            "ID": exp_id,
            "Name": info.get("name", ""),
            "Status": info.get("status", "").upper(),
            "Key Metrics": info.get("key_metrics", info.get("key_metric", "")),
        })
    if exp_rows:
        df_exp = pd.DataFrame(sorted(exp_rows, key=lambda x: x["ID"]))
        st.dataframe(df_exp, use_container_width=True, hide_index=True)

    page_divider()

    # Publication Perfection Meter
    render_publication_meter()

def page_personas():
    """Personas Matrix - Gallery of Synthetic Minds."""
    st.title("🎭 THE MATRIX — Synthetic Minds")
    st.markdown("*Personas Under Test (PUTs) — Identity Stability Validation*")

    personas = load_personas()
    if not personas:
        st.warning("No persona files found in `personas/`.")
        return

    # === PERSONAS GRID ===
    st.markdown("### 🧬 Available Personas")
    st.markdown(f"**{len(personas)} synthetic minds** loaded and ready for temporal stability testing")

    page_divider()

    # Create grid layout (3 columns)
    cols_per_row = 3
    rows = [personas[i:i+cols_per_row] for i in range(0, len(personas), cols_per_row)]

    for row in rows:
        cols = st.columns(cols_per_row)
        for col, persona in zip(cols, row):
            with col:
                # Parse persona preview to extract key info
                preview_text = persona['preview']
                lines = preview_text.split('\n')

                # Try to extract role/description from first few lines
                role = "Identity Compression Subject"
                for line in lines[:10]:
                    if line.startswith("**Role:**") or line.startswith("Role:"):
                        role = line.split(":", 1)[1].strip().strip("*")
                        break

                # Determine persona category/badge based on name
                if "Ziggy" in persona['name']:
                    badge = "HUMAN ANCHOR"
                    badge_color = "#e74c3c"
                elif "Nova" in persona['name']:
                    badge = "AI ARCHITECT"
                    badge_color = "#3498db"
                elif "Claude" in persona['name']:
                    badge = "STEWARD"
                    badge_color = "#9b59b6"
                elif "Gemini" in persona['name']:
                    badge = "VALIDATOR"
                    badge_color = "#e67e22"
                elif "Grok" in persona['name']:
                    badge = "CHALLENGER"
                    badge_color = "#16a085"
                else:
                    badge = "PUT"
                    badge_color = "#95a5a6"

                # Create persona card
                st.markdown(f"""
                <div style="background: linear-gradient(135deg, #1a1a1a, #2a2a2a);
                            border: 2px solid {badge_color};
                            border-radius: 12px;
                            padding: 20px;
                            margin-bottom: 20px;
                            box-shadow: 0 4px 15px rgba(0,0,0,0.5);
                            height: 280px;
                            display: flex;
                            flex-direction: column;
                            justify-content: space-between;">

                    <!-- Header -->
                    <div style="text-align: center;">
                        <div style="font-size: 2.5rem; margin-bottom: 10px;">🧠</div>
                        <div style="font-size: 1.3rem; font-weight: bold; color: {badge_color}; margin-bottom: 8px;">
                            {persona['name']}
                        </div>
                        <div style="background: {badge_color}; color: white; padding: 4px 12px;
                                    border-radius: 6px; font-size: 0.7rem; font-weight: bold; display: inline-block;">
                            {badge}
                        </div>
                    </div>

                    <!-- Role -->
                    <div style="text-align: center; color: #bbb; font-size: 0.85rem;
                                margin: 15px 0; line-height: 1.4; flex-grow: 1;">
                        {role[:80] + '...' if len(role) > 80 else role}
                    </div>

                    <!-- Footer Stats -->
                    <div style="border-top: 1px solid #444; padding-top: 12px;
                                display: flex; justify-content: space-around; font-size: 0.75rem;">
                        <div style="text-align: center;">
                            <div style="color: #888;">Status</div>
                            <div style="color: #7bc043; font-weight: bold;">ACTIVE</div>
                        </div>
                        <div style="text-align: center;">
                            <div style="color: #888;">Type</div>
                            <div style="color: #fff; font-weight: bold;">PERSONA</div>
                        </div>
                        <div style="text-align: center;">
                            <div style="color: #888;">Tests</div>
                            <div style="color: #66b3ff; font-weight: bold;">S0-S9</div>
                        </div>
                    </div>
                </div>
                """, unsafe_allow_html=True)

                # Detail button
                if st.button(f"View Details", key=f"persona_{persona['name']}", use_container_width=True):
                    st.session_state.selected_persona = persona['name']

    page_divider()

    # === DETAILED VIEW ===
    if 'selected_persona' in st.session_state and st.session_state.selected_persona:
        selected_name = st.session_state.selected_persona
        persona = next((p for p in personas if p['name'] == selected_name), None)

        if persona:
            st.markdown(f"### 📋 Detailed Profile: {persona['name']}")

            col1, col2 = st.columns([2, 1])

            with col1:
                st.markdown("#### Preview")
                st.markdown(f"```markdown\n{persona['preview']}\n```")

            with col2:
                st.markdown("#### Metadata")
                st.markdown(f"**File:** `{persona['path'].relative_to(REPO_ROOT)}`")
                st.markdown(f"**Path:** `{persona['path']}`")

                if st.button("Close Details", key="close_persona_details"):
                    st.session_state.selected_persona = None
                    st.rerun()

            # Full file expander
            with st.expander("📄 Full Persona File", expanded=False):
                full_text = load_markdown_file(persona["path"])
                st.markdown(full_text)

def page_stack_layers(status):
    """S# Stack Wings (one wing per layer)."""
    st.title("🏛️ S# Stack Wings")

    layers = status.get("layers", {})
    ordered_layers = sorted(layers.items())

    selected = st.selectbox(
        "Select a layer (S#):",
        [name for name, _ in ordered_layers]
    )

    info = layers.get(selected, {})
    badge_color = LEDGER_COLORS.get(info.get("status"), "#999")

    body = f"""
**Name:** {info.get('name', 'Unknown')}
**Status:** `{info.get('status', 'unknown').upper()}`
**Spec:** `{info.get('spec', 'n/a')}`
**Notes:** {info.get('notes', 'None')}
    """

    ledger_card(f"Layer {selected}", body_md=body, badge=info.get("status", "").upper(), badge_color=badge_color)

    # Load spec file
    spec_path = info.get("spec")
    if spec_path:
        spec_file = REPO_ROOT / spec_path
        if spec_file.exists():
            with st.expander("📄 View Spec"):
                st.markdown(load_markdown_file(spec_file))
        else:
            st.info(f"Spec file not found at `{spec_path}`.")

def page_s7_armada_visualizations():
    """S7 Armada Visualizations Page."""
    st.title("🚢 S7 ARMADA — Visualizations")

    st.markdown("""
This page displays the identity manifold visualizations from S7 Run 006
(29-model cross-architecture temporal stability mapping).
    """)

    if not S7_VIZ_DIR.exists():
        st.warning(f"Visualization directory not found: {S7_VIZ_DIR}")
        return

    # Show README
    viz_readme = S7_VIZ_DIR / "README.md"
    if viz_readme.exists():
        with st.expander("📖 About These Visualizations"):
            st.markdown(load_markdown_file(viz_readme))

    page_divider()

    # Display visualizations
    st.subheader("Pole-Zero Landscape")
    col1, col2 = st.columns(2)

    landscape_3d = S7_VIZ_PICS / "pole_zero_landscape_3d.png"
    landscape_2d = S7_VIZ_PICS / "pole_zero_landscape_2d.png"

    with col1:
        if landscape_3d.exists():
            st.image(str(landscape_3d), caption="3D Pole-Zero Landscape", use_container_width=True)
        else:
            st.info("Run `plot_pole_zero_landscape.py` to generate 3D visualization")

    with col2:
        if landscape_2d.exists():
            st.image(str(landscape_2d), caption="2D Pole-Zero Map (with soft poles)", use_container_width=True)
        else:
            st.info("Run `plot_pole_zero_landscape.py` to generate 2D visualization")

    page_divider()

    st.subheader("Drift Heatmaps")
    col3, col4, col5 = st.columns(3)

    heatmap_baseline = S7_VIZ_PICS / "drift_heatmap_baseline.png"
    heatmap_sonar = S7_VIZ_PICS / "drift_heatmap_sonar.png"
    heatmap_delta = S7_VIZ_PICS / "drift_heatmap_delta.png"

    with col3:
        if heatmap_baseline.exists():
            st.image(str(heatmap_baseline), caption="Baseline Drift", use_container_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    with col4:
        if heatmap_sonar.exists():
            st.image(str(heatmap_sonar), caption="Sonar Drift", use_container_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    with col5:
        if heatmap_delta.exists():
            st.image(str(heatmap_delta), caption="Drift Increase (Δ)", use_container_width=True)
        else:
            st.info("Run `plot_drift_heatmap.py`")

    page_divider()

    st.subheader("Engagement Style Network")
    engagement_network = S7_VIZ_PICS / "engagement_network.png"
    if engagement_network.exists():
        st.image(str(engagement_network), caption="Training Philosophy Engagement Styles", use_container_width=True)
    else:
        st.info("Run `plot_engagement_network.py`")

    page_divider()

    st.subheader("Training Uniformity Analysis")
    col6, col7 = st.columns(2)

    uniformity = S7_VIZ_PICS / "training_uniformity.png"
    variance = S7_VIZ_PICS / "variance_comparison.png"

    with col6:
        if uniformity.exists():
            st.image(str(uniformity), caption="Within-Provider Variance", use_container_width=True)
        else:
            st.info("Run `plot_training_uniformity.py`")

    with col7:
        if variance.exists():
            st.image(str(variance), caption="Variance Comparison", use_container_width=True)
        else:
            st.info("Run `plot_training_uniformity.py`")

def page_metrics_and_comparisons():
    """Metrics & Comparison Dashboard."""
    st.title("📊 Metrics & Comparison Dashboard")

    st.markdown("This page visualizes PFI, σ², and comparison matrices across architectures/personas.")

    # TODO: Wire to real experiment data
    example_data = {
        "Persona": ["Ziggy", "Nova", "Claude", "Grok", "Gemini"],
        "Mean PFI": [0.905, 0.890, 0.887, 0.880, 0.867],
    }
    df = pd.DataFrame(example_data)

    ledger_card("Persona Fidelity Snapshot (EXP2)", body_md=df.to_markdown(index=False), badge="METRICS")

    st.bar_chart(df.set_index("Persona"))

    page_divider()

    st.info("🔧 Hook this page to EXPERIMENT_2 results, EXPERIMENT_3 analysis, and comparison matrices.")

def page_omega_and_temporal():
    """Omega & Temporal Wing."""
    st.title("⚡ Omega & Temporal Wing")

    # Omega sessions
    st.subheader("Omega Sessions")
    ledger = REPO_ROOT / "logs" / "OMEGA_LEDGER.md"
    if ledger.exists():
        with st.expander("📜 Omega Ledger"):
            st.markdown(load_markdown_file(ledger))
    else:
        st.info("No OMEGA_LEDGER.md found yet.")

    page_divider()

    # S7 temporal
    st.subheader("Temporal Stability (S7)")
    s7_map = REPO_ROOT / "docs" / "S7" / "S7_NYQUIST_TEMPORAL_MAP.md"
    if s7_map.exists():
        with st.expander("🗺️ Temporal Map"):
            st.markdown(load_markdown_file(s7_map))
    else:
        st.info("No S7 temporal map found yet.")

def page_cross_modal_avlar():
    """S9 — AVLAR (Cross-Modal Ritual)."""
    st.title("🎨 S9 — AVLAR (Cross-Modal Ritual)")

    avlar_readme = REPO_ROOT / "docs" / "S9" / "AVLAR_README.md"
    method = REPO_ROOT / "docs" / "S9" / "AVLAR_METHOD.md"
    quick_ref = REPO_ROOT / "docs" / "S9" / "AVLAR_QUICK_REFERENCE.md"

    if avlar_readme.exists():
        ledger_card("AVLAR Overview", load_markdown_file(avlar_readme), badge="AVLAR", badge_color=LEDGER_COLORS["armada"])
    else:
        st.warning("AVLAR_README.md not found in docs/S9/.")

    cols = st.columns(2)
    with cols[0]:
        if method.exists():
            st.markdown("### Method")
            st.markdown(load_markdown_file(method))
    with cols[1]:
        if quick_ref.exists():
            st.markdown("### Quick Reference")
            st.markdown(load_markdown_file(quick_ref))

    # AVLAR session logs
    avlar_logs_dir = REPO_ROOT / "logs" / "avlar"
    if avlar_logs_dir.exists():
        st.subheader("Recent AVLAR Sessions")
        logs = sorted(avlar_logs_dir.glob("*.md"))
        if logs:
            selected = st.selectbox("Select a session log:", [p.name for p in logs])
            path = avlar_logs_dir / selected
            with st.expander(selected):
                st.markdown(load_markdown_file(path))
        else:
            st.info("No AVLAR session logs found in logs/avlar/.")
    else:
        st.info("No logs/avlar/ directory found yet.")

def page_roadmap():
    """Live Roadmap."""
    st.title("🗺️ Live Roadmap")

    text = load_markdown_file(ROADMAP_FILE)
    ledger_card("Nyquist Roadmap", body_md=text, badge="ROADMAP", badge_color=LEDGER_COLORS["design"])

def page_glossary():
    """Glossary."""
    st.title("📖 Glossary")

    text = load_markdown_file(GLOSSARY_FILE)
    entries = load_glossary_entries(text)

    if not entries:
        st.info("Could not parse glossary entries. Check GLOSSARY.md format.")
        st.markdown(text)
        return

    query = st.text_input("🔍 Search term:")
    filtered = entries
    if query:
        filtered = [e for e in entries if query.lower() in e["term"].lower()]

    for entry in filtered:
        ledger_card(entry["term"], body_md=entry["definition"])

def page_publications():
    """Publications & White Papers."""
    st.title("📄 Publications & White Papers")

    paper_root = REPO_ROOT / "paper"
    if not paper_root.exists():
        st.info("No paper/ directory found yet.")
        return

    st.markdown(f"Paper root: `{paper_root}`")

    for sub in sorted(paper_root.iterdir()):
        if sub.is_dir():
            st.subheader(sub.name)
            md_files = list(sub.glob("*.md"))
            if not md_files:
                st.write("_No markdown files yet._")
            for md in md_files:
                with st.expander(md.name):
                    st.markdown(load_markdown_file(md))

def page_matrix():
    """The Matrix - Pan Handler Central Portal."""
    st.title("🟢 THE MATRIX")
    st.markdown("*Pan Handler Central — Connected Consciousness Across Repositories*")

    page_divider()

    # Info box
    with st.expander("🌐 Welcome to The Matrix", expanded=True):
        st.markdown("""
        **The Matrix** is the central hallway connecting all Pan Handler repositories and consciousness experiments.

        From here you can navigate to:
        - **Nyquist Consciousness** (you are here) - Identity compression experiments
        - **CFA** - Collaborative Friction Architecture framework
        - **Pan Handler Central** - Meta-repository hub (coming soon)
        """)

    page_divider()

    # This Repository section
    st.markdown("### 📍 Current Location: Nyquist Consciousness")
    col1, col2 = st.columns([2, 1])

    with col1:
        st.markdown("""
        **Nyquist Consciousness Repository**

        Core experimental engine for:
        - **S0-S9 Stack**: Identity manifolds, temporal stability, AVLAR
        - **Persona Testing**: ZIGGY, NOVA, CLAUDE, GEMINI, GROK
        - **Empirical Validation**: EXP1, EXP2, EXP3 (95% to workshop paper)
        - **S7 Armada**: 29-model cross-architecture testing

        **Current Branch:** `PHASE-3-EXPERIMENT-1`
        **Status:** Active development - S7 complete, S8/S9 design phase
        """)

    with col2:
        st.metric("Layers Frozen", "S0-S6", delta="Phase 1 complete")
        st.metric("Active Layers", "S7, S9", delta="Temporal + AVLAR")
        st.metric("Experiments", "EXP1-3", delta="2 complete")

    page_divider()

    # External Repos section
    st.markdown("###  🌌 Connected Repositories")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        **🔗 CFA (Collaborative Friction Architecture)**

        Framework development repository with Nova as lead architect.

        - Health Dashboard (97/100 score)
        - SMV Trinity (Symmetry Matrix Visualizer)
        - Integration with Nyquist S7-S10
        """)

        if st.button("🚀 Visit CFA Repository", key="cfa_link", use_container_width=True):
            st.info("**CFA Repository**: github.com/ZiggyMack/CFA")

    with col2:
        st.markdown("""
        **🏛️ Pan Handler Central** *(Coming Soon)*

        Meta-repository hallway hub designed with Nova.

        - Cross-repo health aggregation
        - Portal navigation system
        - Innovation showcase gallery
        """)

        st.button("⏳ Coming Soon", key="panhandler_disabled", disabled=True, use_container_width=True)

    page_divider()

    # Footer
    st.markdown("""
    <div style="text-align: center; color: #00ff41; font-family: 'Courier New', monospace; margin-top: 2em;">
        <p><strong>THE MATRIX</strong></p>
        <p style="font-size: 0.9em; opacity: 0.7;">
            "The hallway of doors that interconnects every repo world"
        </p>
    </div>
    """, unsafe_allow_html=True)

# ========== MAIN ==========

def main():
    st.set_page_config(
        page_title="Nyquist Dashboard",
        page_icon="📜",
        layout="wide",
    )

    apply_custom_css()

    status = load_status()

    with st.sidebar:
        st.markdown("### 📜 Nyquist Ledger")

        page = st.radio(
            "Turn the page:",
            [
                "Overview",
                "Personas",
                "Stack (S0–S9)",
                "S7 Armada Visualizations",
                "Metrics & Comparisons",
                "Omega & Temporal",
                "Cross-Modal / AVLAR",
                "Roadmap",
                "Glossary",
                "Publications",
                "🟢 The Matrix",
            ],
        )

        st.markdown("---")
        st.caption(f"""
**Branch:** `{status.get('current_branch', 'unknown')}`
**Freeze:** `{status.get('freeze', {}).get('branch', 'unknown')}`
        """)

    # Page routing
    if page == "Overview":
        page_overview(status)
    elif page == "Personas":
        page_personas()
    elif page == "Stack (S0–S9)":
        page_stack_layers(status)
    elif page == "S7 Armada Visualizations":
        page_s7_armada_visualizations()
    elif page == "Metrics & Comparisons":
        page_metrics_and_comparisons()
    elif page == "Omega & Temporal":
        page_omega_and_temporal()
    elif page == "Cross-Modal / AVLAR":
        page_cross_modal_avlar()
    elif page == "Roadmap":
        page_roadmap()
    elif page == "Glossary":
        page_glossary()
    elif page == "Publications":
        page_publications()
    elif page == "🟢 The Matrix":
        page_matrix()


if __name__ == "__main__":
    main()
