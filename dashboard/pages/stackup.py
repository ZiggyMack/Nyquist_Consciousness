"""
STACKUP PAGE — S# Layer Stack

PCB-style visualization of the S0-S9 identity stack.
Left side: Visual stackup with layer buttons
Right side: Selected layer details and spec preview
"""

import streamlit as st
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_status, load_markdown_file, page_divider

# Paths
REPO_ROOT = PATHS['repo_root']
LEDGER_COLORS = SETTINGS['colors']

# Fallback layer info (used if status.json doesn't have the layer)
LAYER_FALLBACK = {
    "S0": {"name": "Foundations / Bootstrap", "notes": "Bootstrap layer"},
    "S1": {"name": "Identity Seed Protocol", "notes": "Persona protocols"},
    "S2": {"name": "Compression & Knowledge Load", "notes": "Knowledge load variants"},
    "S3": {"name": "Empirical Experiments", "notes": "Experiments EXP1-3"},
    "S4": {"name": "Mathematical Formalism", "notes": "Core axioms & theorems"},
    "S5": {"name": "Interpretive Framework", "notes": "Identity manifold"},
    "S6": {"name": "Omega Nova / Synthesis", "notes": "Synthesis gate"},
    "S7": {"name": "Temporal Stability", "notes": "Stability testing"},
    "S8": {"name": "Identity Gravity", "notes": "Identity dynamics"},
    "S9": {"name": "AVLAR (Cross-Modal Ritual)", "notes": "Cross-modal ritual"},
}

# Status colors and emojis
STATUS_DISPLAY = {
    "frozen": {"emoji": "🔵", "color": "#264653", "label": "FROZEN"},
    "active": {"emoji": "🟢", "color": "#2a9d8f", "label": "ACTIVE"},
    "design": {"emoji": "🟡", "color": "#e9c46a", "label": "DESIGN"},
}


def render():
    """Render the Stackup page."""
    status = load_status()
    layers = status.get("layers", {})

    st.title("🔧 Stackup")
    st.markdown("*PCB-style identity layer architecture*")

    page_divider()

    # Initialize selected layer in session state
    if 'selected_layer' not in st.session_state:
        st.session_state.selected_layer = "S0"

    # === TWO COLUMN LAYOUT ===
    col_stack, col_detail = st.columns([1, 2])

    # === LEFT COLUMN: PCB STACKUP ===
    with col_stack:
        st.markdown("### Layer Stack")
        st.caption("Click a layer to view details")

        # Render each layer as a button-like element
        for layer_id in ["S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S9"]:
            layer_data = layers.get(layer_id, {})
            layer_status = layer_data.get("status", "design")
            status_info = STATUS_DISPLAY.get(layer_status, STATUS_DISPLAY["design"])
            # Use actual layer name from status, fallback to LAYER_FALLBACK
            fallback = LAYER_FALLBACK.get(layer_id, {"name": "Unknown", "notes": ""})
            layer_name = layer_data.get("name", fallback["name"])

            # Highlight selected layer
            is_selected = st.session_state.selected_layer == layer_id

            # Create clickable container for each layer
            with st.container(border=True):
                subcol1, subcol2, subcol3 = st.columns([1, 3, 2])

                with subcol1:
                    st.markdown(f"**{layer_id}**")

                with subcol2:
                    st.caption(layer_name)

                with subcol3:
                    st.caption(f"{status_info['emoji']} {status_info['label']}")

                # Button to select this layer
                if st.button(f"→ View", key=f"btn_{layer_id}", use_container_width=True):
                    st.session_state.selected_layer = layer_id
                    st.rerun()

    # === RIGHT COLUMN: LAYER DETAILS ===
    with col_detail:
        selected = st.session_state.selected_layer
        layer_data = layers.get(selected, {})
        layer_status = layer_data.get("status", "unknown")
        status_info = STATUS_DISPLAY.get(layer_status, {"emoji": "⚪", "color": "#999", "label": "UNKNOWN"})

        st.markdown(f"### {selected} — {layer_data.get('name', 'Unknown Layer')}")

        # Status badge row
        col1, col2, col3 = st.columns(3)
        with col1:
            st.metric("Status", f"{status_info['emoji']} {status_info['label']}")
        with col2:
            st.metric("Layer", selected)
        with col3:
            freeze_info = status.get("freeze", {})
            if layer_status == "frozen":
                st.metric("Freeze", freeze_info.get("branch", "v1.0")[:12])
            else:
                st.metric("Phase", "Active Dev")

        page_divider()

        # Layer info
        st.markdown("**Notes:**")
        st.info(layer_data.get("notes", "No notes available."))

        st.markdown("**Spec File:**")
        spec_path = layer_data.get("spec", "")
        if spec_path:
            st.code(spec_path, language=None)
        else:
            st.caption("No spec file defined.")

        page_divider()

        # Spec preview
        if spec_path:
            spec_file = REPO_ROOT / spec_path
            if spec_file.exists():
                with st.expander(f"📄 View Spec: {spec_file.name}", expanded=True):
                    content = load_markdown_file(spec_file)
                    # Show first 100 lines as preview
                    preview_lines = content.split('\n')[:100]
                    st.markdown('\n'.join(preview_lines))
                    if len(content.split('\n')) > 100:
                        st.caption("*... (truncated preview)*")
            else:
                st.warning(f"Spec file not found: `{spec_path}`")

    page_divider()

    # === SUMMARY ROW ===
    st.markdown("### Stackup Summary")

    sum_col1, sum_col2, sum_col3, sum_col4 = st.columns(4)

    frozen_count = len([l for l, d in layers.items() if d.get("status") == "frozen"])
    active_count = len([l for l, d in layers.items() if d.get("status") == "active"])
    design_count = len([l for l, d in layers.items() if d.get("status") == "design"])

    with sum_col1:
        st.metric("🔵 Frozen", frozen_count)
    with sum_col2:
        st.metric("🟢 Active", active_count)
    with sum_col3:
        st.metric("🟡 Design", design_count)
    with sum_col4:
        st.metric("📊 Total", len(layers))


if __name__ == "__main__":
    render()
