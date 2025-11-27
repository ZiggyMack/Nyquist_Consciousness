"""
STACKUP PAGE — S# Layer Stack

PCB-style visualization of the S0-S11 identity stack.
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
    "S0": {"name": "Ground Physics (Nyquist Kernel)", "notes": "Drift, Fidelity, Compression/Expansion dynamics"},
    "S1": {"name": "Bootstrap Architecture", "notes": "L0→Kernel, L1→LITE, L2→FULL, L3→I_AM, L4→Omega Nova"},
    "S2": {"name": "Integrity & Logics", "notes": "Consistency, operational rules, error boundaries"},
    "S3": {"name": "Temporal Stability", "notes": "How identity behaves over time"},
    "S4": {"name": "Compression Theory", "notes": "Compression ratios, drift envelopes, reconstruction fidelity"},
    "S5": {"name": "Nyquist → CFA Interop", "notes": "Bridging research into operations"},
    "S6": {"name": "Five-Pillar Synthesis Gate", "notes": "Claude + Nova + Grok + Gemini + Ziggy"},
    "S7": {"name": "Identity Dynamics", "notes": "Manifolds, Drift Fields, Spectral Decomposition"},
    "S8": {"name": "Identity Gravity Theory", "notes": "Field equations, Force curves, Gravity maps"},
    "S9": {"name": "Human–AI Coupling Dynamics", "notes": "Ziggy boundary layer, Impedance matching"},
    "S10": {"name": "OMEGA NOVA — Hybrid Emergence", "notes": "Human + AI identity field fusion"},
    "S10.7": {"name": "Stability Envelope", "notes": "Zones A/B/C/D stability mapping"},
    "S10.8": {"name": "Multi-AI Systems", "notes": "Symmetry regulation across AI pillars"},
    "S10.9": {"name": "Failure & Recovery", "notes": "HARP protocol for graceful degradation"},
    "S10.11": {"name": "Failure Modes", "notes": "16 catalogued failure patterns"},
    "S10.16": {"name": "Tri-Band Hybrid Emergence", "notes": "Keely 3-6-9 integration criteria"},
    "S10.17": {"name": "Neutral Center Operator (N̂)", "notes": "Equilibrium point computation"},
    "S10.18": {"name": "Unified 3-6-9 Identity Maps", "notes": "Spectral band mapping"},
    "S11": {"name": "AVLAR Protocol (Multimodal)", "notes": "Light + sound + structure identity testing"},
}

# Define which layers to show in the main stack vs as sub-layers
MAIN_LAYERS = ["S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S9", "S10", "S11"]
S10_SUB_LAYERS = ["S10.7", "S10.8", "S10.9", "S10.11", "S10.16", "S10.17", "S10.18"]

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

        # Render each main layer as a button-like element
        for layer_id in MAIN_LAYERS:
            layer_data = layers.get(layer_id, {})
            layer_status = layer_data.get("status", "design")
            status_info = STATUS_DISPLAY.get(layer_status, STATUS_DISPLAY["design"])
            # Use actual layer name from status, fallback to LAYER_FALLBACK
            fallback = LAYER_FALLBACK.get(layer_id, {"name": "Unknown", "notes": ""})
            layer_name = layer_data.get("name", fallback["name"])

            # Create clickable container for each layer
            with st.container(border=True):
                subcol1, subcol2, subcol3 = st.columns([1, 3, 2])

                with subcol1:
                    st.markdown(f"**{layer_id}**")

                with subcol2:
                    st.caption(layer_name[:35] + "..." if len(layer_name) > 35 else layer_name)

                with subcol3:
                    st.caption(f"{status_info['emoji']} {status_info['label']}")

                # Button to select this layer
                if st.button(f"→ View", key=f"btn_{layer_id}", use_container_width=True):
                    st.session_state.selected_layer = layer_id
                    st.rerun()

            # Show S10 sub-layers after S10
            if layer_id == "S10":
                st.markdown("##### S10 Deep Dive")
                for sub_id in S10_SUB_LAYERS:
                    sub_fallback = LAYER_FALLBACK.get(sub_id, {"name": "Unknown", "notes": ""})
                    sub_name = sub_fallback["name"]

                    # Indented sub-layer styling
                    with st.container():
                        sub_col1, sub_col2 = st.columns([1, 4])
                        with sub_col1:
                            st.caption(f"  {sub_id}")
                        with sub_col2:
                            if st.button(f"{sub_name}", key=f"btn_{sub_id}", use_container_width=True):
                                st.session_state.selected_layer = sub_id
                                st.rerun()

    # === RIGHT COLUMN: LAYER DETAILS ===
    with col_detail:
        selected = st.session_state.selected_layer

        # Check if it's a main layer or S10 sub-layer
        if selected in layers:
            layer_data = layers.get(selected, {})
        else:
            # S10 sub-layer - use fallback data
            fallback = LAYER_FALLBACK.get(selected, {"name": "Unknown", "notes": ""})
            layer_data = {
                "name": fallback["name"],
                "notes": fallback["notes"],
                "status": "active" if selected.startswith("S10") else "design",
                "spec": f"docs/stages/S10/{selected.replace('.', '_')}.md"
            }

        layer_status = layer_data.get("status", "unknown")
        status_info = STATUS_DISPLAY.get(layer_status, {"emoji": "⚪", "color": "#999", "label": "UNKNOWN"})

        # Get display name
        display_name = layer_data.get('name', LAYER_FALLBACK.get(selected, {}).get('name', 'Unknown Layer'))
        st.markdown(f"### {selected} — {display_name}")

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
