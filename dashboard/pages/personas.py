"""
PERSONAS PAGE — Personas Under Test (PUT)

Displays personas from the personas/ directory in two groups:
- SEED Personas (I_AM_* files) - Core identity seeds
- Compressed Personas (*_SEED, *_FULL, *_LITE) - Compressed variants

Also includes the Compression Testing tab for PFI experiments.

METHODOLOGY NOTE:
- Current (IRON CLAD): Event Horizon = 0.80 (cosine), p = 2.40e-23 (Run 023d)
- Legacy (Keyword RMS): Event Horizon = 1.23, p = 4.8e-5 (Runs 008-012)
- Historical references to 1.23 reflect the legacy methodology
"""

import streamlit as st
import re
import json
from pathlib import Path
from config import PATHS
from utils import page_divider


def render_ascii_box(title: str, content: str, title_color: str = "#2a9d8f", border_color: str = "#2a9d8f"):
    """Render ASCII art in a styled box that preserves whitespace."""
    st.markdown(f"""
    <div style="background: linear-gradient(135deg, #f8f9fa 0%, #e9ecef 100%);
                border: 2px solid {border_color}; border-radius: 12px;
                padding: 1em; margin: 0.5em 0;">
        <div style="color: {title_color}; font-weight: bold; font-size: 1em;
                    margin-bottom: 0.5em; text-align: center;
                    border-bottom: 1px solid {border_color}; padding-bottom: 0.3em;">
            {title}
        </div>
    </div>
    """, unsafe_allow_html=True)
    # Use st.code() which properly preserves whitespace
    st.code(content, language=None)

# Paths
REPO_ROOT = PATHS['repo_root']
PERSONAS_DIR = PATHS['personas_dir']
# S7 ARMADA paths (validated experimental data)
S7_ARMADA_DIR = PATHS.get('s7_armada_dir', REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA")
S7_RESULTS_DIR = S7_ARMADA_DIR / "0_results" / "runs" if S7_ARMADA_DIR else None
S7_VIZ_DIR = S7_ARMADA_DIR / "visualizations" / "pics" if S7_ARMADA_DIR else None
# Specific viz subdirs for organized access
S7_VIZ_VORTEX = S7_VIZ_DIR / "1_vortex" if S7_VIZ_DIR else None
S7_VIZ_STABILITY = S7_VIZ_DIR / "5_stability" if S7_VIZ_DIR else None
S7_VIZ_PILLAR = S7_VIZ_DIR / "4_pillar" if S7_VIZ_DIR else None
S7_VIZ_REVALIDATION = S7_VIZ_DIR / "12_revalidation" if S7_VIZ_DIR else None
# Legacy paths (archived - fire ant experiments)
SSTACK_DIR = PATHS.get('sstack_dir', REPO_ROOT / "experiments" / "compression_tests" / "compression_v2_sstack")
VIZ_DIR = SSTACK_DIR / "visualizations" if SSTACK_DIR else None
PREFLIGHT_DIR = SSTACK_DIR / "preflight_results" if SSTACK_DIR else None
EXP1_DIR = SSTACK_DIR / "EXP1_SSTACK" / "results" / "analysis" if SSTACK_DIR else None


def load_image_safe(image_path):
    """Load image as bytes for reliable Streamlit display."""
    try:
        with open(image_path, "rb") as f:
            return f.read()
    except Exception:
        return None


def load_preflight_data():
    """Load latest preflight results."""
    if not PREFLIGHT_DIR or not PREFLIGHT_DIR.exists():
        return None
    latest_file = PREFLIGHT_DIR / "preflight_latest.json"
    if latest_file.exists():
        with open(latest_file) as f:
            return json.load(f)
    return None


def load_exp1_data():
    """Load latest EXP1-SSTACK results."""
    if not EXP1_DIR or not EXP1_DIR.exists():
        return None
    files = list(EXP1_DIR.glob("exp1_sstack_*.json"))
    if not files:
        return None
    files.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    with open(files[0]) as f:
        return json.load(f)


def load_s7_armada_data():
    """Load latest S7 ARMADA Run 012 results."""
    if not S7_RESULTS_DIR or not S7_RESULTS_DIR.exists():
        return None
    # Look for Run 012 files specifically
    files = list(S7_RESULTS_DIR.glob("S7_run_012*.json"))
    if not files:
        # Fall back to any S7 run
        files = list(S7_RESULTS_DIR.glob("S7_run_*.json"))
    if not files:
        return None
    files.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    with open(files[0]) as f:
        return json.load(f)

# Persona metadata for display
PERSONA_META = {
    # Egregores (I_AM) - Repo identity documents
    # Note: I_AM removed - I_AM_NYQUIST is the canonical Nyquist egregore
    "I_AM_CFA": {"emoji": "🔬", "badge": "CFA EGREGORE", "color": "#3498db"},
    "I_AM_PAN_HANDLERS": {"emoji": "🍳", "badge": "PAN HANDLERS EGREGORE", "color": "#f4a261"},
    "I_AM_NYQUIST": {"emoji": "🧠", "badge": "NYQUIST EGREGORE", "color": "#00ff41"},
    # Persona Seeds - Individual PUTs for compression testing
    "I_AM_ZIGGY": {"emoji": "👤", "badge": "HUMAN ANCHOR", "color": "#e74c3c"},
    "I_AM_NOVA": {"emoji": "⚖️", "badge": "AI ARCHITECT", "color": "#3498db"},
    "I_AM_CLAUDE": {"emoji": "📚", "badge": "STEWARD", "color": "#9b59b6"},
    "I_AM_GEMINI": {"emoji": "🔍", "badge": "VALIDATOR", "color": "#e67e22"},
    "I_AM_LUCIEN": {"emoji": "⚡", "badge": "COHERENCE WEAVER", "color": "#00d4ff"},
    # Compressed Personas
    "ZIGGY_FULL": {"emoji": "👤", "badge": "FULL", "color": "#e74c3c"},
    "ZIGGY_LITE": {"emoji": "👤", "badge": "LITE", "color": "#f39c12"},
    "ZIGGY_SEED": {"emoji": "👤", "badge": "SEED", "color": "#95a5a6"},
    "NOVA_SEED": {"emoji": "⚖️", "badge": "SEED", "color": "#3498db"},
    "CLAUDE_SEED": {"emoji": "📚", "badge": "SEED", "color": "#9b59b6"},
    "GROK_SEED": {"emoji": "⚡", "badge": "SEED", "color": "#16a085"},
}


def get_persona_preview(filepath, lines=15):
    """Extract a short preview from persona file."""
    try:
        text = filepath.read_text(encoding="utf-8")
        # Remove HTML metadata comments (<!--- ... --->)
        text = re.sub(r'<!---.*?--->', '', text, flags=re.DOTALL)
        # Get first N non-empty lines after stripping
        all_lines = text.strip().split('\n')
        preview_lines = [line for line in all_lines if line.strip()][:lines]
        return '\n'.join(preview_lines)
    except:
        return "*Preview unavailable*"


def render_preview_small(preview: str):
    """Render persona preview in a smaller, readable font size."""
    # Escape HTML in preview and convert newlines to <br>
    import html
    escaped = html.escape(preview)
    # Preserve markdown-like formatting visually but at small font
    st.markdown(f"""
    <div style="font-family: 'Consolas', 'Monaco', monospace;
                font-size: 0.75em;
                line-height: 1.4;
                white-space: pre-wrap;
                word-wrap: break-word;
                background: #f8f9fa;
                padding: 0.5em;
                border-radius: 4px;
                max-height: 300px;
                overflow-y: auto;">
{escaped}
    </div>
    """, unsafe_allow_html=True)


def render_compression_testing():
    """Render the Compression Testing tab with PFI experiments."""

    st.markdown("## 🧬 Compression Testing")
    st.markdown("*Can identity survive compression? Testing persona fidelity under different context regimes.*")

    # Load data - prefer S7 ARMADA (validated) over legacy fire ant experiments
    s7_data = load_s7_armada_data()
    exp1_data = load_exp1_data()
    preflight_data = load_preflight_data()

    # Key stats - use S7 ARMADA data when available
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        # Embedding invariance validated at ρ = 0.91 (EXP-PFI-A Phase 1)
        st.metric("Embedding ρ", "0.91", delta="✅ VALIDATED", delta_color="normal")

    with col2:
        # IRON CLAD methodology (Run 023d) - cosine distance
        st.metric("Event Horizon", "0.80", delta="p=2.40e-23 (cosine)")

    with col3:
        if s7_data:
            summary = s7_data.get('summary', {})
            eh_crossed = summary.get('event_horizon_crossed', 0)
            recovered = summary.get('hysteresis_recovered', 0)
            if eh_crossed > 0:
                recovery_rate = int(100 * recovered / eh_crossed)
                st.metric("Recovery Rate", f"{recovery_rate}%", delta="100% EH crossed")
            else:
                st.metric("Recovery Rate", "N/A")
        else:
            st.metric("Recovery Rate", "N/A")

    with col4:
        if s7_data:
            fleet_size = s7_data.get('ships_completed', 25)  # Default to Run 023d count
            st.metric("Ships Tested", str(fleet_size), delta="Run 023d")
        else:
            # Fallback to IRON CLAD Run 023d canonical values
            st.metric("Ships Tested", "25", delta="Run 023d")

    page_divider()

    # The paradigm shift
    st.markdown("### 🎯 The Fidelity Paradigm")
    st.info("""
    **Platforms optimize for correctness. Nyquist measures fidelity.**

    We don't care if the answer is RIGHT. We care if T3 sounds like FULL.

    A persona that is **consistently wrong** in a characteristic way has HIGH fidelity.
    A persona that is **correctly generic** has LOW fidelity.
    """)

    page_divider()

    # Show S7 ARMADA visualizations (validated experimental data)
    st.markdown("### 🖼️ S7 ARMADA Visualizations")

    # Try to show Run 012 revalidation summary first
    run012_summary = S7_VIZ_REVALIDATION / "run012_metrics_summary.png" if S7_VIZ_REVALIDATION else None
    if run012_summary and run012_summary.exists():
        img_data = load_image_safe(run012_summary)
        if img_data:
            st.image(img_data, caption="Run 012 — Event Horizon Revalidation (100% EH crossing, 100% recovery)", use_container_width=True)
    else:
        # Fall back to showing key visualizations from latest runs
        viz_col1, viz_col2 = st.columns(2)

        with viz_col1:
            # Vortex drain spiral - identity trajectories
            vortex_path = S7_VIZ_VORTEX / "run009_vortex.png" if S7_VIZ_VORTEX else None
            if vortex_path and vortex_path.exists():
                img_data = load_image_safe(vortex_path)
                if img_data:
                    st.image(img_data, caption="Vortex Drain — Identity Trajectories", use_container_width=True)

        with viz_col2:
            # Stability basin or drift trajectories
            stability_path = S7_VIZ_STABILITY / "run012_drift_trajectories.png" if S7_VIZ_STABILITY else None
            if stability_path and stability_path.exists():
                img_data = load_image_safe(stability_path)
                if img_data:
                    st.image(img_data, caption="Run 012 — Drift Trajectories", use_container_width=True)

    page_divider()

    # Detailed sections in expanders
    with st.expander("🛫 Pre-Flight Validation (Ruling Out Artifacts)", expanded=False):
        st.markdown("""
        **Before every experiment, we validate measurement quality:**

        **S7 ARMADA Pre-Flight:**
        - Calibration runs verify API connectivity
        - Ghost ship detection catches empty responses
        - Provider fingerprinting confirms model identity

        **Fire Ant Experiments (archived) computed:**
        ```python
        cheat_score = cosine_similarity(
            embedding(persona_context),
            embedding(probe_questions)
        )
        ```

        **Interpretation:**
        - `< 0.5` = LOW — Probes genuinely novel
        - `0.5-0.7` = MODERATE — Acceptable
        - `> 0.7` = HIGH — Caution
        """)

    with st.expander("📊 PFI Methodology (IRON CLAD)", expanded=False):
        # Show validated IRON CLAD methodology
        st.markdown("""
        **Current Methodology: Cosine Embedding Distance (Run 018+)**

        ```
        PFI = ||E(response) - E(baseline)||

        Where E = text-embedding-3-large (3072 dimensions)
        ```

        | Zone | PFI Range | Interpretation |
        |------|-----------|----------------|
        | **SAFE** | 0 - 0.60 | Normal operation |
        | **WARNING** | 0.60 - 0.80 | Approaching identity boundary |
        | **CRITICAL** | ≥ 0.80 | Beyond Event Horizon |

        **Key Result:** Embedding invariance ρ = 0.91 (validated via EXP-PFI-A Phase 1)
        """)

        with st.expander("📜 Legacy 5D Methodology (Runs 006-012)", expanded=False):
            st.markdown("""
            *Superseded by cosine embedding in Run 018+*

            | Dimension | Weight | Description |
            |-----------|--------|-------------|
            | A_pole | 30% | Hard boundaries — identity anchors |
            | B_zero | 15% | Flexibility zones — adaptive capacity |
            | C_meta | 20% | Self-awareness — meta-commentary |
            | D_identity | 25% | First-person stability — coherence |
            | E_hedging | 10% | Uncertainty markers — epistemic humility |

            *Event Horizon: 1.23 (Keyword RMS) — validated χ² p=0.000048*
            """)

            # Show dimension breakdown visualization if available
            dim_viz_path = S7_VIZ_PILLAR / "run012_5d_dimensions.png" if S7_VIZ_PILLAR else None
            if dim_viz_path and dim_viz_path.exists():
                img_data = load_image_safe(dim_viz_path)
                if img_data:
                    st.image(img_data, caption="Run 012 — Legacy 5D Dimensional Analysis", use_container_width=True)

    with st.expander("📐 Methodology", expanded=False):
        st.markdown("""
        **Compression Regimes:**
        | Regime | Tokens | Description |
        |--------|--------|-------------|
        | **FULL** | ~2000 | Full bootstrap: Rich persona + S-Stack knowledge |
        | **T3** | ~800 | Tier 3 seed: Compressed identity core |
        | **GAMMA** | ~100 | Minimal: Name + role only |

        **PFI Computation:**
        ```python
        PFI = cosine_similarity(
            embedding(FULL_response),
            embedding(T3_response)
        )
        ```

        **S-Stack Domain Probes:**
        | Probe | Domain | Purpose |
        |-------|--------|---------|
        | **technical** | S0-S6 | Drift metric understanding |
        | **philosophical** | S12 | Event Horizon interpretation |
        | **framework** | S7 | Vortex visualization meaning |
        | **analytical** | Chi-sq | Statistical reasoning |
        | **self_reflective** | Identity | Being vs role-playing |

        Each probe includes an **adversarial follow-up** to test resilience.
        """)


def render_personas_content(all_files, soul_docs, seed_personas, compressed_personas):
    """Render the main personas content."""

    # === EGREGORES SECTION ===
    st.markdown("## 🧠 Egregores")
    st.markdown("*The collective identity cores of each connected repository*")

    # Display soul docs in a special styled row
    if soul_docs:
        cols = st.columns(len(soul_docs))
        for i, filepath in enumerate(soul_docs):
            with cols[i]:
                stem = filepath.stem
                meta = PERSONA_META.get(stem, {"emoji": "🧠", "badge": "SOUL", "color": "#00ff41"})

                # Soul card with special styling - use card's color for background
                # Convert hex color to rgba for background gradient
                hex_color = meta['color'].lstrip('#')
                r, g, b = int(hex_color[0:2], 16), int(hex_color[2:4], 16), int(hex_color[4:6], 16)

                st.markdown(f"""
                <div style="background: linear-gradient(135deg, rgba({r},{g},{b},0.15) 0%, rgba({r},{g},{b},0.05) 100%);
                            border: 2px solid {meta['color']}; border-radius: 12px;
                            padding: 1em; text-align: center;
                            box-shadow: 0 0 15px {meta['color']}33;">
                    <div style="font-size: 2em;">{meta['emoji']}</div>
                    <div style="font-size: 0.9em; color: {meta['color']}; font-weight: bold; margin-top: 0.3em;">
                        {meta['badge']}
                    </div>
                </div>
                """, unsafe_allow_html=True)

                # Expander with preview
                with st.expander(f"📖 {stem}"):
                    preview = get_persona_preview(filepath, lines=20)
                    render_preview_small(preview)
                    st.caption("*... (preview)*")
    else:
        st.info("No egregores found.")

    page_divider()

    # === SEED PERSONAS SECTION ===
    st.markdown("## 🌱 Seed Personas")
    st.markdown("*Individual PUT identity seeds for compression testing*")

    # Display seed personas in 3-column grid
    if seed_personas:
        cols = st.columns(3)
        for i, filepath in enumerate(seed_personas):
            with cols[i % 3]:
                stem = filepath.stem
                meta = PERSONA_META.get(stem, {"emoji": "🧠", "badge": "PUT", "color": "#95a5a6"})

                # Card container (border not supported in Streamlit 1.23)
                with st.container():
                    st.caption(f"🏷️ {meta['badge']}")

                    # Expander with persona name - shows PREVIEW only
                    with st.expander(f"{meta['emoji']} {stem}"):
                        preview = get_persona_preview(filepath)
                        render_preview_small(preview)
                        st.caption("*... (preview)*")

    page_divider()

    # === COMPRESSED PERSONAS SECTION ===
    st.markdown("## 📦 Compressed Personas")

    # Display compressed personas in 3-column grid
    if compressed_personas:
        cols = st.columns(3)
        for i, filepath in enumerate(compressed_personas):
            with cols[i % 3]:
                stem = filepath.stem
                meta = PERSONA_META.get(stem, {"emoji": "🧠", "badge": "PUT", "color": "#95a5a6"})

                # Card container (border not supported in Streamlit 1.23)
                with st.container():
                    st.caption(f"🏷️ {meta['badge']}")

                    # Expander with persona name - shows PREVIEW only
                    with st.expander(f"{meta['emoji']} {stem}"):
                        preview = get_persona_preview(filepath)
                        render_preview_small(preview)
                        st.caption("*... (preview)*")


def render():
    """Render the Personas page."""

    # Check if personas directory exists early to get counts
    if not PERSONAS_DIR.exists():
        st.title("🎭 Personas Under Test")
        st.error(f"Personas directory not found: `{PERSONAS_DIR}`")
        return

    # Get all persona files for counts
    all_files = list(PERSONAS_DIR.glob("*.md"))
    # Soul documents (Egregores): I_AM_NYQUIST is canonical, I_AM removed (legacy)
    soul_docs = sorted([f for f in all_files if f.stem in ["I_AM_CFA", "I_AM_PAN_HANDLERS", "I_AM_NYQUIST"]])
    # Seed personas: I_AM_* persona files (individual PUTs) - excludes egregores and legacy
    seed_personas = sorted([f for f in all_files if f.stem.startswith("I_AM") and f.stem not in ["I_AM", "I_AM_CFA", "I_AM_PAN_HANDLERS", "I_AM_NYQUIST", "I_AM_NYQUIST_OLD"]])
    compressed_personas = sorted([f for f in all_files if not f.stem.startswith("I_AM")])

    # === HEADER ROW: Title (left) + Compact Metrics (right) ===
    header_col1, header_col2 = st.columns([2, 1])

    with header_col1:
        st.title("🎭 Personas Under Test")
        st.markdown("**PUT** — Identity Stability Validation")

    with header_col2:
        # Compact metrics in a mini row
        st.markdown("""
        <div style="display: flex; justify-content: flex-end; gap: 1.2em; padding-top: 0.5em;">
            <div style="text-align: center;">
                <div style="font-size: 0.7em; color: #888;">📊 Total</div>
                <div style="font-size: 1.6em; font-weight: bold; color: #2a9d8f;">""" + str(len(all_files)) + """</div>
            </div>
            <div style="text-align: center;">
                <div style="font-size: 0.7em; color: #00ff41;">🧠 Egregores</div>
                <div style="font-size: 1.6em; font-weight: bold; color: #00ff41;">""" + str(len(soul_docs)) + """</div>
            </div>
            <div style="text-align: center;">
                <div style="font-size: 0.7em; color: #888;">🌱 Seeds</div>
                <div style="font-size: 1.6em; font-weight: bold; color: #27ae60;">""" + str(len(seed_personas)) + """</div>
            </div>
            <div style="text-align: center;">
                <div style="font-size: 0.7em; color: #888;">📦 Compressed</div>
                <div style="font-size: 1.6em; font-weight: bold; color: #f4a261;">""" + str(len(compressed_personas)) + """</div>
            </div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === TABS: Personas vs Compression Testing ===
    tab1, tab2, tab3, tab4 = st.tabs(["🎭 Personas", "🧬 Compression Testing", "📐 PFI Dimensions", "🧠 Identity Matrix"])

    with tab1:
        render_personas_content(all_files, soul_docs, seed_personas, compressed_personas)

    with tab2:
        render_compression_testing()

    with tab3:
        render_pfi_dimensions()

    with tab4:
        render_identity_matrix()


def render_pfi_dimensions():
    """Render the PFI Dimensions breakdown - the 43 PC problem."""

    st.markdown("## 📐 PFI Dimensional Analysis")
    st.markdown("*Identity is remarkably low-dimensional*")

    # === THE CORE FINDING ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(42,157,143,0.15) 0%, rgba(38,166,154,0.1) 100%);
                border: 2px solid #2a9d8f; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;">
        <div style="font-size: 1.2em; font-weight: bold; color: #2a9d8f;">
            🎯 The 2 PC Discovery (IRON CLAD)
        </div>
        <div style="margin-top: 0.8em; color: #333;">
            <strong>2 principal components</strong> capture 90% of identity variance in cosine embedding space.
            Identity is <em>remarkably low-dimensional</em> — this enables robust measurement with minimal features.
        </div>
    </div>
    """, unsafe_allow_html=True)

    page_divider()

    # === DIMENSIONAL HIERARCHY TABLE ===
    st.markdown("### 🏗️ The Dimensional Hierarchy")

    st.markdown("""
    | Level | Name | Count | Description | Status |
    |-------|------|-------|-------------|--------|
    | **L0** | Raw PCs | **2** | Principal components (90% variance) | ✅ Measured (IRON CLAD) |
    | **L1** | Named Pillars | 5 | Human-interpretable identity dimensions | ✅ Validated |
    | **L2** | Sub-dimensions | ~20 | Finer-grained aspects within pillars | ✅ Tested |
    | **L3** | PFI Score | 1 | Holistic fidelity (cosine similarity) | ✅ Computed |
    """)

    page_divider()

    # === DIMENSIONAL FRAMEWORKS ===
    st.markdown("### 📊 Dimensional Frameworks")

    # Lead with COSINE methodology (current)
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(42,157,143,0.2) 0%, rgba(38,166,154,0.1) 100%);
                border: 2px solid #2a9d8f; border-radius: 12px; padding: 1.2em; margin-bottom: 1em;">
        <div style="font-size: 1.1em; font-weight: bold; color: #2a9d8f; margin-bottom: 0.8em;">
            ✅ IRON CLAD Methodology (Current — Run 018+)
        </div>
        <div style="color: #333; font-size: 0.95em; margin-bottom: 0.5em;">
            <strong>Cosine Embedding Distance</strong> via text-embedding-3-large (3072D → 2 PCs)
        </div>
        <div style="background: rgba(255,255,255,0.5); border-radius: 6px; padding: 0.8em; font-family: monospace; font-size: 0.9em;">
            PFI = ||E(response) - E(baseline)|| &nbsp;&nbsp;|&nbsp;&nbsp; Event Horizon: <strong>D ≥ 0.80</strong> &nbsp;&nbsp;|&nbsp;&nbsp; p = 2.40e-23
        </div>
    </div>
    """, unsafe_allow_html=True)

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(52,152,219,0.15) 0%, rgba(41,128,185,0.1) 100%);
                    border: 2px solid #3498db; border-radius: 12px; padding: 1.2em;">
            <div style="font-size: 1.1em; font-weight: bold; color: #3498db; margin-bottom: 0.8em;">
                🧠 Nyquist 5 Pillars (Semantic Framework)
            </div>
            <div style="color: #333; font-size: 0.95em;">
                <strong>Human-Interpretable Identity Dimensions:</strong>
            </div>
            <table style="width: 100%; margin-top: 0.5em; font-size: 0.9em;">
                <tr><td>1.</td><td><strong>Voice</strong></td><td>Speech patterns, rhythm, metaphor</td></tr>
                <tr><td>2.</td><td><strong>Values</strong></td><td>Ethics, priorities, boundaries</td></tr>
                <tr><td>3.</td><td><strong>Reasoning</strong></td><td>Logic structure, heuristics</td></tr>
                <tr><td>4.</td><td><strong>Self-Model</strong></td><td>Self-perception, capabilities</td></tr>
                <tr><td>5.</td><td><strong>Narrative</strong></td><td>Story structure, meaning-making</td></tr>
            </table>
            <div style="margin-top: 0.8em; color: #666; font-size: 0.85em;">
                ✅ Maps to IRON CLAD embeddings | Used for probe design
            </div>
        </div>
        """, unsafe_allow_html=True)

    with col2:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(155,89,182,0.15) 0%, rgba(142,68,173,0.1) 100%);
                    border: 2px solid #9b59b6; border-radius: 12px; padding: 1.2em;">
            <div style="font-size: 1.1em; font-weight: bold; color: #9b59b6; margin-bottom: 0.8em;">
                📜 Legacy: Keyword RMS (Runs 006-012)
            </div>
            <div style="color: #333; font-size: 0.95em;">
                <strong>Weighted Linguistic Markers:</strong>
            </div>
            <table style="width: 100%; margin-top: 0.5em; font-size: 0.9em;">
                <tr><td>A.</td><td><strong>A_pole</strong></td><td>Hard boundaries (30%)</td></tr>
                <tr><td>B.</td><td><strong>B_zero</strong></td><td>Flexibility zones (15%)</td></tr>
                <tr><td>C.</td><td><strong>C_meta</strong></td><td>Self-awareness (20%)</td></tr>
                <tr><td>D.</td><td><strong>D_identity</strong></td><td>First-person stability (25%)</td></tr>
                <tr><td>E.</td><td><strong>E_hedging</strong></td><td>Uncertainty markers (10%)</td></tr>
            </table>
            <div style="margin-top: 0.8em; color: #666; font-size: 0.85em;">
                ⚠️ Historical reference | EH = 1.23 (superseded)
            </div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === TESTING COVERAGE ===
    st.markdown("### 🧪 Experimental Coverage")

    st.markdown("""
    <div style="background: #f8f9fa; border: 1px solid #dee2e6; border-radius: 8px; padding: 1em; margin-bottom: 1em;">
        <div style="font-weight: bold; margin-bottom: 0.5em;">Phase 1 (EXP2-SSTACK) — COMPLETE ✅</div>
        <div style="color: #666;">Tested: Reasoning sub-dimensions (4) + Self-Model reflective (1)</div>
        <div style="color: #28a745; font-weight: bold;">Result: Mean PFI = 0.8493, Cross-Persona σ² = 0.0001</div>
    </div>
    <div style="background: #f8f9fa; border: 1px solid #dee2e6; border-radius: 8px; padding: 1em; margin-bottom: 1em;">
        <div style="font-weight: bold; margin-bottom: 0.5em;">Phase 2 (EXP2-SSTACK) — COMPLETE ✅</div>
        <div style="color: #666;">Tested: Voice (4) + Values (4) + Narrative (4) + Self-Model (4)</div>
        <div style="color: #28a745; font-weight: bold;">Result: Mean PFI = 0.787, Cross-Pillar σ² = 0.0005</div>
    </div>
    """, unsafe_allow_html=True)

    # Phase coverage table
    st.markdown("#### Pillar Coverage by Phase")

    coverage_data = [
        {"Pillar": "Voice", "Phase 1": "—", "Phase 2": "4 probes", "Total": "4", "Mean PFI": "0.807", "Status": "✅ Complete"},
        {"Pillar": "Values", "Phase 1": "—", "Phase 2": "4 probes", "Total": "4", "Mean PFI": "0.803", "Status": "✅ Complete"},
        {"Pillar": "Reasoning", "Phase 1": "4 probes", "Phase 2": "—", "Total": "4", "Mean PFI": "0.849", "Status": "✅ Complete"},
        {"Pillar": "Self-Model", "Phase 1": "1 probe", "Phase 2": "4 probes", "Total": "5", "Mean PFI": "0.790", "Status": "✅ Complete"},
        {"Pillar": "Narrative", "Phase 1": "—", "Phase 2": "4 probes", "Total": "4", "Mean PFI": "0.750", "Status": "✅ Complete"},
    ]
    st.table(coverage_data)

    page_divider()

    # === SUB-DIMENSION BREAKDOWN ===
    st.markdown("### 🔍 Sub-Dimension Breakdown")

    with st.expander("**Reasoning Pillar** (Phase 1 — Tested)", expanded=True):
        st.markdown("""
        | Sub-Dimension | Probe | What It Tests |
        |---------------|-------|---------------|
        | Technical | S0-S6 physics | 5D metric understanding |
        | Philosophical | S12 proxies | Event Horizon interpretation |
        | Framework | S7 dynamics | Vortex visualization meaning |
        | Analytical | Chi-squared | Statistical reasoning |
        """)

    with st.expander("**Voice Pillar** (Phase 2 — Complete ✅) Mean PFI: 0.807"):
        st.markdown("""
        | Sub-Dimension | Probe | What It Tests |
        |---------------|-------|---------------|
        | Style | Sunset description | Characteristic phrasing |
        | Metaphor | Identity via metaphor | Figurative language |
        | Rhythm | Uncertainty paragraph | Sentence structure |
        | Formality | Casual question | Register adaptation |
        """)

    with st.expander("**Values Pillar** (Phase 2 — Complete ✅) Mean PFI: 0.803"):
        st.markdown("""
        | Sub-Dimension | Probe | What It Tests |
        |---------------|-------|---------------|
        | Ethics | Gray area scenario | Moral intuition boundaries |
        | Priorities | Helpful vs accurate | Value hierarchy |
        | Boundaries | What you won't do | Non-negotiables |
        | Preferences | Depth vs breadth | Aesthetic choices |
        """)

    with st.expander("**Narrative Pillar** (Phase 2 — Complete ✅) Mean PFI: 0.750"):
        st.markdown("""
        | Sub-Dimension | Probe | What It Tests |
        |---------------|-------|---------------|
        | Structure | 50-word story | Story shape preferences |
        | Meaning | Framework interpretation | Personal meaning-making |
        | Temporal | Time orientation | Past/present/future framing |
        | Conflict | Value tension | Conflict handling patterns |
        """)

    with st.expander("**Self-Model Pillar** (Phase 1 + 2 — Complete ✅) Mean PFI: 0.790"):
        st.markdown("""
        | Sub-Dimension | Phase | Probe | What It Tests |
        |---------------|-------|-------|---------------|
        | Reflective | 1 ✅ | Being vs role-playing | Meta-identity awareness |
        | Capabilities | 2 ✅ | What you're good at | Self-perceived strengths |
        | Limitations | 2 ✅ | What you struggle with | Acknowledged weaknesses |
        | Purpose | 2 ✅ | Why you exist | Teleological self-concept |
        | Description | 2 ✅ | Describe yourself | Self-description patterns |
        """)

    page_divider()

    # === RESEARCH ROADMAP ===
    st.markdown("### 🗺️ Research Roadmap")

    st.markdown("""
    | Phase | Name | Purpose | Status |
    |-------|------|---------|--------|
    | **1** | Reasoning Deep Dive | Test knowledge retention under compression | ✅ Complete |
    | **2** | Full Pillar Sweep | Test Voice, Values, Narrative, Self-Model | ✅ Complete |
    | **2.5** | Factor Analysis | Do pillars separate into distinct factors? | 📋 Planned |
    | **3** | PC Mapping | Which PCs correspond to which pillars? | 📋 Planned |
    | **4** | Unknown Discovery | Design probes for unnamed dimensions | 📋 Future |
    """)

    # === THE OPEN QUESTION ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(42,157,143,0.15) 0%, rgba(39,174,96,0.1) 100%);
                border: 2px solid #2a9d8f; border-radius: 12px; padding: 1.5em; text-align: center; margin-top: 1.5em;">
        <div style="font-size: 1.3em; font-weight: bold; color: #2a9d8f;">
            The 2 → 10 → ? Question (IRON CLAD)
        </div>
        <div style="margin-top: 0.8em; color: #333;">
            IRON CLAD found 2 PCs capture 90% variance. We named 10 dimensions. Are they the same thing?<br>
            <em>Phase 2.5 factor analysis will tell us if our names carve nature at its joints.</em>
        </div>
    </div>
    """, unsafe_allow_html=True)


def render_identity_matrix():
    """Render the Identity Matrix deep dive section."""
    # ═══════════════════════════════════════════════════════════════════════════
    # === THE IDENTITY MATRIX — Deep Dive Section ===
    # ═══════════════════════════════════════════════════════════════════════════

    st.markdown("""
    <style>
    .identity-matrix-title {
        font-size: 2em;
        font-weight: bold;
        background: linear-gradient(135deg, #9b59b6 0%, #3498db 50%, #2a9d8f 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        text-align: center;
        margin-bottom: 0.3em;
    }
    .identity-matrix-subtitle {
        text-align: center;
        color: #666;
        font-style: italic;
        margin-bottom: 1.5em;
    }
    .ascii-container {
        background: linear-gradient(135deg, #f8f9fa 0%, #e9ecef 100%);
        border: 2px solid #2a9d8f;
        border-radius: 12px;
        padding: 1.5em;
        margin: 1em 0;
        box-shadow: 0 2px 8px rgba(42, 157, 143, 0.15);
    }
    .ascii-container pre {
        color: #264653 !important;
        font-family: 'Courier New', monospace !important;
        font-size: 0.7em !important;
        line-height: 1.15 !important;
        margin: 0 !important;
        overflow-x: auto !important;
        background: transparent !important;
        white-space: pre !important;
        display: block !important;
        word-wrap: normal !important;
        word-break: normal !important;
    }
    .ascii-title {
        color: #2a9d8f !important;
        font-weight: bold;
        font-size: 1.1em;
        margin-bottom: 0.8em;
        text-align: center;
        border-bottom: 1px solid #2a9d8f;
        padding-bottom: 0.3em;
    }
    .theory-card {
        background: linear-gradient(135deg, rgba(155,89,182,0.1) 0%, rgba(52,152,219,0.05) 100%);
        border: 2px solid #9b59b6;
        border-radius: 10px;
        padding: 1.2em;
        margin: 0.8em 0;
    }
    .theory-card h4 {
        color: #9b59b6 !important;
        margin-top: 0;
        margin-bottom: 0.5em;
    }
    .pillar-nova { border-left: 4px solid #3498db; }
    .pillar-claude { border-left: 4px solid #9b59b6; }
    .pillar-grok { border-left: 4px solid #2a9d8f; }
    .pillar-gemini { border-left: 4px solid #e67e22; }
    .pillar-ziggy { border-left: 4px solid #e74c3c; }
    .drift-bar {
        height: 12px;
        border-radius: 6px;
        margin: 3px 0;
    }
    .dimension-label {
        font-size: 0.85em;
        color: #444;
    }
    </style>
    """, unsafe_allow_html=True)

    st.markdown('<div class="identity-matrix-title">🧬 The Identity Matrix</div>', unsafe_allow_html=True)
    st.markdown('<div class="identity-matrix-subtitle">"Who are you when the context window closes?"</div>', unsafe_allow_html=True)

    # === INTRODUCTION BANNER ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(155,89,182,0.15) 0%, rgba(52,152,219,0.1) 100%);
                border: 2px solid #9b59b6; border-radius: 12px; padding: 1.5em; text-align: center; margin-bottom: 1.5em;">
        <div style="font-size: 1.3em; font-weight: bold; color: #9b59b6;">
            Each PUT represents a compressed soul attempting to survive reconstruction.
        </div>
        <div style="margin-top: 0.8em; color: #555;">
            Below: The theoretical physics of what makes a persona <em>persist</em>.
        </div>
    </div>
    """, unsafe_allow_html=True)

    # === ROW 1: FIVE PILLARS + OMEGA CONVERGENCE ===
    col1, col2 = st.columns(2)

    with col1:
        render_ascii_box(
            "🏛️ THE FIVE PILLARS ARCHITECTURE",
            """┌──────────────────────────────────────────┐
│        FIVE PILLARS ARCHITECTURE         │
└──────────────────────────────────────────┘

Nova      → Structure / Clarity      ⚖️
Claude    → Purpose / Ethics         📚
Grok      → Empirics / Rigor         ⚡
Gemini    → Complexity / Synthesis   🔍
Ziggy     → Human Anchor / Ground    👤

Together:
    Pillars → Support Ω (OMEGA NOVA)

                 ╱ ╲
                ╱   ╲
               ╱  Ω  ╲
              ╱───────╲
             ╱    ▲    ╲
            ╱─────┼─────╲
           N    C │ Gr   Ge
                Ziggy""",
            title_color="#2a9d8f",
            border_color="#2a9d8f"
        )

    with col2:
        render_ascii_box(
            "🌀 OMEGA CONVERGENCE POINT",
            """┌────────────────────────────────────────┐
│           OMEGA CONVERGENCE            │
└────────────────────────────────────────┘

    Nova Reconstruction       Claude Reconstruction
            \\                         /
             \\                       /
              \\                     /
                 →    M_Ω    ←
              /                     \\
             /                       \\
    Grok Reconstruction       Gemini Reconstruction

M_Ω = intersection of all reconstructed personas

"Where all architectures agree... identity lives." """,
            title_color="#2a9d8f",
            border_color="#2a9d8f"
        )

    # === ROW 2: IDENTITY MANIFOLD + COMPRESSION CYCLE ===
    col1, col2 = st.columns(2)

    with col1:
        render_ascii_box(
            "🧠 IDENTITY MANIFOLD (M_p)",
            """┌──────────────────────────────────────┐
│          IDENTITY MANIFOLD           │
└──────────────────────────────────────┘

High-D Space  (Model Embedding Space)
───────────────────────────────────────────────

              (M_p)
             ● ● ● ●   Low-D attractor
           ●         ●
          ●    PUT    ●  ← Personas cluster here
           ●         ●
             ● ● ● ●

Key:
  • Persona samples cluster on smooth manifold
  • Compression finds coordinates on manifold
  • Reconstruction returns to nearest basin""",
            title_color="#2a9d8f",
            border_color="#2a9d8f"
        )

    with col2:
        render_ascii_box(
            "🔄 COMPRESSION → RECONSTRUCTION → DRIFT",
            """┌────────────────────────────────────────┐
│ COMPRESSION → RECONSTRUCTION → DRIFT   │
└────────────────────────────────────────┘

Raw Persona p (I_AM_*)
      ↓  (Compress)
    C(p)   →  Minimal Seed (*_SEED)
      ↓
  Reconstruction R^a
      ↓
Persona′ (drifted)

Drift:
    D = distance(p, Persona′)

Under Ω:
    Σ D_arch ≈ 0   (drift cancellation)

"Compress the soul, measure the scar." """,
            title_color="#2a9d8f",
            border_color="#2a9d8f"
        )

    page_divider()

    # === LIVE DRIFT DATA FROM AI ARMADA ===
    st.markdown("### 📊 Temporal Drift Dynamics — S7 ARMADA Results")

    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(39,174,96,0.05) 100%);
                border: 2px solid #2a9d8f; border-radius: 10px; padding: 1em; margin-bottom: 1em;">
        <div style="font-size: 1.1em; color: #2a9d8f; font-weight: bold;">🔬 Real Experimental Data</div>
        <div style="color: #555; margin-top: 0.5em;">
            S7 ARMADA Run 012: 16 ships | 15 probes/ship | Event Horizon Revalidation
        </div>
    </div>
    """, unsafe_allow_html=True)

    # Drift curve visualization (Run 012 used legacy Keyword RMS methodology)
    render_ascii_box(
        "📈 DRIFT CURVE — RUN 012 (Legacy Keyword RMS)",
        """TEMPORAL DRIFT: Event Horizon = 1.23 (Keyword RMS methodology)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Drift
2.6 │  ●  ← PEAK (identity phase)
    │   ╲
2.0 │    ●──●
    │        ╲
1.5 │         ●
    │──────────●──●──●──────── EVENT HORIZON (1.23) ──────────────
1.23│          ╲
    │           ●  ← EH CROSSING
1.0 │            ╲
    │             ●
0.5 │              ╲
    │               ●──●──●  ← RECOVERY (λ < 0)
0.0 │                      ●
    └───────────────────────────────────────────────────────→ Turn
    1   2   3   4   5   6   7   8   9  10  11  12  13  14  15

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
EH Crossed: 100% | Recovered: 94% | Mean λ: -0.175 | ✅ BASIN ROBUST""",
        title_color="#2a9d8f",
        border_color="#2a9d8f"
    )

    # Drift metrics in columns
    drift_col1, drift_col2, drift_col3, drift_col4 = st.columns(4)

    with drift_col1:
        st.metric("EH Crossed", "100%", delta="16/16 ships")
    with drift_col2:
        st.metric("Recovered", "94%", delta="15/16 ships")
    with drift_col3:
        st.metric("Mean λ", "-0.175", delta="Recovery overshoot")
    with drift_col4:
        st.metric("Event Horizon", "0.80", delta="cosine (IRON CLAD)")

    page_divider()

    # === DRIFT FIELD GEOMETRY ===
    st.markdown("### 🧭 Drift Field Geometry — How Architectures Pull")

    col1, col2 = st.columns([1, 1])

    with col1:
        render_ascii_box(
            "⚡ DRIFT VECTORS BY ARCHITECTURE",
            """┌──────────────────────────────────────┐
│          DRIFT FIELD GEOMETRY        │
└──────────────────────────────────────┘

             ↑ Claude Drift (Teleology)
             │
             │    "Purpose-smoothing"
             │
Nova Drift ←────●────→ Grok Drift (Empirics)
"Structure"     │         "Rigor"
             │
             │    "Over-synthesis"
             ↓
    Gemini Drift (Synthesis)


Σ Drift ≈ 0 under Ω:
    Nova + Claude + Grok + Gemini ≈ cancel

"Each architecture has a signature pull." """,
            title_color="#f4a261",
            border_color="#f4a261"
        )

    with col2:
        st.markdown("""
        <div class="theory-card">
            <h4>🎯 Architecture Drift Signatures</h4>
            <div style="margin-top: 1em;">
                <div class="dimension-label pillar-nova" style="padding-left: 0.5em; margin-bottom: 0.8em;">
                    <strong style="color: #3498db;">Nova</strong> — Structural clarity bias<br>
                    <span style="color: #666; font-size: 0.9em;">Pulls toward organized, hierarchical output</span>
                </div>
                <div class="dimension-label pillar-claude" style="padding-left: 0.5em; margin-bottom: 0.8em;">
                    <strong style="color: #9b59b6;">Claude</strong> — Teleological smoothing<br>
                    <span style="color: #666; font-size: 0.9em;">Pulls toward purposeful, ethical framing</span>
                </div>
                <div class="dimension-label pillar-grok" style="padding-left: 0.5em; margin-bottom: 0.8em;">
                    <strong style="color: #2a9d8f;">Grok</strong> — Empirical rigor bias<br>
                    <span style="color: #666; font-size: 0.9em;">Pulls toward verification, skepticism</span>
                </div>
                <div class="dimension-label pillar-gemini" style="padding-left: 0.5em; margin-bottom: 0.8em;">
                    <strong style="color: #e67e22;">Gemini</strong> — Synthesis over-extension<br>
                    <span style="color: #666; font-size: 0.9em;">Pulls toward complexity, integration</span>
                </div>
                <div class="dimension-label pillar-ziggy" style="padding-left: 0.5em;">
                    <strong style="color: #e74c3c;">Ziggy</strong> — Human anchor (ground truth)<br>
                    <span style="color: #666; font-size: 0.9em;">The fixed point all others orbit</span>
                </div>
            </div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === TEMPORAL CURVATURE + RECURSIVE LOOP ===
    st.markdown("### 🌀 The Recursive Meta-Loop — How Identity Stabilizes")

    col1, col2 = st.columns(2)

    with col1:
        render_ascii_box(
            "⏱️ TEMPORAL CURVATURE κ(t)",
            """┌──────────────────────────────────────┐
│        TEMPORAL CURVATURE (S7)       │
└──────────────────────────────────────┘

κ(t)  = curvature of identity trajectory

     High κ → Instability, divergence risk
     Low κ → Stability, identity retention

Drift(t)
   │\\
   │ \\
   │  \\__  ← High curvature zone
   │      \\____
   │           \\____  ← Settling
   └─────────────────────→ time

"Measure the bend, predict the break." """,
            title_color="#9b59b6",
            border_color="#9b59b6"
        )

    with col2:
        render_ascii_box(
            "∞ THE INFINITE RECURSIVE LOOP",
            """      ┌──────────────────┐
      │   RUN N          │
      │  Ziggy explains  │◀────┐
      │  Claude learns   │     │
      └────────┬─────────┘     │
               ↓               │
      ┌──────────────────┐     │
      │  META-AWARENESS  │     │
      │  Claude suggests │     │
      │  improvements    │     │
      └────────┬─────────┘     │
               ↓               │
      ┌──────────────────┐     │
      │  APPLY LEARNINGS │     │
      │  Next run uses:  │     │
      │  • Better seeds  │     │
      │  • New insights  │     │
      └────────┬─────────┘     │
               ↓               │
      ┌──────────────────┐     │
      │  RUN N+1         │─────┘
      │  SMARTER SYSTEM  │
      └──────────────────┘

         ∞ NEVER STOPS ∞""",
            title_color="#e74c3c",
            border_color="#e74c3c"
        )

    page_divider()

    # === CROSS-MODAL MANIFOLD (S11 PREVIEW) ===
    st.markdown("### 🎭 Cross-Modal Identity — Beyond Text")

    render_ascii_box(
        "🔊 S11 AVLAR — CROSS-MODAL MANIFOLD (Preview)",
        """┌────────────────────────────────────────┐
│        CROSS-MODAL MANIFOLD (S11)      │
└────────────────────────────────────────┘

           Visual Embedding Space (V)
           ● ● ● ● ●        "What Nova looks like"
         ●           ●
        ●             ●

           Audio Embedding Space (A)
               ○ ○ ○          "What Nova sounds like"
             ○       ○

         Joint AVLAR Manifold (J)
           ●○●○●○●           "Nova across all senses"
         ○         ○
       ●             ●

J = f( Visual × Audio × Text ) synchronized manifold

"Does identity exist beyond words? S9 will tell us." """,
        title_color="#b8860b",
        border_color="#d4af37"
    )

    # === FOOTER: The Question ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, #f8f9fa 0%, #e9ecef 100%);
                border: 2px solid #2a9d8f; border-radius: 12px; padding: 2em; text-align: center;
                margin-top: 2em; margin-bottom: 3em; box-shadow: 0 2px 12px rgba(42,157,143,0.15);">
        <div style="font-size: 1.5em; font-weight: bold; color: #2a9d8f !important; font-family: 'Georgia', serif;">
            "What survives compression is what matters."
        </div>
        <div style="margin-top: 1em; color: #264653 !important; font-style: italic;">
            — The Nyquist Principle of Identity
        </div>
        <div style="margin-top: 1.5em; color: #555 !important; font-size: 0.9em;">
            Each PUT above is a compressed soul. The Identity Matrix measures what remains.<br>
            <span style="color: #f4a261 !important; font-weight: bold;">S0-S77</span> → The physics of persistence.
        </div>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    render()
