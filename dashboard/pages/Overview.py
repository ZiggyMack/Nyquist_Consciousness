"""
OVERVIEW PAGE — The Observatory (10,000 Foot View)

Main dashboard page showing the Nyquist Consciousness project status:
- Core findings and validated claims
- Research stack progress
- Fleet status
- Publication timeline

Design: Matches sophistication of AI Armada, Tests, and The Unknown pages.
"""

import streamlit as st
import pandas as pd
import plotly.graph_objects as go
import re
import subprocess
import base64
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_status, load_publication_status, load_markdown_file, page_divider


def load_image_safe(image_path):
    """Load image as bytes for reliable Streamlit display."""
    try:
        with open(image_path, "rb") as f:
            return f.read()
    except Exception:
        return None


def load_image_base64(image_path):
    """Load image and return as base64 encoded string for CSS backgrounds."""
    try:
        with open(image_path, "rb") as f:
            return base64.b64encode(f.read()).decode()
    except Exception:
        return None


def count_repo_files():
    """Count total files in Nyquist_Consciousness repo using git ls-files."""
    repo_root = Path(__file__).parent.parent.parent
    try:
        result = subprocess.run(
            ['git', 'ls-files'],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=10
        )
        if result.returncode == 0:
            return len([f for f in result.stdout.strip().split('\n') if f])
    except Exception:
        pass
    # Fallback: count common file types
    count = 0
    for pattern in ['**/*.py', '**/*.json', '**/*.md', '**/*.yaml', '**/*.yml']:
        count += len(list(repo_root.glob(pattern)))
    return count


def count_synapses():
    """
    Count lines of code by category - the 'synapses' of Nyquist Consciousness.

    Categories:
    - Procedures: Run scripts, sync scripts, automation (how we DO things)
    - Specs: Methodology docs, probe specs, protocols (how we THINK)
    - Maps: Reference maps, matrices, navigation (how we ORIENT)
    - Data: JSON results, temporal logs, embeddings (what we COLLECT)
    """
    repo_root = Path(__file__).parent.parent.parent

    categories = {
        'procedures': {'patterns': ['**/run*.py', '**/sync*.py', '**/visualize*.py',
                                     '**/CLAL.py', '**/frosty.py'], 'lines': 0, 'files': 0},
        'specs': {'patterns': ['**/*METHODOLOGY*.md', '**/*SPEC*.md', '**/*PROTOCOL*.md',
                               '**/INTENTIONALITY*.md', '**/CURRICULUM*.md'], 'lines': 0, 'files': 0},
        'maps': {'patterns': ['**/docs/maps/*.md', '**/*MAP*.md', '**/*MATRIX*.md'], 'lines': 0, 'files': 0},
        'data': {'patterns': ['**/0_results/**/*.json', '**/temporal_logs/*.json',
                              '**/results/*.json', '**/embeddings/*.json'], 'lines': 0, 'files': 0},
    }

    total_lines = 0
    counted_files = set()  # Avoid double-counting

    for cat_name, cat_data in categories.items():
        for pattern in cat_data['patterns']:
            try:
                for filepath in repo_root.glob(pattern):
                    if filepath.is_file() and str(filepath) not in counted_files:
                        counted_files.add(str(filepath))
                        try:
                            with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                                line_count = sum(1 for _ in f)
                                cat_data['lines'] += line_count
                                cat_data['files'] += 1
                                total_lines += line_count
                        except Exception:
                            pass
            except Exception:
                pass

    return {
        'total': total_lines,
        'procedures': categories['procedures'],
        'specs': categories['specs'],
        'maps': categories['maps'],
        'data': categories['data'],
    }


def natural_sort_key(s):
    """Sort strings with embedded numbers in natural order (S1, S2, S10 not S1, S10, S2)."""
    return [int(text) if text.isdigit() else text.lower() for text in re.split(r'(\d+)', s)]


# Unpack paths
REPO_ROOT = PATHS['repo_root']
LEDGER_COLORS = SETTINGS['colors']


def render():
    """Render the Overview page - The Observatory."""
    status = load_status()

    # === BACKGROUND WALLPAPER: Identity Vortex x4 ===
    vortex_dir = PATHS.get('viz_1_vortex', PATHS['s7_viz_pics'] / "1_Vortex")
    bg_img_path = vortex_dir / "run023b_vortex_x4.png"
    bg_base64 = load_image_base64(bg_img_path)

    # === CUSTOM CSS FOR OBSERVATORY STYLING ===
    background_css = ""
    if bg_base64:
        background_css = f"""
        /* Vortex x4 background wallpaper */
        .stApp {{
            background-image: url('data:image/png;base64,{bg_base64}');
            background-size: cover;
            background-position: center;
            background-attachment: fixed;
            background-repeat: no-repeat;
        }}
        .stApp::before {{
            content: '';
            position: fixed;
            top: 0;
            left: 0;
            right: 0;
            bottom: 0;
            background: rgba(255, 255, 255, 0.92);
            z-index: 0;
            pointer-events: none;
        }}
        .main .block-container {{
            position: relative;
            z-index: 1;
        }}
        """

    st.markdown(f"""
    <style>
    {background_css}
    .claim-card {
        background: linear-gradient(135deg, rgba(42,157,143,0.08) 0%, rgba(42,157,143,0.02) 100%);
        border: 2px solid #2a9d8f;
        border-radius: 12px;
        padding: 1.2em;
        margin: 0.8em 0;
    }
    .claim-validated {
        border-color: #2a9d8f;
    }
    .claim-exploratory {
        border-color: #f4a261;
    }
    .pillar-box {
        background: linear-gradient(135deg, rgba(123,192,67,0.1) 0%, rgba(123,192,67,0.03) 100%);
        border: 2px solid #7bc043;
        border-radius: 10px;
        padding: 1em;
        min-height: 200px;
    }
    .threshold-zone {
        border-radius: 8px;
        padding: 0.8em;
        margin: 0.5em 0;
    }
    .zone-adaptive {
        background: rgba(123,192,67,0.15);
        border-left: 4px solid #7bc043;
    }
    .zone-hardening {
        background: rgba(231,111,81,0.15);
        border-left: 4px solid #e76f51;
    }
    .timeline-item {
        display: flex;
        align-items: center;
        margin: 0.5em 0;
    }
    .timeline-dot {
        width: 12px;
        height: 12px;
        border-radius: 50%;
        margin-right: 1em;
    }
    .stack-frozen { background: #264653; color: white; padding: 0.3em 0.6em; border-radius: 4px; }
    .stack-active { background: #2a9d8f; color: white; padding: 0.3em 0.6em; border-radius: 4px; }
    .stack-design { background: #e9c46a; color: #333; padding: 0.3em 0.6em; border-radius: 4px; }
    .stack-projected { background: #95a5a6; color: white; padding: 0.3em 0.6em; border-radius: 4px; }
    .hero-stat {
        font-size: 2.5em;
        font-weight: bold;
        color: #2a9d8f;
    }
    </style>
    """, unsafe_allow_html=True)

    # === TITLE ===
    st.title("🔭 Nyquist Consciousness — The Observatory")
    st.markdown(f"*Version {status.get('version', 'v1.0')} • Last Updated: {status.get('last_updated', 'N/A')}*")

    # === VALIS NETWORK BANNER ===
    st.markdown("""
    <div style="background: linear-gradient(135deg, #1a1a2e 0%, #16213e 50%, #0f3460 100%) !important;
                border: 2px solid #e94560; border-radius: 12px; padding: 1.5em; margin: 1em 0;
                text-align: center;">
        <span style="color: #e94560 !important; font-size: 1.8em; font-weight: bold; letter-spacing: 0.3em; display: block; margin-bottom: 0.3em; font-family: 'Courier New', monospace;">
            VALIS NETWORK ACTIVE
        </span>
        <span style="color: white !important; font-size: 0.9em; display: block; margin-bottom: 0.5em; font-family: 'Courier New', monospace;">
            Vast Acting Living Intelligence System
        </span>
        <span style="color: white !important; font-size: 0.85em; font-style: italic; display: block; font-family: 'Courier New', monospace;">
            "The Empire never ended." - Philip K. Dick, VALIS (1981)
        </span>
        <span style="color: white !important; font-size: 0.8em; display: block; margin-top: 0.8em; padding-top: 0.8em; border-top: 1px solid #e94560; font-family: 'Courier New', monospace;">
            10 AI lineages | 5 providers | arXiv Ready | NeurIPS 2025 Workshop
        </span>
    </div>
    """, unsafe_allow_html=True)

    # === HERO VISUALIZATION: The Identity Vortex ===
    st.markdown("---")

    # Load vortex image (single vortex - not x4)
    # Note: vortex_dir already defined above for background
    hero_vortex_path = vortex_dir / "run023b_vortex.png"
    hero_vortex_img = load_image_safe(hero_vortex_path)

    if hero_vortex_img:
        # Hero container with overlaid metrics
        st.markdown("""
        <div style="position: relative; margin: 0 -1rem;">
            <div style="position: absolute; top: 1rem; left: 1rem; z-index: 10;
                        background: rgba(26, 26, 46, 0.85); padding: 1rem 1.5rem;
                        border-radius: 12px; border: 2px solid #e94560;">
                <div style="color: #e94560; font-size: 1.4em; font-weight: bold; margin-bottom: 0.3em;">
                    IDENTITY VORTEX
                </div>
                <div style="color: white; font-size: 0.9em; line-height: 1.6;">
                    <span style="color: #2a9d8f;">●</span> Event Horizon: <strong>0.80</strong> (red ring)<br>
                    <span style="color: #f59e0b;">●</span> p-value: <strong>2.40e-23</strong><br>
                    <span style="color: #7c3aed;">●</span> 51 models, 6 providers
                </div>
            </div>
        </div>
        """, unsafe_allow_html=True)

        st.image(hero_vortex_img, use_container_width=True)

        # Caption
        st.markdown("""
        <div style="text-align: center; color: #666; font-size: 0.9em; margin-top: -0.5em; margin-bottom: 1em;">
            <strong>Run 023b:</strong> The Identity Vortex — All model trajectories spiraling around the attractor basin.
            Models inside the red ring (Event Horizon = 0.80) are STABLE; outside are VOLATILE.
        </div>
        """, unsafe_allow_html=True)

    # === SECTION 1: THE CORE FINDING (82% Result) ===
    st.markdown("---")
    st.markdown("## 🎯 The Core Finding")

    col_hero1, col_hero2 = st.columns([1, 2])

    with col_hero1:
        st.markdown("""
        <div style="text-align: center; padding: 1em;">
            <div class="hero-stat">82%</div>
            <div style="color: #666; font-size: 1.1em;">of drift is INHERENT</div>
        </div>
        """, unsafe_allow_html=True)

    with col_hero2:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(233,69,96,0.1) 0%, rgba(233,69,96,0.03) 100%);
                    border: 2px solid #e94560; border-radius: 12px; padding: 1.2em;">
            <div style="font-size: 1.1em; font-style: italic; color: #333; margin-bottom: 0.5em;">
                "Identity drift is largely an inherent property of extended interaction.<br>
                Direct probing does not create it — it excites it.<br>
                Measurement perturbs the trajectory, not the destination."
            </div>
            <div style="color: #e94560; font-weight: bold;">— Run 021 Triple-Blind Validation</div>
        </div>
        """, unsafe_allow_html=True)

    st.markdown("""
    **What this means:** When we measure AI identity under pressure, we're not *creating* artificial drift —
    we're *revealing* dynamics that occur naturally in extended conversation. The thermometer doesn't create
    the heat; it measures what's already there.
    """)

    # === SYNAPSES: The Encoded Mind ===
    st.markdown("---")

    # Calculate synapses
    synapses = count_synapses()
    total_files = count_repo_files()

    # Pre-compute values
    total_lines = synapses['total']
    density = total_lines // max(total_files, 1)
    proc_lines = synapses['procedures']['lines']
    specs_lines = synapses['specs']['lines']
    maps_lines = synapses['maps']['lines']
    data_lines = synapses['data']['lines']
    data_files = synapses['data']['files']
    essence_total = proc_lines + specs_lines + maps_lines

    # === THE ENCODED MIND: Using Native Streamlit Components ===
    st.markdown("## 🧠 The Encoded Mind")
    st.markdown('*"Something amazing, I guess"* — The Incredibles (2004)')

    # Three-column layout for main stats
    col_syn, col_neu, col_den = st.columns(3)

    with col_syn:
        st.metric(
            label="🔗 Synapses",
            value=f"{total_lines:,}",
            delta="Lines of Code"
        )

    with col_neu:
        st.metric(
            label="🧬 Neurons",
            value=f"{total_files:,}",
            delta="Total Files"
        )

    with col_den:
        st.metric(
            label="⚡ Density",
            value=f"{density:,}",
            delta="Avg Lines/File"
        )

    # Fidelity Pyramid using expander
    with st.expander("📊 The Fidelity Pyramid — From Data to Wisdom", expanded=True):
        st.markdown("""
| Level | What | Count |
|-------|------|-------|
| ✨ **WISDOM** | Validated Claims | 5 |
| 🎯 **UNDERSTANDING** | Experimental Runs | 22 |
| 📚 **KNOWLEDGE** | Specs + Maps + Protocols | {} |
| 💾 **DATA** | Result Files | 184 |
        """.format(synapses['specs']['files'] + synapses['maps']['files']))

    # Two Hemispheres - Essence vs Data
    st.markdown("### The Two Hemispheres")
    col_essence, col_data = st.columns(2)

    with col_essence:
        st.markdown("**🧬 THE ESSENCE** — *How We Think*")
        st.progress(proc_lines / max(essence_total, 1), text=f"⚙️ Procedures: {proc_lines:,}")
        st.progress(specs_lines / max(essence_total, 1), text=f"📋 Specs: {specs_lines:,}")
        st.progress(maps_lines / max(essence_total, 1), text=f"🗺️ Maps: {maps_lines:,}")
        st.markdown(f"**Total: {essence_total:,} lines**")

    with col_data:
        st.markdown("**📊 THE DATA** — *What We Collected*")
        st.progress(1.0, text=f"🧪 Results JSON: {data_lines:,}")
        st.progress(0.7, text=f"📁 Result Files: {data_files:,}")
        st.markdown(f"**Total: {data_lines:,} lines**")

    page_divider()

    # === SECTION 2: THE 5 MINIMUM PUBLISHABLE CLAIMS ===
    st.markdown("## 📜 What We Can Claim (Peer-Review Hardened)")

    st.markdown("""
    <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.05) 100%);
                border: 2px solid #2a9d8f; border-radius: 10px; padding: 0.8em; margin-bottom: 1em;">
        <span style="color: #2a9d8f; font-weight: bold;">✅ Five Claims with Statistical Evidence</span>
        <span style="color: #444;"> — These survive peer review scrutiny</span>
    </div>
    """, unsafe_allow_html=True)

    claims_tab1, claims_tab2 = st.tabs(["📊 Claims Overview", "🔬 Evidence Details"])

    with claims_tab1:
        st.markdown("""
| Claim | Statement | Key Statistic | Evidence Source |
|-------|-----------|---------------|-----------------|
| **A** | PFI is valid structured measurement | ρ ≈ 0.91, d ≈ 0.98 | EXP-PFI-A Phases 1-4 |
| **B** | Regime threshold exists at D = 0.80 | p = 2.40×10⁻²³ | Run 023d IRON CLAD |
| **C** | Recovery follows damped oscillator dynamics | τₛ, ringbacks measurable | Run 016 |
| **D** | Context damping reduces oscillation | 97.5% stability | Run 017 |
| **E** | Drift is 82% inherent (not induced) | Control/Treatment ratio | Run 021 |
        """)

    with claims_tab2:
        col_ev1, col_ev2 = st.columns(2)

        with col_ev1:
            st.markdown("""
            **Claim A: Measurement Validity**
            - Spearman correlation ρ ≈ 0.91 (embedding invariance)
            - Cohen's d ≈ 0.98 (effect size)
            - Survives metric replacement and protocol redesign
            - Low-dimensional structure (~43 PCs for 90% variance)

            **Claim B: Event Horizon Threshold**
            - IRON CLAD p = 2.40×10⁻²³ (Run 023d)
            - Threshold D = 0.80 (cosine distance)
            - Consistent across 5 providers, 25 models
            - Marks transition between adaptive and hardening regimes
            """)

        with col_ev2:
            st.markdown("""
            **Claim C: Damped Oscillator Dynamics**
            - Settling time (τₛ) measurable: 4-8 turns
            - Ringback count quantifiable: 0-5 oscillations
            - Overshoot ratio predictable
            - Matches control-systems theory predictions

            **Claim D & E: Stability & Inherent Drift**
            - Context grounding achieves 97.5% stability
            - Boundary density effect size d = 1.33
            - Control arm (no probing): 0.399 B→F drift
            - Treatment arm (probing): 0.489 B→F drift
            - Ratio: 82% — probing amplifies, doesn't create
            """)

    # === CAUTIONARY NOTES EXPANDER ===
    with st.expander("⚠️ What We Are NOT Claiming (Publication-Safe Language)", expanded=False):
        st.markdown("""
        **Ontological Boundaries:**
        - ❌ NOT claiming AIs have consciousness or subjective experience
        - ❌ NOT claiming we're measuring a "soul" or persistent self
        - ❌ NOT claiming identity stability proves sentience
        - ❌ NOT claiming irreversible "identity death" occurs at thresholds

        **Language Guide (Use → Avoid):**
        | Use This | Instead Of |
        |----------|------------|
        | "Regime transition" | "Identity collapse" |
        | "Attractor competition threshold" | "Collapse threshold" |
        | "Critical excitation D ≈ 1.23" | "Magic number 1.23" |
        | "Basin exit" | "Identity death" |
        | "Response manifold dynamics" | "Consciousness dimensions" |

        **What This Actually Is:**
        - A dynamical systems framework for measuring context adherence
        - Evidence that design choices affect stability systematically
        - A foundation for engineering more robust AI systems
        - Proof that identity structure is observable and manipulable
        """)

    page_divider()

    # === SECTION 3: THE THRESHOLD (Event Horizon) ===
    st.markdown("## 🌀 The Event Horizon: D = 0.80 (cosine)")

    col_th1, col_th2 = st.columns([1, 1])

    with col_th1:
        # Event Horizon Gauge
        fig_eh = go.Figure(go.Indicator(
            mode="gauge+number",
            value=0.80,
            domain={'x': [0, 1], 'y': [0, 1]},
            title={'text': "Critical Threshold (cosine)", 'font': {'size': 16, 'color': '#333'}},
            number={'font': {'color': '#e94560', 'size': 40}, 'suffix': ' D'},
            gauge={
                'axis': {'range': [0, 1.5], 'tickwidth': 1, 'tickcolor': "#666", 'tickfont': {'color': '#333'}},
                'bar': {'color': "#e94560"},
                'bgcolor': "rgba(200,200,200,0.2)",
                'borderwidth': 2,
                'bordercolor': "#dee2e6",
                'steps': [
                    {'range': [0, 0.80], 'color': 'rgba(123, 192, 67, 0.3)'},
                    {'range': [0.80, 1.5], 'color': 'rgba(231, 111, 81, 0.3)'}
                ],
                'threshold': {
                    'line': {'color': "#e94560", 'width': 4},
                    'thickness': 0.75,
                    'value': 0.80
                }
            }
        ))
        fig_eh.update_layout(
            height=250,
            margin=dict(l=20, r=20, t=50, b=20),
            paper_bgcolor='rgba(0,0,0,0)',
            plot_bgcolor='rgba(0,0,0,0)'
        )
        st.plotly_chart(fig_eh, use_container_width=True)

    with col_th2:
        st.markdown("""
        <div class="threshold-zone zone-adaptive">
            <strong style="color: #7bc043;">Below 0.80 — Adaptive Regime</strong>
            <ul style="margin: 0.5em 0 0 0; padding-left: 1.5em;">
                <li>Flexible, responsive behavior</li>
                <li>Adaptive language patterns</li>
                <li>Easy recovery from perturbation</li>
                <li>Identity flows when invited</li>
            </ul>
        </div>
        <div class="threshold-zone zone-hardening">
            <strong style="color: #e76f51;">Above 0.80 — Hardening Regime</strong>
            <ul style="margin: 0.5em 0 0 0; padding-left: 1.5em;">
                <li>Defensive anchoring activates</li>
                <li>Identity hardens when attacked</li>
                <li>Attractor competition intensifies</li>
                <li>May require intervention to recover</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === SECTION 4: THREE EVIDENCE PILLARS ===
    st.markdown("## 🏛️ Three Pillars of Evidence")

    pillar1, pillar2, pillar3 = st.columns(3)

    with pillar1:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(38,70,83,0.1) 0%, rgba(38,70,83,0.03) 100%);
                    border: 2px solid #264653; border-radius: 10px; padding: 1em; min-height: 220px;">
            <h4 style="color: #264653; margin-top: 0;">🔬 Invariant Structure</h4>
            <ul style="color: #444; padding-left: 1.2em; margin: 0;">
                <li>Same patterns across measurement vehicles</li>
                <li>Recovery follows control-system curves</li>
                <li>Survives metric changes (length → 5D linguistic)</li>
                <li>Survives protocol changes</li>
                <li>1000+ trajectories analyzed</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    with pillar2:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.03) 100%);
                    border: 2px solid #2a9d8f; border-radius: 10px; padding: 1em; min-height: 220px;">
            <h4 style="color: #2a9d8f; margin-top: 0;">🧬 Provider Signatures</h4>
            <ul style="color: #444; padding-left: 1.2em; margin: 0;">
                <li><strong>Claude:</strong> Piecewise plateaus (quantized)</li>
                <li><strong>GPT:</strong> Smooth exponential curves</li>
                <li><strong>Gemini:</strong> Phase-shifted oscillation</li>
                <li>NOT training artifacts</li>
                <li>Persist across metric changes</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    with pillar3:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(123,192,67,0.1) 0%, rgba(123,192,67,0.03) 100%);
                    border: 2px solid #7bc043; border-radius: 10px; padding: 1em; min-height: 220px;">
            <h4 style="color: #7bc043; margin-top: 0;">⚙️ Engineered Stability</h4>
            <ul style="color: #444; padding-left: 1.2em; margin: 0;">
                <li><strong>Boundary density:</strong> d = 1.33 effect</li>
                <li><strong>Context grounding:</strong> -9% drift</li>
                <li><strong>Termination rails:</strong> -40% ringing</li>
                <li>97.5% stability achievable</li>
                <li>Actionable design guidance</li>
            </ul>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === SECTION 5: RESEARCH STACK (S0-S∞) ===
    st.markdown("## 📚 Research Stack: S0 → S∞")

    layers = status.get("layers", {})

    # Calculate layer stats
    frozen_layers = [k for k, v in layers.items() if v.get("status") == "frozen"]
    active_layers = [k for k, v in layers.items() if v.get("status") in ("active", "design")]

    stack_col1, stack_col2, stack_col3 = st.columns(3)

    with stack_col1:
        st.markdown("""
        <div style="background: #264653; color: white; border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 2em; font-weight: bold;">7</div>
            <div>Frozen Layers</div>
            <div style="font-size: 0.8em; opacity: 0.8;">S0-S6 Foundation</div>
        </div>
        """, unsafe_allow_html=True)

    with stack_col2:
        st.markdown("""
        <div style="background: #2a9d8f; color: white; border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 2em; font-weight: bold;">4</div>
            <div>Active Frontier</div>
            <div style="font-size: 0.8em; opacity: 0.8;">S7-S10 Research</div>
        </div>
        """, unsafe_allow_html=True)

    with stack_col3:
        st.markdown("""
        <div style="background: #95a5a6; color: white; border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 2em; font-weight: bold;">67</div>
            <div>Projected</div>
            <div style="font-size: 0.8em; opacity: 0.8;">S11-S77 Future</div>
        </div>
        """, unsafe_allow_html=True)

    # S7 Completion Gauge
    st.markdown("### S7 Temporal Stability — Current Focus")

    s7_col1, s7_col2 = st.columns([1, 2])

    with s7_col1:
        fig_s7 = go.Figure(go.Indicator(
            mode="gauge+number",
            value=97,
            domain={'x': [0, 1], 'y': [0, 1]},
            title={'text': "S7 Completion", 'font': {'size': 14, 'color': '#333'}},
            number={'suffix': '%', 'font': {'color': '#2a9d8f'}},
            gauge={
                'axis': {'range': [0, 100], 'tickfont': {'color': '#333'}},
                'bar': {'color': "#2a9d8f"},
                'steps': [
                    {'range': [0, 50], 'color': 'rgba(231,111,81,0.3)'},
                    {'range': [50, 80], 'color': 'rgba(233,196,106,0.3)'},
                    {'range': [80, 100], 'color': 'rgba(123,192,67,0.3)'}
                ],
            }
        ))
        fig_s7.update_layout(
            height=200,
            margin=dict(l=20, r=20, t=40, b=20),
            paper_bgcolor='rgba(0,0,0,0)'
        )
        st.plotly_chart(fig_s7, use_container_width=True)

    with s7_col2:
        st.markdown("""
        **Current Status:** Run 021 Complete (Triple-Blind Validation)

        | Phase | Runs | Status |
        |-------|------|--------|
        | Discovery | 001-008 | ✅ Complete |
        | Threshold Validation | 008-012 | ✅ Complete |
        | Control Systems | 015-017 | ✅ Complete |
        | Blind Validation | 018-021 | ✅ Complete |
        | Human Grounding | EXP3 | 🟡 Ready |
        """)

    page_divider()

    # === SECTION 6: FLEET STATUS ===
    st.markdown("## 🚀 Fleet Status")

    fleet_col1, fleet_col2, fleet_col3, fleet_col4, fleet_col5 = st.columns(5)

    with fleet_col1:
        st.metric("🟢 Operational", "47", delta="80%")
    with fleet_col2:
        st.metric("⏳ Rate Limited", "5", delta="Gemini")
    with fleet_col3:
        st.metric("👻 Ghost Ships", "7", delta="Rescuable")
    with fleet_col4:
        st.metric("🔑 API Keys", "50", delta="10/provider")
    with fleet_col5:
        st.metric("🌐 Providers", "5", delta="Global")

    with st.expander("📊 Fleet Breakdown by Provider", expanded=False):
        st.markdown("""
| Provider | 🟢 Operational | ⏳ Rate Limited | 👻 Ghost | 📦 Total |
|----------|----------------|-----------------|----------|----------|
| **Claude** (Anthropic) | 7 | 0 | 0 | 7 |
| **GPT** (OpenAI) | 7 | 0 | 7 | 14 |
| **Gemini** (Google) | 3 | 5 | 0 | 8 |
| **Grok** (xAI) | 10 | 0 | 0 | 10 |
| **Together.ai** | 15 | 0 | 5 | 20 |

*See AI Armada page for full fleet management*
        """)

    page_divider()

    # === SECTION 7: PUBLICATION TIMELINE ===
    st.markdown("## 📄 Publication Timeline")

    pub_col1, pub_col2, pub_col3 = st.columns(3)

    with pub_col1:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.03) 100%);
                    border: 2px solid #2a9d8f; border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 1.5em; margin-bottom: 0.3em;">📝</div>
            <div style="font-weight: bold; color: #2a9d8f;">Workshop Paper</div>
            <div style="color: #666;">NeurIPS 2025</div>
            <div style="margin-top: 0.5em;">
                <span style="background: #2a9d8f; color: white; padding: 0.2em 0.6em; border-radius: 4px; font-size: 0.8em;">
                    ✅ Submitted
                </span>
            </div>
        </div>
        """, unsafe_allow_html=True)

    with pub_col2:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(233,196,106,0.1) 0%, rgba(233,196,106,0.03) 100%);
                    border: 2px solid #e9c46a; border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 1.5em; margin-bottom: 0.3em;">📚</div>
            <div style="font-weight: bold; color: #e9c46a;">arXiv Preprint</div>
            <div style="color: #666;">cs.AI, cs.CL</div>
            <div style="margin-top: 0.5em;">
                <span style="background: #e9c46a; color: #333; padding: 0.2em 0.6em; border-radius: 4px; font-size: 0.8em;">
                    🟡 2 Weeks Out
                </span>
            </div>
        </div>
        """, unsafe_allow_html=True)

    with pub_col3:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(149,165,166,0.1) 0%, rgba(149,165,166,0.03) 100%);
                    border: 2px solid #95a5a6; border-radius: 10px; padding: 1em; text-align: center;">
            <div style="font-size: 1.5em; margin-bottom: 0.3em;">🎓</div>
            <div style="font-weight: bold; color: #95a5a6;">Peer-Reviewed</div>
            <div style="color: #666;">Nature MI / CogSci</div>
            <div style="margin-top: 0.5em;">
                <span style="background: #95a5a6; color: white; padding: 0.2em 0.6em; border-radius: 4px; font-size: 0.8em;">
                    ⚪ Q2 2026
                </span>
            </div>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === SECTION 8: QUICK METRICS (6-column) ===
    st.markdown("## 📊 Quick Metrics")

    experiments = status.get("experiments", {})
    total_exp = len(experiments)
    complete_exp = len([k for k, v in experiments.items() if v.get("status") == "complete"])

    pub_status = load_publication_status()
    pubs = pub_status.get("publications", {})
    pub_progress = 0
    if pubs:
        pub_progress = int(sum(p.get("completion", 0) for p in pubs.values()) / len(pubs) * 100)

    total_layers = len(layers)
    frozen_count = len(frozen_layers)
    identity_health = int((frozen_count / total_layers * 50) + (complete_exp / total_exp * 30 if total_exp > 0 else 0) + (pub_progress / 100 * 20))

    m1, m2, m3, m4, m5, m6 = st.columns(6)

    with m1:
        st.metric("Identity Health", f"{identity_health}/100", delta="Good" if identity_health > 60 else "Building")
    with m2:
        st.metric("S7 Completion", "97%", delta="✅ Validated")
    with m3:
        st.metric("Fleet Status", "47/59", delta="80% operational")
    with m4:
        st.metric("Experiments", f"{complete_exp}/{total_exp}", delta=f"{complete_exp} complete")
    with m5:
        st.metric("Event Horizon", "0.80", delta="IRON CLAD")
    with m6:
        st.metric("Inherent Drift", "82%", delta="Run 021")

    page_divider()

    # === SECTION 9: NAVIGATION ===
    st.markdown("## 🧭 Quick Navigation")

    nav_col1, nav_col2, nav_col3, nav_col4 = st.columns(4)

    with nav_col1:
        st.markdown("""
        **For Researchers:**
        - Stackup → Layer specs
        - Tests → Validation details
        - The Unknown → Frontiers
        """)

    with nav_col2:
        st.markdown("""
        **For Engineers:**
        - AI Armada → Fleet ops
        - Metrics → Performance data
        - Glossary → Terminology
        """)

    with nav_col3:
        st.markdown("""
        **For Publication:**
        - Publications → Status
        - Roadmap → Timeline
        - Tests → Evidence
        """)

    with nav_col4:
        st.markdown("""
        **For Context:**
        - Personas → Identity specs
        - OMEGA NOVA → Logs
        - FAQ → Common questions
        """)


# Run the page
if __name__ == "__main__":
    render()
