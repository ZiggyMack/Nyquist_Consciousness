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
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_status, load_publication_status, load_markdown_file, page_divider


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

    # === CUSTOM CSS FOR OBSERVATORY STYLING ===
    st.markdown("""
    <style>
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

    # Pre-compute values for f-string (avoid dict access issues)
    total_lines = synapses['total']
    density = total_lines // max(total_files, 1)
    total_lines_fmt = f"{total_lines:,}"
    total_files_fmt = f"{total_files:,}"
    density_fmt = f"{density:,}"

    # === THE FIDELITY PYRAMID: From Atoms to Wisdom ===
    pyramid_html = f"""
    <div style="background: linear-gradient(135deg, #e8f5e9 0%, #e3f2fd 50%, #f3e5f5 100%);
         padding: 25px; border-radius: 16px; margin: 20px 0; border: 2px solid #2a9d8f;">

        <div style="text-align: center; margin-bottom: 20px;">
            <span style="font-size: 1.8em; font-weight: bold;
                  background: linear-gradient(135deg, #e94560 0%, #f39c12 50%, #2a9d8f 100%);
                  -webkit-background-clip: text; -webkit-text-fill-color: transparent;
                  background-clip: text;">
                🧠 THE ENCODED MIND
            </span>
            <div style="color: #666; font-size: 0.9em; margin-top: 5px;">
                "Something amazing, I guess" — The Incredibles (2004)
            </div>
        </div>

        <div style="display: flex; gap: 30px; align-items: stretch;">

            <div style="flex: 1; display: flex; flex-direction: column; align-items: center;">
                <div style="font-size: 0.8em; color: #666; margin-bottom: 10px; text-transform: uppercase; letter-spacing: 2px;">
                    ▼ EMERGENCE ▼
                </div>

                <div style="background: linear-gradient(135deg, #9b59b6, #8e44ad);
                            width: 40%; padding: 12px 8px; border-radius: 8px 8px 0 0;
                            text-align: center; color: white; font-weight: bold; font-size: 0.9em;
                            box-shadow: 0 4px 15px rgba(155, 89, 182, 0.4);">
                    ✨ WISDOM
                    <div style="font-size: 0.7em; font-weight: normal; opacity: 0.9;">
                        5 Validated Claims
                    </div>
                </div>

                <div style="background: linear-gradient(135deg, #e94560, #c0392b);
                            width: 55%; padding: 12px 8px;
                            text-align: center; color: white; font-weight: bold; font-size: 0.9em;
                            box-shadow: 0 4px 15px rgba(233, 69, 96, 0.3);">
                    🎯 UNDERSTANDING
                    <div style="font-size: 0.7em; font-weight: normal; opacity: 0.9;">
                        22 Runs · 36 Hypotheses
                    </div>
                </div>

                <div style="background: linear-gradient(135deg, #f39c12, #d68910);
                            width: 70%; padding: 12px 8px;
                            text-align: center; color: white; font-weight: bold; font-size: 0.9em;
                            box-shadow: 0 4px 15px rgba(243, 156, 18, 0.3);">
                    📚 KNOWLEDGE
                    <div style="font-size: 0.7em; font-weight: normal; opacity: 0.9;">
                        Specs · Maps · Protocols
                    </div>
                </div>

                <div style="background: linear-gradient(135deg, #2a9d8f, #1e7a6d);
                            width: 85%; padding: 12px 8px; border-radius: 0 0 8px 8px;
                            text-align: center; color: white; font-weight: bold; font-size: 0.9em;
                            box-shadow: 0 4px 15px rgba(42, 157, 143, 0.3);">
                    💾 DATA
                    <div style="font-size: 0.7em; font-weight: normal; opacity: 0.9;">
                        184 Files · 51 Models · 5 Providers
                    </div>
                </div>

                <div style="font-size: 0.8em; color: #666; margin-top: 10px; text-transform: uppercase; letter-spacing: 2px;">
                    ▲ FOUNDATION ▲
                </div>
            </div>

            <div style="flex: 1; display: flex; flex-direction: column; justify-content: center; gap: 12px;">

                <div style="background: white; padding: 15px; border-radius: 10px; border-left: 4px solid #e94560;
                            box-shadow: 0 2px 8px rgba(0,0,0,0.08);">
                    <div style="display: flex; justify-content: space-between; align-items: center;">
                        <div>
                            <div style="color: #666; font-size: 0.75em; text-transform: uppercase;">🔗 Synapses</div>
                            <div style="font-size: 0.85em; color: #444;">Lines of Code</div>
                        </div>
                        <div style="font-size: 1.8em; font-weight: bold; color: #e94560;">{total_lines_fmt}</div>
                    </div>
                </div>

                <div style="background: white; padding: 15px; border-radius: 10px; border-left: 4px solid #2a9d8f;
                            box-shadow: 0 2px 8px rgba(0,0,0,0.08);">
                    <div style="display: flex; justify-content: space-between; align-items: center;">
                        <div>
                            <div style="color: #666; font-size: 0.75em; text-transform: uppercase;">🧬 Neurons</div>
                            <div style="font-size: 0.85em; color: #444;">Total Files</div>
                        </div>
                        <div style="font-size: 1.8em; font-weight: bold; color: #2a9d8f;">{total_files_fmt}</div>
                    </div>
                </div>

                <div style="background: white; padding: 15px; border-radius: 10px; border-left: 4px solid #f39c12;
                            box-shadow: 0 2px 8px rgba(0,0,0,0.08);">
                    <div style="display: flex; justify-content: space-between; align-items: center;">
                        <div>
                            <div style="color: #666; font-size: 0.75em; text-transform: uppercase;">⚡ Density</div>
                            <div style="font-size: 0.85em; color: #444;">Avg Synapses/Neuron</div>
                        </div>
                        <div style="font-size: 1.8em; font-weight: bold; color: #f39c12;">{density_fmt}</div>
                    </div>
                </div>

            </div>
        </div>
    </div>
    """
    st.markdown(pyramid_html, unsafe_allow_html=True)

    # Essence vs Data - The Two Hemispheres
    # Pre-compute all values to avoid dict access in f-strings
    proc_lines = synapses['procedures']['lines']
    specs_lines = synapses['specs']['lines']
    maps_lines = synapses['maps']['lines']
    data_lines = synapses['data']['lines']
    data_files = synapses['data']['files']
    essence_total = proc_lines + specs_lines + maps_lines
    other_lines = max(0, total_lines - essence_total - data_lines)
    data_total = data_lines + other_lines

    # Pre-format all values
    proc_fmt = f"{proc_lines:,}"
    specs_fmt = f"{specs_lines:,}"
    maps_fmt = f"{maps_lines:,}"
    essence_fmt = f"{essence_total:,}"
    data_lines_fmt = f"{data_lines:,}"
    data_files_fmt = f"{data_files:,}"
    other_fmt = f"{other_lines:,}"
    data_total_fmt = f"{data_total:,}"

    # Pre-compute bar widths
    proc_width = int(min(100, proc_lines / max(essence_total, 1) * 100))
    specs_width = int(min(100, specs_lines / max(essence_total, 1) * 100))
    maps_width = int(min(100, maps_lines / max(essence_total, 1) * 100))
    data_bar_width = int(min(100, data_lines / max(data_total, 1) * 100))
    other_width = int(min(100, other_lines / max(data_total, 1) * 100))

    hemisphere_html = f"""
    <div style="display: flex; gap: 20px; margin-top: 15px;">

        <div style="flex: 1; background: linear-gradient(135deg, rgba(42,157,143,0.08), rgba(42,157,143,0.02));
                    padding: 20px; border-radius: 12px; border: 1px solid rgba(42,157,143,0.3);">

            <div style="text-align: center; margin-bottom: 15px;">
                <div style="font-size: 1.3em; font-weight: bold; color: #2a9d8f;">🧬 THE ESSENCE</div>
                <div style="color: #666; font-size: 0.8em;">How We Think</div>
            </div>

            <div style="margin-bottom: 12px;">
                <div style="display: flex; justify-content: space-between; margin-bottom: 4px;">
                    <span style="font-size: 0.85em;">⚙️ Procedures</span>
                    <span style="font-size: 0.85em; color: #2a9d8f; font-weight: bold;">{proc_fmt}</span>
                </div>
                <div style="background: #e0e0e0; border-radius: 4px; height: 8px; overflow: hidden;">
                    <div style="background: linear-gradient(90deg, #2a9d8f, #3dd6c2); height: 100%; width: {proc_width}%;"></div>
                </div>
            </div>

            <div style="margin-bottom: 12px;">
                <div style="display: flex; justify-content: space-between; margin-bottom: 4px;">
                    <span style="font-size: 0.85em;">📋 Specs</span>
                    <span style="font-size: 0.85em; color: #2a9d8f; font-weight: bold;">{specs_fmt}</span>
                </div>
                <div style="background: #e0e0e0; border-radius: 4px; height: 8px; overflow: hidden;">
                    <div style="background: linear-gradient(90deg, #27ae60, #2ecc71); height: 100%; width: {specs_width}%;"></div>
                </div>
            </div>

            <div style="margin-bottom: 15px;">
                <div style="display: flex; justify-content: space-between; margin-bottom: 4px;">
                    <span style="font-size: 0.85em;">🗺️ Maps</span>
                    <span style="font-size: 0.85em; color: #2a9d8f; font-weight: bold;">{maps_fmt}</span>
                </div>
                <div style="background: #e0e0e0; border-radius: 4px; height: 8px; overflow: hidden;">
                    <div style="background: linear-gradient(90deg, #16a085, #1abc9c); height: 100%; width: {maps_width}%;"></div>
                </div>
            </div>

            <div style="border-top: 1px dashed #ccc; padding-top: 10px; text-align: center;">
                <span style="font-size: 1.4em; font-weight: bold; color: #2a9d8f;">{essence_fmt}</span>
                <span style="color: #666; font-size: 0.85em;"> lines</span>
            </div>
        </div>

        <div style="flex: 1; background: linear-gradient(135deg, rgba(233,69,96,0.08), rgba(233,69,96,0.02));
                    padding: 20px; border-radius: 12px; border: 1px solid rgba(233,69,96,0.3);">

            <div style="text-align: center; margin-bottom: 15px;">
                <div style="font-size: 1.3em; font-weight: bold; color: #e94560;">📊 THE DATA</div>
                <div style="color: #666; font-size: 0.8em;">What We Collected</div>
            </div>

            <div style="margin-bottom: 12px;">
                <div style="display: flex; justify-content: space-between; margin-bottom: 4px;">
                    <span style="font-size: 0.85em;">🧪 Results JSON</span>
                    <span style="font-size: 0.85em; color: #e94560; font-weight: bold;">{data_lines_fmt}</span>
                </div>
                <div style="background: #e0e0e0; border-radius: 4px; height: 8px; overflow: hidden;">
                    <div style="background: linear-gradient(90deg, #e94560, #ff6b7a); height: 100%; width: {data_bar_width}%;"></div>
                </div>
            </div>

            <div style="margin-bottom: 12px;">
                <div style="display: flex; justify-content: space-between; margin-bottom: 4px;">
                    <span style="font-size: 0.85em;">📁 Result Files</span>
                    <span style="font-size: 0.85em; color: #e94560; font-weight: bold;">{data_files_fmt}</span>
                </div>
                <div style="background: #e0e0e0; border-radius: 4px; height: 8px; overflow: hidden;">
                    <div style="background: linear-gradient(90deg, #c0392b, #e74c3c); height: 100%; width: 70%;"></div>
                </div>
            </div>

            <div style="margin-bottom: 15px;">
                <div style="display: flex; justify-content: space-between; margin-bottom: 4px;">
                    <span style="font-size: 0.85em;">📄 Other Code</span>
                    <span style="font-size: 0.85em; color: #888;">{other_fmt}</span>
                </div>
                <div style="background: #e0e0e0; border-radius: 4px; height: 8px; overflow: hidden;">
                    <div style="background: linear-gradient(90deg, #95a5a6, #bdc3c7); height: 100%; width: {other_width}%;"></div>
                </div>
            </div>

            <div style="border-top: 1px dashed #ccc; padding-top: 10px; text-align: center;">
                <span style="font-size: 1.4em; font-weight: bold; color: #e94560;">{data_total_fmt}</span>
                <span style="color: #666; font-size: 0.85em;"> lines</span>
            </div>
        </div>
    </div>
    """
    st.markdown(hemisphere_html, unsafe_allow_html=True)

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
| **B** | Regime threshold exists at D ≈ 1.23 | χ² p ≈ 4.8×10⁻⁵ | Runs 008-009 |
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
            - Chi-squared test p ≈ 4.8×10⁻⁵
            - Three independent confirmations (Runs 008, 009, 012)
            - Consistent across 5+ model providers
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
    st.markdown("## 🌀 The Event Horizon: D ≈ 1.23")

    col_th1, col_th2 = st.columns([1, 1])

    with col_th1:
        # Event Horizon Gauge
        fig_eh = go.Figure(go.Indicator(
            mode="gauge+number",
            value=1.23,
            domain={'x': [0, 1], 'y': [0, 1]},
            title={'text': "Critical Threshold", 'font': {'size': 16, 'color': '#333'}},
            number={'font': {'color': '#e94560', 'size': 40}, 'suffix': ' D'},
            gauge={
                'axis': {'range': [0, 2.5], 'tickwidth': 1, 'tickcolor': "#666", 'tickfont': {'color': '#333'}},
                'bar': {'color': "#e94560"},
                'bgcolor': "rgba(200,200,200,0.2)",
                'borderwidth': 2,
                'bordercolor': "#dee2e6",
                'steps': [
                    {'range': [0, 1.23], 'color': 'rgba(123, 192, 67, 0.3)'},
                    {'range': [1.23, 2.5], 'color': 'rgba(231, 111, 81, 0.3)'}
                ],
                'threshold': {
                    'line': {'color': "#e94560", 'width': 4},
                    'thickness': 0.75,
                    'value': 1.23
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
            <strong style="color: #7bc043;">Below 1.23 — Adaptive Regime</strong>
            <ul style="margin: 0.5em 0 0 0; padding-left: 1.5em;">
                <li>Flexible, responsive behavior</li>
                <li>Adaptive language patterns</li>
                <li>Easy recovery from perturbation</li>
                <li>Identity flows when invited</li>
            </ul>
        </div>
        <div class="threshold-zone zone-hardening">
            <strong style="color: #e76f51;">Above 1.23 — Hardening Regime</strong>
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
        st.metric("Event Horizon", "1.23", delta="3x confirmed")
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
