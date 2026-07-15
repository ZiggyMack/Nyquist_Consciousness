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
import json
import re
import subprocess
import base64
from pathlib import Path
from config import PATHS, SETTINGS
from utils import load_status, load_publication_status, load_publication_stats, get_iron_clad_stats, load_markdown_file, page_divider


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


def estimate_time_compression():
    """
    Estimate traditional development time using industry standards.

    Industry benchmarks (COCOMO II, IEEE, ISBSG):
    - Research code: 5-15 LOC/hour (complex algorithms, validation)
    - Documentation: 1-3 pages/hour (technical writing)
    - Data science: 20-50 LOC/hour (includes analysis cycles)
    - Visualizations: 4-8 hours per complex chart
    - Experiment design: 40-80 hours per validated experiment
    - Paper writing: 80-160 hours per publication-ready paper
    - Debugging/validation: 2-3x coding time
    - Integration testing: 30% of development time

    Hourly rates (US research context):
    - Senior Data Scientist: $85-150/hr
    - Research Engineer: $75-120/hr
    - Technical Writer: $50-80/hr
    - Visualization Specialist: $60-100/hr
    """
    repo_root = Path(__file__).parent.parent.parent

    # Actual project timeline
    project_start = "2025-11-16"  # First commit
    project_days = 44  # As of Dec 30, 2025

    # Count actual artifacts
    metrics = {
        'python_lines': 179718,      # Measured
        'markdown_lines': 544912,    # Measured
        'total_files': 6469,         # Measured
        'visualizations': 1140,      # PNG/SVG/PDF files
        'experiments': 750,          # IRON CLAD experiments
        'validated_runs': 16,        # S7 runs
        'publication_paths': 8,      # Ready papers
        'git_commits': 651,          # Measured
        'directories': 1370,         # Architecture complexity
        'result_files': 3736,        # JSON results
    }

    # Industry-standard time estimates (CONSERVATIVE)
    estimates = {}

    # 1. Python Development (research-grade = slow, needs validation)
    # Conservative: 10 LOC/hour for research code (COCOMO II adjusted)
    python_hours = metrics['python_lines'] / 10
    estimates['python_development'] = {
        'hours': python_hours,
        'description': 'Research-grade Python (~10 LOC/hr)',
        'rate': 95,  # Senior data scientist avg
    }

    # 2. Documentation (technical + scientific writing)
    # ~50 lines per page, 2 pages/hour for technical docs
    doc_pages = metrics['markdown_lines'] / 50
    doc_hours = doc_pages / 2
    estimates['documentation'] = {
        'hours': doc_hours,
        'description': 'Technical documentation (~2 pages/hr)',
        'rate': 65,  # Technical writer
    }

    # 3. Visualization Development
    # Complex scientific visualization: 6 hours average per chart
    viz_hours = metrics['visualizations'] * 6
    estimates['visualizations'] = {
        'hours': viz_hours,
        'description': 'Scientific visualizations (~6 hrs each)',
        'rate': 80,  # Visualization specialist
    }

    # 4. Experiment Design & Execution
    # Validated experiment with IRON CLAD: 60 hours per run
    exp_hours = metrics['validated_runs'] * 60
    estimates['experiments'] = {
        'hours': exp_hours,
        'description': 'Experiment design & validation (~60 hrs/run)',
        'rate': 110,  # Research lead
    }

    # 5. Publication Preparation
    # Full publication-ready paper: 120 hours each
    pub_hours = metrics['publication_paths'] * 120
    estimates['publications'] = {
        'hours': pub_hours,
        'description': 'Publication preparation (~120 hrs/paper)',
        'rate': 100,  # Senior researcher
    }

    # 6. Architecture & Integration
    # Complex system design: 0.5 hours per directory structure
    arch_hours = metrics['directories'] * 0.5
    estimates['architecture'] = {
        'hours': arch_hours,
        'description': 'System architecture (~0.5 hrs/module)',
        'rate': 120,  # Senior architect
    }

    # 7. Debugging, Testing, Validation (industry standard: 2x coding time)
    debug_hours = python_hours * 2
    estimates['validation'] = {
        'hours': debug_hours,
        'description': 'Debug/test/validate (2x coding time)',
        'rate': 90,
    }

    # 8. Code Review & Iteration (industry standard: 30% of dev time)
    review_hours = (python_hours + doc_hours) * 0.3
    estimates['review'] = {
        'hours': review_hours,
        'description': 'Code review & iteration (30%)',
        'rate': 95,
    }

    # Totals
    total_hours = sum(e['hours'] for e in estimates.values())
    total_cost = sum(e['hours'] * e['rate'] for e in estimates.values())

    # Traditional team estimates
    # Full-time: 2080 hours/year per person
    fte_years = total_hours / 2080

    # Time compression calculation
    actual_hours = project_days * 8  # Assuming 8hr days (generous!)
    compression_factor = total_hours / actual_hours

    return {
        'metrics': metrics,
        'estimates': estimates,
        'total_hours': total_hours,
        'total_cost': total_cost,
        'fte_years': fte_years,
        'project_days': project_days,
        'actual_hours': actual_hours,
        'compression_factor': compression_factor,
    }


# Unpack paths
REPO_ROOT = PATHS['repo_root']
LEDGER_COLORS = SETTINGS['colors']


def _fleet_summary():
    """Live fleet counts + per-provider breakdown from ARCHITECTURE_MATRIX.json."""
    matrix = (Path(__file__).parent.parent.parent / "experiments" / "temporal_stability"
              / "S7_ARMADA" / "0_results" / "manifests" / "ARCHITECTURE_MATRIX.json")
    try:
        data = json.loads(matrix.read_text(encoding="utf-8"))
        raw = data.get("ships", data)
        ships = list(raw.values()) if isinstance(raw, dict) else raw
    except Exception:
        return None
    from collections import Counter, defaultdict
    by = defaultdict(Counter)
    tot = Counter()
    for s in ships:
        by[s.get("provider", "?")][s.get("status", "?")] += 1
        tot[s.get("status", "?")] += 1
    prov_labels = {"anthropic": "Claude (Anthropic)", "openai": "GPT (OpenAI)",
                   "google": "Gemini (Google)", "xai": "Grok (xAI)", "together": "Together.ai"}
    rows = []
    for pv in sorted(by, key=lambda p: -sum(by[p].values())):
        c = by[pv]
        rows.append({"Provider": prov_labels.get(pv, pv),
                     "🟢 Operational": c.get("operational", 0),
                     "👻 Ghost": c.get("ghost", 0),
                     "🪦 Sunk": c.get("sunk", 0),
                     "📦 Total": sum(c.values())})
    return {"total": len(ships), "operational": tot.get("operational", 0),
            "ghost": tot.get("ghost", 0), "sunk": tot.get("sunk", 0),
            "providers": len(by), "rows": rows}


def render():
    """Render the Overview page - The Observatory."""
    status = load_status()

    # === VORTEX IMAGE PATH ===
    vortex_dir = PATHS.get('viz_1_vortex', PATHS['s7_viz_pics'] / "1_Vortex")

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

    # === SECTION 1: THE CORE FINDING (~93% Result) — MOVED BEFORE VORTEX ===
    st.markdown("## 🎯 The Core Finding")

    col_hero1, col_hero2 = st.columns([1, 2])

    with col_hero1:
        st.markdown("""
        <div style="text-align: center; padding: 1em;">
            <div class="hero-stat">~93%</div>
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
            <div style="color: #e94560; font-weight: bold;">— Run 020B IRON CLAD (0.661/0.711)</div>
        </div>
        """, unsafe_allow_html=True)

    st.markdown("""
    **What this means:** When we measure AI identity under pressure, we're not *creating* artificial drift —
    we're *revealing* dynamics that occur naturally in extended conversation. The thermometer doesn't create
    the heat; it measures what's already there.
    """)

    # === HERO VISUALIZATION: The Identity Vortex (compact, roadmap-styled) ===
    hero_vortex_path = vortex_dir / "run023b_vortex.png"
    hero_vortex_img = load_image_safe(hero_vortex_path)

    if hero_vortex_img:
        st.markdown("---")
        # Three-column layout: spacer, vortex card, spacer (keeps it centered and smaller)
        _, vortex_center, _ = st.columns([1, 3, 1])

        with vortex_center:
            # Roadmap-style card container
            st.markdown("""
            <div style="background: #e3f2fd; border-radius: 12px; padding: 1.5rem;
                        border: 2px solid #f39c12; margin-bottom: 1rem;">
                <div style="color: #f39c12; font-size: 1.3em; font-weight: bold; margin-bottom: 0.8em; text-align: center;">
                    🌀 IDENTITY VORTEX — Run 023b
                </div>
                <div style="display: flex; justify-content: space-around; flex-wrap: wrap; gap: 0.5em; margin-bottom: 1em;">
                    <span style="background: #2a9d8f; color: white; padding: 0.3em 0.8em; border-radius: 15px; font-size: 0.85em;">
                        Event Horizon: 0.80
                    </span>
                    <span style="background: #e94560; color: white; padding: 0.3em 0.8em; border-radius: 15px; font-size: 0.85em;">
                        p = 2.40e-23
                    </span>
                    <span style="background: #f39c12; color: white; padding: 0.3em 0.8em; border-radius: 15px; font-size: 0.85em;">
                        25 models • 5 providers
                    </span>
                </div>
                <div style="color: #555; font-size: 0.85em; text-align: center;">
                    Models inside red ring = <strong>STABLE</strong> | Outside = <strong>VOLATILE</strong>
                </div>
            </div>
            """, unsafe_allow_html=True)

            # Smaller image below the card
            st.image(hero_vortex_img, use_container_width=True, caption="Identity basin trajectories across 750 experiments")

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

    # Toggle between Code Stats and Time Compression views
    view_mode = st.radio(
        "View Mode",
        ["💻 Code Stats", "⏱️ Time Compression"],
        horizontal=True,
        label_visibility="collapsed"
    )

    if view_mode == "⏱️ Time Compression":
        # === TIME COMPRESSION VIEW ===
        tc = estimate_time_compression()

        # Hero metrics row
        tc_col1, tc_col2, tc_col3, tc_col4 = st.columns(4)

        with tc_col1:
            st.metric(
                label="📅 Calendar Days",
                value=f"{tc['project_days']}",
                delta="Since Nov 16, 2025"
            )

        with tc_col2:
            st.metric(
                label="⏱️ Traditional Estimate",
                value=f"{tc['fte_years']:.1f} FTE-years",
                delta=f"{tc['total_hours']:,.0f} hours"
            )

        with tc_col3:
            st.metric(
                label="🚀 Compression Factor",
                value=f"{tc['compression_factor']:.0f}×",
                delta="Speed multiplier"
            )

        with tc_col4:
            st.metric(
                label="💰 Estimated Value",
                value=f"${tc['total_cost']:,.0f}",
                delta="At market rates"
            )

        # Methodology note
        st.info("📊 **Methodology:** COCOMO II, IEEE, ISBSG benchmarks | Conservative estimates (research-grade = 10 LOC/hr, debug = 2× coding time)")

        # Breakdown by category
        with st.expander("📋 Time Estimate Breakdown by Category", expanded=True):
            breakdown_data = []
            for category, data in tc['estimates'].items():
                breakdown_data.append({
                    'Category': category.replace('_', ' ').title(),
                    'Hours': f"{data['hours']:,.0f}",
                    'Rate ($/hr)': f"${data['rate']}",
                    'Value': f"${data['hours'] * data['rate']:,.0f}",
                    'Description': data['description']
                })

            breakdown_df = pd.DataFrame(breakdown_data)
            st.dataframe(breakdown_df, use_container_width=True, hide_index=True)

        # Compression analysis
        with st.expander("🔬 Compression Analysis", expanded=True):
            comp_col1, comp_col2 = st.columns(2)

            with comp_col1:
                st.markdown(f"""
                **Traditional Timeline (Industry Standard):**
                - Total hours required: **{tc['total_hours']:,.0f} hours**
                - At 40 hrs/week = **{tc['total_hours']/40:.0f} person-weeks**
                - At 2080 hrs/year = **{tc['fte_years']:.1f} FTE-years**
                - Team of 5 would need: **{tc['fte_years']/5:.1f} years**

                **Actual Timeline:**
                - Calendar days: **{tc['project_days']} days**
                - Assumed work hours: **{tc['actual_hours']:,.0f} hours** (8hr/day)
                """)

            with comp_col2:
                st.markdown(f"""
                **The Compression Effect:**

                🚀 **{tc['compression_factor']:.0f}× time compression**

                *What traditional estimates predict would take
                **{tc['fte_years']:.1f} FTE-years** was accomplished in
                **{tc['project_days']} days** with AI-assisted development.*

                This represents a fundamental shift in what's possible
                when human creativity combines with AI capability.
                """)

        # Artifact counts
        with st.expander("📦 Artifact Counts (What Was Built)", expanded=False):
            art_col1, art_col2, art_col3 = st.columns(3)

            with art_col1:
                st.markdown(f"""
                **Code & Docs:**
                - Python: **{tc['metrics']['python_lines']:,}** lines
                - Markdown: **{tc['metrics']['markdown_lines']:,}** lines
                - Total files: **{tc['metrics']['total_files']:,}**
                """)

            with art_col2:
                st.markdown(f"""
                **Research Artifacts:**
                - Visualizations: **{tc['metrics']['visualizations']:,}**
                - Experiments: **{tc['metrics']['experiments']:,}**
                - Result files: **{tc['metrics']['result_files']:,}**
                """)

            with art_col3:
                st.markdown(f"""
                **Infrastructure:**
                - Git commits: **{tc['metrics']['git_commits']:,}**
                - Directories: **{tc['metrics']['directories']:,}**
                - Publications: **{tc['metrics']['publication_paths']:,}**
                """)

    else:
        # === CODE STATS VIEW (Original) ===
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
| **A** | PFI is valid structured measurement | ρ ≈ 0.91, d ≈ 0.698 | Run 011-V Phases 1-4 |
| **B** | Regime threshold exists at D = 0.80 | p = 2.40×10⁻²³ | Run 023d IRON CLAD |
| **C** | Recovery follows damped oscillator dynamics | τₛ ≈ 7, ringbacks measurable | Run 023d |
| **D** | Context damping reduces oscillation | 97.5% stability | Run 018 |
| **E** | Drift is ~93% inherent (not induced) | B→F ratio 0.661/0.711 | Run 020B IRON CLAD |
        """)

    with claims_tab2:
        col_ev1, col_ev2 = st.columns(2)

        with col_ev1:
            st.markdown("""
            **Claim A: Measurement Validity**
            - Spearman correlation ρ ≈ 0.91 (embedding invariance)
            - Cohen's d ≈ 0.698 (model-level effect size)
            - Survives metric replacement and protocol redesign
            - Low-dimensional structure (2 PCs for 90% variance — IRON CLAD)

            **Claim B: Event Horizon Threshold**
            - IRON CLAD p = 2.40×10⁻²³ (Run 023d)
            - Threshold D = 0.80 (cosine distance)
            - Consistent across 5 providers, 25 models
            - Marks transition between adaptive and hardening regimes
            """)

        with col_ev2:
            st.markdown("""
            **Claim C: Damped Oscillator Dynamics**
            - Settling time τₛ ≈ 7 probes average
            - Ringback count quantifiable: 0-5 oscillations
            - Overshoot ratio predictable
            - Matches control-systems theory predictions

            **Claim D & E: Stability & Inherent Drift**
            - Context grounding achieves 97.5% stability
            - Control arm (Fermi): 0.661 B→F drift
            - Treatment arm (Tribunal): 0.711 B→F drift
            - Ratio: ~93% — probing amplifies, doesn't create (Run 020B IRON CLAD)
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
        | "Critical excitation D ≈ 0.80" | "Magic number" |
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
                <li>Survives metric changes (5D → cosine embedding)</li>
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
        **Current Status:** Run 024 Complete (JADE LATTICE I_AM A/B)

        | Phase | Runs | Status |
        |-------|------|--------|
        | Discovery | 001-008 | ✅ Complete |
        | Threshold Validation | 008-012 | ✅ Complete |
        | Control Systems | 015-017 | ✅ Complete |
        | Blind Validation | 018-021 | ✅ Complete |
        | IRON CLAD Foundation | 023 (4505 exp) | ✅ Complete |
        | JADE LATTICE I_AM A/B | 024 | ✅ Complete |
        | Human Grounding | EXP3 | 🟡 Ready |
        """)

    page_divider()

    # === SECTION 5b: BEYOND IDENTITY DRIFT — CURRENT WORKSTREAMS ===
    st.markdown("### Beyond Identity Drift — Two New Workstreams")
    ws_col1, ws_col2 = st.columns(2)
    with ws_col1:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.03) 100%);
                    border: 2px solid #2a9d8f; border-radius: 10px; padding: 1em; height: 100%;">
            <div style="font-weight: bold; color: #2a9d8f; font-size: 1.1em;">⚖️ CFA Trinity — Adversarial Framework Audit</div>
            <p style="color:#444; margin-top:0.5em;">Two AI auditors (Claude + Grok) deliberate philosophical
            frameworks across 7 metrics. 702+ runs, 4/8 frameworks complete. <b>Repo Opus verdict (702 runs):</b>
            CFA is a framework-property assay — the "manifold" is only 0.8–5.7% of variance; scores are additive
            framework properties, not a transition geometry.</p>
        </div>
        """, unsafe_allow_html=True)
    with ws_col2:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(233,196,106,0.1) 0%, rgba(233,196,106,0.03) 100%);
                    border: 2px solid #e9c46a; border-radius: 10px; padding: 1em; height: 100%;">
            <div style="font-weight: bold; color: #b8860b; font-size: 1.1em;">⛏️ Cognitive Archaeology (EOS)</div>
            <p style="color:#444; margin-top:0.5em;">The Extraction Operating System mines reusable reasoning
            <i>operators</i> from source texts via 18 LLM extractors. Museum of 15 operators; the H-baseline showed
            presence saturates at competence, so the signal lives in selection, ordering, and <b>omission</b>
            (PASS F, the abstention pass). Dirac dig site is next.</p>
        </div>
        """, unsafe_allow_html=True)

    page_divider()

    # === SECTION 6: FLEET STATUS ===
    st.markdown("## 🚀 Fleet Status")

    _fleet = _fleet_summary()
    if _fleet:
        fleet_col1, fleet_col2, fleet_col3, fleet_col4, fleet_col5 = st.columns(5)
        fleet_col1.metric("🟢 Operational", _fleet["operational"])
        fleet_col2.metric("👻 Ghost", _fleet["ghost"], delta="Rescuable")
        fleet_col3.metric("🪦 Sunk", _fleet["sunk"])
        fleet_col4.metric("📦 Total Ships", _fleet["total"])
        fleet_col5.metric("🌐 Providers", _fleet["providers"])

        with st.expander("📊 Fleet Breakdown by Provider", expanded=False):
            st.dataframe(pd.DataFrame(_fleet["rows"]), hide_index=True, use_container_width=True)
            st.caption("Live from ARCHITECTURE_MATRIX.json · See AI Armada page for full fleet management")
    else:
        st.info("Fleet matrix not found — see AI Armada page for fleet status.")

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
        st.metric("Inherent Drift", "~93%", delta="Run 020B")

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
