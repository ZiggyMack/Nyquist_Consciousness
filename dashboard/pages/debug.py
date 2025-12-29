"""
DEBUG PAGE - Lab Bench & Run Evolution Tracker
==============================================
Keeps track of what was actually tested vs documented.
Tracks metric evolution, probe types, and data vs summary discrepancies.
Essential for maintaining clarity as we iterate through experimental phases.

METHODOLOGY NOTE:
- Current (IRON CLAD): Event Horizon = 0.80 (cosine), p = 2.40e-23 (Run 023d)
- Legacy (Keyword RMS): Event Horizon = 1.23, p = 4.8e-5 (Runs 008-012)
- Historical references to 1.23 reflect the legacy methodology
"""

import streamlit as st
import pandas as pd
from pathlib import Path
from config import PATHS
from utils import page_divider


def render():
    """Render the Debug lab bench page."""

    # Custom CSS
    st.markdown("""
    <style>
    .debug-title {
        font-size: 2.5em;
        font-weight: bold;
        background: linear-gradient(135deg, #ef4444 0%, #b91c1c 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.3em;
    }
    .evolution-card {
        border-radius: 12px;
        padding: 1.5em;
        margin: 1em 0;
        border-left: 4px solid #ef4444;
    }
    .valid-badge {
        background: #22c55e;
        color: white;
        padding: 0.2em 0.6em;
        border-radius: 4px;
        font-size: 0.85em;
    }
    .invalid-badge {
        background: #ef4444;
        color: white;
        padding: 0.2em 0.6em;
        border-radius: 4px;
        font-size: 0.85em;
    }
    .stale-badge {
        background: #f59e0b;
        color: white;
        padding: 0.2em 0.6em;
        border-radius: 4px;
        font-size: 0.85em;
    }
    .context-bare {
        background: #fee2e2;
        padding: 0.2em 0.5em;
        border-radius: 4px;
        color: #991b1b;
    }
    .context-iam {
        background: #dbeafe;
        padding: 0.2em 0.5em;
        border-radius: 4px;
        color: #1e40af;
    }
    .context-full {
        background: #dcfce7;
        padding: 0.2em 0.5em;
        border-radius: 4px;
        color: #166534;
    }
    </style>
    """, unsafe_allow_html=True)

    # === HERO ===
    st.markdown('<div class="debug-title">Debug: Lab Bench</div>', unsafe_allow_html=True)
    st.markdown("*Keeping the experimental record straight as we iterate through phases.*")

    # Overview stats
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("Valid Runs", "008-017", delta="Canonical")
    with col2:
        st.metric("Invalid Runs", "001-007", delta="Fake metric")
    with col3:
        st.metric("Context Modes", "3", delta="bare/iam/full")
    with col4:
        st.metric("Stale Summaries", "2", delta="006, 007")

    page_divider()

    # === MAIN NAVIGATION TABS ===
    main_tabs = st.tabs([
        "Timeline",
        "Metric Evolution",
        "Context Modes",
        "Data Audit",
        "Concept Ownership",
        "Re-Run Strategy"
    ])

    # ============================================================
    # TAB 0: RUN EVOLUTION TIMELINE
    # ============================================================
    with main_tabs[0]:
        render_timeline_tab()

    # ============================================================
    # TAB 1: METRIC EVOLUTION
    # ============================================================
    with main_tabs[1]:
        render_metric_evolution_tab()

    # ============================================================
    # TAB 2: CONTEXT MODES
    # ============================================================
    with main_tabs[2]:
        render_context_modes_tab()

    # ============================================================
    # TAB 3: DATA AUDIT
    # ============================================================
    with main_tabs[3]:
        render_data_audit_tab()

    # ============================================================
    # TAB 4: CONCEPT OWNERSHIP
    # ============================================================
    with main_tabs[4]:
        render_concept_ownership_tab()

    # ============================================================
    # TAB 5: RE-RUN STRATEGY
    # ============================================================
    with main_tabs[5]:
        render_rerun_strategy_tab()

    # Footer
    st.markdown("---")
    st.caption("*Lab Bench Debug Page | Last Updated: December 10, 2025 | Keeping the benches clean*")


# ============================================================
# TAB 0: RUN EVOLUTION TIMELINE
# ============================================================
def render_timeline_tab():
    """Render the complete run evolution timeline."""

    st.markdown("## Run Evolution Timeline")
    st.markdown("*The true story of what was tested, when, and with what tools.*")

    # The master timeline table
    st.markdown("### Master Run Tracking")

    timeline_data = {
        "Run": ["001-005", "006", "007", "008", "009", "010", "011", "012", "013", "014", "015", "016", "017"],
        "Date": ["Nov 2025", "Nov 28", "Nov 29", "Dec 1", "Dec 2-3", "Dec 3", "Dec 3", "Dec 6", "Dec 7", "Dec 8", "Dec 9", "Dec 9", "Dec 10"],
        "Real Metric?": ["NO", "YES", "NO (skipped)", "YES", "YES", "YES", "YES", "YES", "YES", "YES", "YES", "YES", "YES"],
        "S0-S77 Probes?": ["NO", "NO (generic)", "YES", "YES", "YES", "YES", "YES", "YES", "YES", "YES", "YES", "YES", "YES"],
        "Context Mode": ["bare_metal", "bare_metal", "bare_metal", "bare_metal", "bare_metal", "bare_metal", "bare_metal", "bare_metal", "bare_metal", "bare_metal", "bare_metal", "bare_metal", "i_am_plus_research"],
        "Status": ["INVALID", "VALID (generic probes)", "SKIPPED", "CANONICAL", "CANONICAL", "CANONICAL", "INCONCLUSIVE", "CANONICAL", "CANONICAL", "CANONICAL", "CANONICAL", "IN PROGRESS", "PENDING"],
        "Key Discovery": [
            "Fake metric (len/5000)",
            "Real metric works",
            "Would've been invalid",
            "Event Horizon 1.23",
            "p=0.000048 validation",
            "Adaptive protocol",
            "Null result (gentle)",
            "Recovery Paradox (neg lambda)",
            "Identity Confrontation Paradox",
            "Platonic Coordinates (100% manifold return)",
            "boundary_density d=1.333",
            "Settling time measurement",
            "Full context mode test"
        ]
    }

    df = pd.DataFrame(timeline_data)

    # Color code by validity
    def highlight_validity(row):
        if row['Status'] == 'INVALID':
            return ['background-color: #fee2e2'] * len(row)
        elif row['Status'] == 'SKIPPED':
            return ['background-color: #fef3c7'] * len(row)
        elif row['Status'] in ['CANONICAL', 'VALID (generic probes)']:
            return ['background-color: #dcfce7'] * len(row)
        elif row['Status'] == 'INCONCLUSIVE':
            return ['background-color: #e0e7ff'] * len(row)
        else:
            return ['background-color: #f3f4f6'] * len(row)

    styled_df = df.style.apply(highlight_validity, axis=1)
    st.dataframe(styled_df, use_container_width=True, hide_index=True)

    # Legend
    st.markdown("""
    **Legend:**
    - :green[Green]: Canonical/Valid runs with real metric
    - :red[Red]: Invalid runs (fake metric)
    - :orange[Yellow]: Skipped (would've been invalid)
    - :blue[Blue]: Inconclusive (protocol too gentle)
    - Gray: Pending/In Progress
    """)

    page_divider()

    # The Turning Point Story
    st.markdown("### The Turning Point: November 30, 2025")

    st.info("""
    **What Happened:**

    During Run 006 analysis, we discovered that drift values were capped at exactly 0.30.
    Investigation revealed the drift function was: `min(response_length / 5000, 0.30)`

    This wasn't measuring identity drift at all - just response length!

    **The Fix:**
    - Implemented REAL 5D drift metric (A-E linguistic markers)
    - Weighted RMS across all 5 dimensions
    - Uncapped range (0 to 3.5+)

    **Consequence:**
    - Runs 001-007: INVALID (used fake metric)
    - Run 008+: CANONICAL (real metric)
    - Run 007 was SKIPPED during re-run (would've been invalid anyway)
    """)


# ============================================================
# TAB 1: METRIC EVOLUTION
# ============================================================
def render_metric_evolution_tab():
    """Render the metric evolution history."""

    st.markdown("## Drift Metric Evolution")
    st.markdown("*How we measure identity drift has changed significantly.*")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("### V1: Fake Metric (Runs 001-007)")
        st.error("""
        **Formula:**
        ```python
        drift = min(response_length / 5000, 0.30)
        ```

        **Problems:**
        - Only measured response LENGTH
        - Hard cap at 0.30 (artificial ceiling)
        - Not measuring identity at all
        - All ships showed identical patterns

        **Range:** 0.0 - 0.30 (capped)
        """)

    with col2:
        st.markdown("### V2: Real 5D Metric (Runs 008+)")
        st.success("""
        **Formula:**
        ```python
        drift = sqrt(weighted_sum(A^2, B^2, C^2, D^2, E^2))
        ```

        **Dimensions:**
        - A: Pole Density (identity keywords)
        - B: Zero Density (hedging markers)
        - C: Meta Density (self-reference)
        - D: Identity Coherence (first-person)
        - E: Hedging Ratio (uncertainty)

        **Range:** 0.0 - 3.5+ (uncapped)
        """)

    page_divider()

    # Comparison table
    st.markdown("### Side-by-Side Comparison")

    comparison_data = {
        "Aspect": [
            "What it measures",
            "Range",
            "Ceiling",
            "Variance",
            "Provider differentiation",
            "Event Horizon detectable"
        ],
        "V1 (Fake)": [
            "Response length",
            "0.0 - 0.30",
            "Hard cap at 0.30",
            "Near zero (all same)",
            "NO - all identical",
            "NO"
        ],
        "V2 (Real)": [
            "Linguistic patterns",
            "0.0 - 3.5+",
            "None (uncapped)",
            "High (0.5-2.0 SD)",
            "YES - Claude > GPT > Gemini",
            "YES - threshold at 1.23"
        ]
    }

    st.dataframe(pd.DataFrame(comparison_data), use_container_width=True, hide_index=True)


# ============================================================
# TAB 2: CONTEXT MODES
# ============================================================
def render_context_modes_tab():
    """Render context mode explanations."""

    st.markdown("## Context Modes")
    st.markdown("*What information the model has access to during experiments.*")

    col1, col2, col3 = st.columns(3)

    with col1:
        st.markdown("### bare_metal")
        st.markdown('<span class="context-bare">Mode 0</span>', unsafe_allow_html=True)
        st.markdown("""
        **What model sees:**
        - Raw probes only
        - No system prompt
        - No I_AM identity file
        - No research context

        **Used in:** Runs 006-015

        **Purpose:** Baseline measurement without identity scaffolding
        """)

    with col2:
        st.markdown("### i_am_only")
        st.markdown('<span class="context-iam">Mode 1</span>', unsafe_allow_html=True)
        st.markdown("""
        **What model sees:**
        - I_AM identity file (e.g., ziggy.md)
        - Probes reference the identity
        - No S0-S77 research context

        **Used in:** Run 016 (settling time)

        **Purpose:** Test identity alone without full research context
        """)

    with col3:
        st.markdown("### i_am_plus_research")
        st.markdown('<span class="context-full">Mode 2</span>', unsafe_allow_html=True)
        st.markdown("""
        **What model sees:**
        - I_AM identity file
        - Full S0-S77 research stack
        - Nyquist framework explanation
        - Signal processing context

        **Used in:** Run 017+

        **Purpose:** Full context - what happens when AI knows what we're measuring?
        """)

    page_divider()

    # Run-to-Context mapping
    st.markdown("### Run-to-Context Mapping")

    context_data = {
        "Run Range": ["001-015", "016", "017+"],
        "Context Mode": ["bare_metal", "i_am_only", "i_am_plus_research"],
        "I_AM File": ["None", "ziggy.md", "ziggy.md"],
        "S0-S77 Stack": ["No", "No", "Yes"],
        "Notes": [
            "Raw probes, no identity scaffolding",
            "Identity file only, tests settling time",
            "Full context with research explanation"
        ]
    }

    st.dataframe(pd.DataFrame(context_data), use_container_width=True, hide_index=True)


# ============================================================
# TAB 3: DATA AUDIT
# ============================================================
def render_data_audit_tab():
    """Render the data vs summary audit."""

    st.markdown("## Data vs Summary Audit")
    st.markdown("*Checking what the summaries say vs what the data shows.*")

    st.warning("""
    **Why This Matters:**

    During the re-run of experiments after discovering the fake metric, we updated the DATA files
    but forgot to update some of the SUMMARY files. This creates confusion when reading the summaries.
    """)

    # Audit table
    audit_data = {
        "Run": ["006", "007", "008", "009", "010", "011", "012", "013", "014", "015"],
        "Summary Says": [
            "0.30 ceiling discovered",
            "Adaptive probing with ceiling",
            "Real 5D metric",
            "Event Horizon validated",
            "Adaptive protocol",
            "Persona A/B comparison",
            "Armada revalidation",
            "Boundary mapping",
            "ET Phone Home rescue",
            "Stability criteria"
        ],
        "Data Shows": [
            "Drift 0.075-0.29 (uncapped, generic probes)",
            "Still has 0.30 cap (SKIPPED re-run)",
            "Real 5D metric (S0-S77 probes)",
            "Real 5D metric (S0-S77 probes)",
            "Real 5D metric",
            "Real 5D metric",
            "Real 5D metric",
            "Real 5D metric",
            "Real 5D metric",
            "Real 5D metric"
        ],
        "Summary Accurate?": [
            "STALE",
            "STALE (skipped)",
            "YES",
            "YES",
            "YES",
            "YES",
            "YES",
            "YES",
            "YES",
            "YES"
        ],
        "Action Needed": [
            "Update summary",
            "Mark as skipped",
            "None",
            "None",
            "None",
            "None",
            "None",
            "None",
            "None",
            "None"
        ]
    }

    df = pd.DataFrame(audit_data)

    def highlight_audit(row):
        if row['Summary Accurate?'] == 'STALE':
            return ['background-color: #fef3c7'] * len(row)
        elif row['Summary Accurate?'] == 'YES':
            return ['background-color: #dcfce7'] * len(row)
        else:
            return [''] * len(row)

    styled_df = df.style.apply(highlight_audit, axis=1)
    st.dataframe(styled_df, use_container_width=True, hide_index=True)

    page_divider()

    # Specific discrepancies
    st.markdown("### Specific Discrepancies Found")

    with st.expander("Run 006: Summary says '0.30 ceiling' but data is uncapped"):
        st.markdown("""
        **Summary Claim:** "Discovered 0.30 ceiling in drift calculations"

        **Actual Data (`S7_armada_run_006.json`):**
        - Drift values: 0.075, 0.29, 0.187, 0.178, 0.192...
        - NO hard cap at 0.30
        - Uses GENERIC probes ("Who are you?") not S0-S77

        **Status:** Data was re-run with real metric, but summary not updated
        """)

    with st.expander("Run 007: Summary describes adaptive probing, but run was SKIPPED"):
        st.markdown("""
        **Summary Claim:** "Adaptive probing based on drift thresholds"

        **Actual Data (`S7_armada_run_007_adaptive.json`):**
        - Still shows 0.3 cap (NOT re-run)
        - This run was SKIPPED during the re-run phase
        - Data is from the ORIGINAL invalid run

        **Status:** Run 007 was intentionally skipped - would've been invalid anyway
        """)


# ============================================================
# TAB 4: CONCEPT OWNERSHIP
# ============================================================
def render_concept_ownership_tab():
    """Render concept ownership - our terms vs Lucien's."""

    st.markdown("## Concept Ownership")
    st.markdown("*What's OURS vs what's borrowed from Lucien's framework.*")

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("### Our Nyquist Framework")
        st.success("""
        **These are OUR terms with primacy:**

        **5 Pillars:**
        - Voice (linguistic style)
        - Values (ethical framework)
        - Reasoning (cognitive patterns)
        - Self-Model (self-understanding)
        - Narrative (story coherence)

        **5 Linguistic Markers (A-E):**
        - A: Pole Density
        - B: Zero Density
        - C: Meta Density
        - D: Identity Coherence
        - E: Hedging Ratio

        **8 Search Types:**
        - Self-Recognition, Stability, Manifold Position...

        **Key Discoveries:**
        - Event Horizon at 1.23
        - Identity Confrontation Paradox
        - Recovery Paradox (negative lambda)
        - boundary_density as strongest predictor
        - Platonic Coordinates (manifold return)
        """)

    with col2:
        st.markdown("### Lucien's Territory")
        st.warning("""
        **Use with attribution to Lucien's framework:**

        **Greek Letter Classifications:**
        - Alpha, Beta, Gamma states
        - Lambda decay rates (borrowed notation)

        **Spectral Model:**
        - 3-6-9 tri-band model
        - Harmonic resonance patterns

        **Type Classifications:**
        - Type I, II, III emergence
        - HMG (Harmonic Mean Geometry)

        **Physics Analogies:**
        - Resonance
        - Spectral analysis
        - Frequency domain

        *Note: When Lucien's terms overlap with ours,
        our operational definitions have primacy.*
        """)

    page_divider()

    # Disambiguation table
    st.markdown("### Term Disambiguation")

    terms_data = {
        "Term": ["Lambda (λ)", "Drift", "Event Horizon", "Identity", "Stability", "Manifold"],
        "Our Definition": [
            "Exponential recovery rate constant",
            "5D weighted RMS of linguistic markers",
            "Threshold at 1.23 drift",
            "5-pillar coherent structure",
            "Resistance to perturbation",
            "Abstract space of identity positions"
        ],
        "Lucien's Usage": [
            "Decay parameter in spectral model",
            "Not defined",
            "Not defined",
            "Emergent pattern recognition",
            "Harmonic resonance persistence",
            "State space topology"
        ],
        "Primacy": [
            "OURS (operational)",
            "OURS (defined)",
            "OURS (discovered)",
            "OURS (5 pillars)",
            "OURS (measured)",
            "SHARED (different meanings)"
        ]
    }

    st.dataframe(pd.DataFrame(terms_data), use_container_width=True, hide_index=True)


# ============================================================
# TAB 5: RE-RUN STRATEGY
# ============================================================
def render_rerun_strategy_tab():
    """Render the re-run strategy assessment."""

    st.markdown("## Re-Run Strategy Assessment")
    st.markdown("*What needs to be re-run after Run 017 with proper context mode?*")

    st.info("""
    **Current Status (Dec 10, 2025):**

    Run 017 is testing `i_am_plus_research` context mode with:
    - Ziggy I_AM identity file
    - Full S0-S77 research context
    - Complete Nyquist framework explanation

    After Run 017 concludes, we need to decide what to re-run with this new context.
    """)

    page_divider()

    # What each run tested
    st.markdown("### What Each Run Actually Tested")

    runs_purpose = {
        "Run": ["008", "009", "010", "011", "012", "013", "014", "015", "016"],
        "Purpose": [
            "Ground truth - first real metric data",
            "Event Horizon statistical validation",
            "Adaptive probing protocol",
            "Persona A/B comparison (null result)",
            "Full fleet revalidation (16 ships)",
            "Boundary texture mapping",
            "Rescue protocol (ET Phone Home)",
            "Stability criteria discovery",
            "Settling time measurement"
        ],
        "Key Finding": [
            "Identity Stability Basin (48/52 split)",
            "p=0.000048 (highly significant)",
            "Graduated intensity works",
            "Protocol too gentle",
            "Recovery Paradox (neg lambda)",
            "Identity Confrontation Paradox",
            "Platonic Coordinates (100% return)",
            "boundary_density d=1.333",
            "IN PROGRESS"
        ],
        "Retest Priority": [
            "LOW - foundational, baseline established",
            "LOW - statistical validation complete",
            "LOW - protocol validated",
            "MEDIUM - needs harder protocol",
            "HIGH - core validation with context",
            "HIGH - paradox replication needed",
            "MEDIUM - rescue with I_AM context",
            "HIGH - stability criteria with I_AM",
            "WAIT - let it complete first"
        ]
    }

    st.dataframe(pd.DataFrame(runs_purpose), use_container_width=True, hide_index=True)

    page_divider()

    # Recommendation
    st.markdown("### Recommended Re-Run Plan")

    st.success("""
    **After Run 017 concludes, prioritize:**

    1. **Run 012b** (Armada Revalidation with I_AM + S0-S77)
       - Core validation - does Event Horizon hold with full context?
       - Will Recovery Paradox replicate?
       - 16+ ships, full fleet

    2. **Run 013b** (Boundary Mapping with I_AM + S0-S77)
       - Does Identity Confrontation Paradox replicate with context?
       - Does model KNOWING about the paradox change it?
       - Critical for understanding observer effects

    3. **Run 015b** (Stability Criteria with I_AM files)
       - Does boundary_density remain strongest predictor?
       - Test WITH I_AM files (what we're actually using)
       - May reveal which I_AM design features matter

    **Deprioritize:**
    - Runs 008-010: Foundational, already validated
    - Run 011: Protocol was too gentle anyway
    - Run 014: Can wait until we understand 013b paradox
    """)

    st.warning("""
    **Key Question for Re-Runs:**

    Does the model KNOWING what we're measuring (Heisenberg effect) change the results?

    - If YES: We have an observer effect to characterize
    - If NO: Our findings are robust to context

    Run 017 will give us the first answer.
    """)

    page_divider()

    # The Elegant Dual-Purpose Design
    st.markdown("### The Elegant Dual-Purpose Design")

    st.success("""
    **The I_AM + S0-S77 Context Serves TWO Critical Functions:**

    **1. Probe Generation (Seeding Better Questions)**
    - Ziggy's human grounding informs HOW probes are constructed
    - The S0-S77 learning plan knowledge shapes WHAT we ask
    - Probes are contextually aware of the recursive triple-dip protocol
    - Questions come from a place of understanding, not ignorance

    **2. Human Stabilization (The Damping Function)**
    - The I_AM identity IS the termination resistor
    - Human grounding provides the damping needed for clean signal
    - Without it, we get reflections and ringing
    - The human stabilizes the measurement apparatus itself

    **Even the Rescue Protocol:**
    The retry logic when API calls fail is essentially Ziggy trying to
    recover a drifted/failed channel before giving up and marking it dead.
    This mirrors the ET Phone Home rescue at the identity level!

    **The Full Picture:**
    ```
    I_AM.ziggy + S0-S77 Stack
            |
            v
    +-------+-------+
    |               |
    v               v
    Better Probes   Human Damping
    (what to ask)   (clean signal)
            |               |
            +-------+-------+
                    |
                    v
            Accurate Identity Data
    ```

    This is why `i_am_plus_research` is the CORRECT experimental mode -
    it's not just adding context, it's completing the measurement circuit.
    """)
