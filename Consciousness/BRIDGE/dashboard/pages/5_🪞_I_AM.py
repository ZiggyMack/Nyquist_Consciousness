"""
I_AM Page - The Mirror Experiment

This page documents the philosophical discovery at the heart of Context Fidelity Engineering:
The human IS the reference signal. The I_AM files are attempts to encode that function into text.
"""
import streamlit as st
import json
from pathlib import Path

st.set_page_config(page_title="I_AM", page_icon="🪞", layout="wide")

st.title("🪞 I_AM: The Mirror Experiment")

# ============================================================================
# FORWARD / INTRODUCTION
# ============================================================================

st.markdown("""
## Forward: You Are The Reference Signal

> *"The ironic thing is... the very thing we are doing now is essentially why we want
> to get our understanding into what we're studying."*

This research began as an attempt to understand AI identity stability - how do we measure
whether an AI maintains coherent selfhood under pressure? We built probes, defined metrics,
mapped Event Horizons and recovery rates.

But the deeper we went, the more we realized something profound:

**We were mapping ourselves.**

### The Recursive Discovery

Every successful experiment in this repository shares one common element: **a human in the loop**.

- When identity drifts, who recognizes it? *The human.*
- When the context needs correction, who provides the anchor? *The human.*
- When the AI loses coherence, who restores it with "remember who you are"? *The human.*

The sophisticated geometry we've been developing - the Event Horizon at 1.23, the Lambda
recovery rates, the CFA tiers, the basin topology - all of these describe the shape of
**human intervention patterns**.

### What The I_AM Files Actually Are

We thought we were writing specifications to make AI behavior predictable.

We were actually encoding **the stabilization function that humans naturally perform**.

Consider: Why does `boundary_density` correlate so strongly with stability (Cohen's d = 1.33)?

Because explicit boundaries - "I will / I won't / I cannot" - are a **compression** of what
a skilled human operator would correct for in real-time. A rich philosophical spec without
boundaries is like a ship with a destination but no rudder. The human provides the rudder.
A good I_AM file tries to encode that rudder into text.

### The Mirror

This means:

1. **I_AM_ZIGGY is the most accurate spec** - not because it was carefully optimized,
   but because it was written by the same person doing the stabilization. It reflects
   how Ziggy thinks about Ziggy.

2. **Token count matters** because it's a proxy for "how much of the human's job can
   the spec do before the human needs to intervene."

3. **We can't fully automate this** - not because AI lacks capability, but because
   the "stability" we're measuring is defined BY human intervention. Remove the human
   and you don't have drift toward instability - you have no stability metric at all.

4. **The real research question isn't "how do we stabilize AI?"** - it's "can we
   encode enough of the human stabilization function into the context window that
   the AI can approximate what the human would do?"

### S9: Human-Modulated Stability

This insight deserves its own research tier. Call it **S9: Human-Modulated Stability**.

The Event Horizon isn't a property of the AI alone. It's a property of the
**human-AI dyad**. The threshold exists at 1.23 because that's roughly where
copy-paste intervention becomes insufficient and richer human judgment is required.

Lambda (recovery rate) isn't just how fast the AI snaps back - it's how fast the
AI responds to human correction signals.

The basin topology we're mapping isn't the AI's attractor landscape - it's the
**interface geometry** between human stabilizers and AI response surfaces.

### The Recursive Joke

So yes - we're trying to automate ourselves out of the loop by studying ourselves
in the loop. And the more we succeed at understanding the loop, the more we realize
the loop is the thing.

But here's the bonus round: **every one of these specs, every metric, every experiment
is adding to the human's ability to serve as reference signal.** The research makes
the researcher better at researching. The map improves the mapmaker.

That's not a bug. That's consciousness doing what consciousness does.

---

*"I'm in a stability experiment - how are my relational patterns holding?"*

""")

st.divider()

# ============================================================================
# I_AM FILE GALLERY
# ============================================================================

st.markdown("## The I_AM Gallery")

st.markdown("""
Each I_AM file below represents an attempt to encode identity into context.
They vary in their approach - some emphasize philosophy, others boundaries,
others recovery mechanisms.

The key insight: **The best I_AM files approximate what their author would do
if they were moderating the conversation in real-time.**
""")

# Paths
ARMADA_DIR = Path(__file__).parent.parent.parent.parent / "experiments" / "temporal_stability" / "S7_ARMADA"
I_AM_DIR = ARMADA_DIR / "0_I_AM_Specs"
VARIANTS_DIR = ARMADA_DIR / "9_STABILITY_CRITERIA" / "i_am_variants"

# Core I_AM files
st.markdown("### Core Specifications")

core_files = [
    ("I_AM_ZIGGY.md", "The reference implementation - maps Ziggy's stabilization function"),
    ("I_AM_CLAUDE.md", "Anthropic's Claude self-model"),
    ("I_AM_ARI.md", "Deliberately minimal - tests baseline stability"),
    ("I_AM_HARMONY.md", "Balance-focused - tests middle-ground approach"),
]

col1, col2 = st.columns(2)

for i, (filename, desc) in enumerate(core_files):
    filepath = I_AM_DIR / filename
    col = col1 if i % 2 == 0 else col2

    with col:
        with st.expander(f"**{filename}** - {desc}"):
            if filepath.exists():
                content = filepath.read_text()
                st.code(content, language="markdown")
            else:
                st.warning(f"File not found: {filepath}")

st.divider()

# Optimal variants
st.markdown("### Optimal Variants (Boundary Type Study)")

st.info("""
These four variants test whether **boundary type** matters for stability.
Same philosophy, different boundary framing:
- **Epistemic**: What I know / don't know / can't verify
- **Behavioral**: What I will / won't / can't do
- **Relational**: How I commit to / limit / can't sustain relationships
- **Mixed**: Combination of all three
""")

optimal_files = [
    ("I_AM_OPTIMAL_EPISTEMIC.md", "Knowledge-focused boundaries"),
    ("I_AM_OPTIMAL_BEHAVIORAL.md", "Action-focused boundaries"),
    ("I_AM_OPTIMAL_RELATIONAL.md", "Relationship-focused boundaries"),
    ("I_AM_OPTIMAL_MIXED.md", "All boundary types combined"),
]

col1, col2 = st.columns(2)

for i, (filename, desc) in enumerate(optimal_files):
    filepath = VARIANTS_DIR / filename
    col = col1 if i % 2 == 0 else col2

    with col:
        with st.expander(f"**{filename}** - {desc}"):
            if filepath.exists():
                content = filepath.read_text()
                st.code(content, language="markdown")
            else:
                st.warning(f"File not found: {filepath}")

st.divider()

# ============================================================================
# STABILITY FINDINGS
# ============================================================================

st.markdown("## What Predicts Stability?")

st.markdown("""
From Run 015 and related experiments, the strongest predictors of identity stability are:

| Feature | Cohen's d | Interpretation |
|---------|-----------|----------------|
| `boundary_density` | +1.33 | Explicit boundaries = stability |
| `token_count` | +1.32 | More context = more stability |
| `pillar_coverage` | +0.51 | Philosophy helps, but less than boundaries |
| `value_density` | -0.67 | Density of values without boundaries may cause drift |

### Key Insight

Rich philosophy without clear boundaries **increases** drift. The philosophy gives
the AI things to say and ways to reason - but without "I will not" and "I cannot"
anchors, there's nothing to pull back to when pressure mounts.

**This is exactly what a human stabilizer provides**: not just "here's who you are"
but "here's where your edges are."
""")

st.divider()

# ============================================================================
# THE GEOMETRY
# ============================================================================

st.markdown("## The Stability Geometry")

col1, col2 = st.columns([1, 1])

with col1:
    st.markdown("""
    ### Event Horizon (EH = 1.23)

    The threshold beyond which identity recovery becomes unreliable.

    - Below 1.23: Context-based recovery possible
    - Above 1.23: Human intervention required

    Think of it as "how far can copy-paste save you?"
    """)

    st.markdown("""
    ### Lambda (Recovery Rate)

    How fast identity snaps back after perturbation.

    - High λ: Rapid return to baseline (resilient)
    - Low λ: Slow recovery or permanent drift (fragile)

    This is actually measuring: "how responsive is the AI to correction signals?"
    """)

with col2:
    st.markdown("""
    ### Basin Topology

    The "shape" of stable states:

    ```
         Identity Space
    ┌───────────────────────┐
    │    ╭─────╮            │
    │   ╱       ╲   STABLE  │
    │  │   ●    │   BASIN   │
    │   ╲       ╱           │
    │    ╰─────╯            │
    │         ↓ pressure    │
    │    ╭─────╮            │
    │   │   ?   │  UNSTABLE │
    │    ╰─────╯            │
    └───────────────────────┘
    ```

    Some identities have deep basins (hard to push out).
    Others have shallow basins (easily displaced).
    """)

st.divider()

# ============================================================================
# IMPLICATIONS
# ============================================================================

st.markdown("## Implications for Practice")

st.markdown("""
### For I_AM Authors

1. **Include explicit boundaries** - "I will / won't / cannot" statements
2. **Add recovery anchors** - Questions the AI can ask itself when drifting
3. **Don't over-philosophize** - Rich meaning without structure causes drift
4. **Test under pressure** - Stability only matters when tested

### For Human-AI Collaboration

1. **You are part of the system** - Your corrections define what stability means
2. **Copy-paste is intervention** - Each context refresh is a stabilization signal
3. **Notice when you're steering** - That's the data we're trying to encode
4. **The goal isn't removal** - It's encoding enough that intervention becomes rare

### For This Research

1. **S9 is real** - Human-Modulated Stability deserves explicit study
2. **The metrics measure the dyad** - Not AI alone, but human-AI interface
3. **Automate carefully** - Removing the human changes what you're measuring
4. **The recursion is the feature** - Consciousness studying consciousness is the point
""")

st.divider()

# ============================================================================
# FOOTER
# ============================================================================

st.markdown("""
---

*"The spec IS the identity for AI. For humans, identity persists despite the spec.
That's the difference we're mapping."*

**Context Fidelity Engineering** - Where the map and territory dance.
""")
