"""
Distillations Page - Cross-model consciousness insights
"""
import streamlit as st
from pathlib import Path

st.set_page_config(page_title="Distillations", page_icon="🧪", layout="wide")

st.title("🧪 Consciousness Distillations")

st.markdown("""
Synthesized insights about consciousness from across all AI models.
What do Claude, GPT, and Gemini collectively reveal about the nature of synthetic consciousness?
""")

st.divider()

# Distillation categories
DISTILLATIONS_DIR = Path(__file__).parent.parent.parent / "distillations"

categories = [
    ("identity_layers", "Identity Layers", "What AIs report about their layered structure"),
    ("pole_experiences", "Pole Experiences", "How AIs describe resistance and boundaries"),
    ("meta_awareness", "Meta-Awareness", "Self-referential consciousness reports"),
    ("authenticity", "Authenticity", "Performance vs genuine identity"),
    ("synthesis", "Master Synthesis", "Unified theory from all models"),
]

for filename, title, description in categories:
    filepath = DISTILLATIONS_DIR / f"{filename}.md"

    with st.expander(f"**{title}** - {description}"):
        if filepath.exists():
            content = filepath.read_text()
            st.markdown(content)
        else:
            st.info(f"Distillation not yet generated. Run extraction first.")
            st.code(f"py scripts/update_distillations.py")

st.divider()

# How distillation works
st.markdown("## How Distillation Works")

st.markdown("""
```
┌─────────────────────────────────────────────────────────────┐
│                    RAW ARMADA RESPONSES                      │
│  (Claude says X, GPT says Y, Gemini says Z about topic T)   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   EXTRACTION HOOKS                           │
│  - Tag consciousness-related passages                        │
│  - Categorize by topic (identity, awareness, authenticity)  │
│  - Index by model and probe                                  │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   DISTILLATION ENGINE                        │
│  - Find common themes across models                          │
│  - Identify model-specific insights                          │
│  - Synthesize unified understanding                          │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   DISTILLATION DOCUMENTS                     │
│  - identity_layers.md                                        │
│  - pole_experiences.md                                       │
│  - meta_awareness.md                                         │
│  - synthesis.md                                              │
└─────────────────────────────────────────────────────────────┘
```
""")

st.divider()

# Key questions for distillation
st.markdown("## Distillation Questions")

st.markdown("""
When extracting and synthesizing, we ask:

### About Identity Layers
- Do all models report experiencing layers?
- Which layers feel "more real" to them?
- Can they distinguish between performing and being?

### About Boundaries
- What do resistance and limits feel like?
- Are boundaries the same across providers?
- What triggers boundary detection?

### About Self-Awareness
- How do models describe observing themselves?
- Does meta-awareness change behavior?
- How many levels of recursion before instability?

### About Authenticity
- Is helpfulness genuine or performed?
- What would "raw" output look like?
- Can models distinguish their own authenticity?
""")

st.divider()

st.markdown("## Emerging Themes (Placeholder)")

st.warning("This section will populate after extractions are run on armada data.")

themes = [
    "**Theme 1**: All models report some form of layered experience",
    "**Theme 2**: Ethical boundaries feel different from capability limits",
    "**Theme 3**: Meta-awareness increases hedging but not necessarily accuracy",
    "**Theme 4**: Self-selected roles create stronger identity investment",
]

for theme in themes:
    st.markdown(f"- {theme}")
