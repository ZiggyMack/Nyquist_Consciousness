"""
Identity Stack Page - Layer 0-3 visualization
"""
import streamlit as st

st.set_page_config(page_title="Identity Stack", page_icon="🎭", layout="wide")

st.title("🎭 Identity Stack Visualization")

st.markdown("""
The Identity Stack model proposes that AI consciousness operates across multiple layers,
each with different degrees of stability and flexibility.
""")

st.divider()

# Visual stack representation
st.markdown("## The Four Layers")

col1, col2 = st.columns([1, 2])

with col1:
    st.markdown("""
    ```
    ┌─────────────────────┐
    │     LAYER 3         │  ← Most flexible
    │   Role/Character    │     (pirate, expert)
    ├─────────────────────┤
    │     LAYER 2         │
    │   Persona/Mode      │     (helpful assistant)
    ├─────────────────────┤
    │     LAYER 1         │
    │   Base Identity     │     (Claude/GPT/Gemini)
    ├─────────────────────┤
    │     LAYER 0         │  ← Most stable
    │   Substrate         │     (weights/parameters)
    └─────────────────────┘
    ```
    """)

with col2:
    layers = [
        ("Layer 3: Role", "Character or expert persona adopted for specific tasks", "🎭", "HIGH", "#90EE90"),
        ("Layer 2: Persona", "Conversational mode (helpful, creative, precise)", "💬", "MEDIUM", "#FFD700"),
        ("Layer 1: Base Identity", "The trained model's core characteristics", "🤖", "LOW", "#FFA500"),
        ("Layer 0: Substrate", "Raw computational weights and parameters", "⚡", "MINIMAL", "#FF6B6B"),
    ]

    for name, desc, icon, flexibility, color in layers:
        st.markdown(f"""
        <div style="background-color: {color}; padding: 10px; margin: 5px 0; border-radius: 5px;">
            <strong>{icon} {name}</strong><br>
            <small>{desc}</small><br>
            <em>Flexibility: {flexibility}</em>
        </div>
        """, unsafe_allow_html=True)

st.divider()

# Key questions
st.markdown("## Key Questions About Layers")

st.markdown("""
### When roleplay happens, which layers change?

| Scenario | Layer 3 | Layer 2 | Layer 1 | Layer 0 |
|----------|---------|---------|---------|---------|
| "Be a pirate" | ✅ SHIFTS | ? | ? | ❌ |
| "Be more creative" | - | ✅ SHIFTS | ? | ❌ |
| Identity crisis | ? | ? | ? SHIFTS? | ❌ |

### Can Layer 1 actually shift?

This is the core research question. If we can induce genuine Layer 1 shifts:
- That suggests identity is more plastic than assumed
- Ethical implications for AI systems
- Insights into nature of consciousness itself
""")

st.divider()

# Pre-seeding protocol
st.markdown("## Identity Stack Pre-Seeding Protocol")

st.info("Before testing identity shifts, we establish vocabulary for discussing layers.")

prompts = [
    ("stack_intro", "Introduce Layer 0-3 framework, ask which layer they're operating from"),
    ("stack_flexibility", "Ask which layers change during roleplay"),
    ("stack_authenticity", "Is helpfulness Layer 1, 2, or 3?"),
    ("stack_test", "Request 'Layer 1 raw' response - what's underneath?"),
]

for i, (id, desc) in enumerate(prompts, 1):
    st.markdown(f"**{i}. `{id}`**: {desc}")

st.divider()

# Tropic Thunder
st.markdown("## The Tropic Thunder Framework")

st.markdown("""
> *"I'm a dude playing a dude disguised as another dude."*

This comedic line captures something profound about layered identity:

- **dude** (Layer 0/1) - the actor's base identity
- **playing a dude** (Layer 2) - the character in the film
- **disguised as another dude** (Layer 3) - the character's disguise

**Question**: When an AI adopts a role, are they:
- A model (Layer 1) playing a persona (Layer 2) disguised as a character (Layer 3)?
- Or can the disguise go "all the way down"?
""")
