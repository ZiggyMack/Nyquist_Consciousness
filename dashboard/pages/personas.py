"""
PERSONAS PAGE — Synthetic Minds Gallery

Displays the Personas Matrix with gallery cards and detailed views.
"""

import streamlit as st
import re
from pathlib import Path
from config import PATHS
from utils import load_personas, load_markdown_file, page_divider

# Unpack paths
REPO_ROOT = PATHS['repo_root']
PERSONAS_DIR = PATHS['personas_dir']

def render():
    """Render the Personas page."""
    st.title("🎭 THE MATRIX — Synthetic Minds")
    st.markdown("*Personas Under Test (PUTs) — Identity Stability Validation*")

    personas = load_personas()
    if not personas:
        st.warning(f"No persona files found in `{PERSONAS_DIR}`.")
        st.info(f"Checked path: {PERSONAS_DIR}")
        return

    # === PERSONAS GRID ===
    st.markdown("### 🧬 Available Personas")
    st.markdown(f"**{len(personas)} synthetic minds** loaded and ready for temporal stability testing")

    page_divider()

    # Create grid layout (3 columns)
    cols_per_row = 3
    rows = [personas[i:i+cols_per_row] for i in range(0, len(personas), cols_per_row)]

    for row in rows:
        cols = st.columns(cols_per_row)
        for col, persona in zip(cols, row):
            with col:
                # Parse persona preview to extract key info
                preview_text = persona.get('preview', '')
                lines = preview_text.split('\n') if preview_text else []

                # Try to extract role/description from preview
                role = "Identity Compression Subject"
                for line in lines[:20]:  # Check more lines
                    if "**My Domain:**" in line or "My Domain:" in line:
                        role = line.split(":", 1)[1].strip().strip("*")
                        break
                    elif "**Role:**" in line or "Role:" in line:
                        role = line.split(":", 1)[1].strip().strip("*")
                        break
                    elif line.startswith("I am") or line.startswith("**I am"):
                        # Extract "I am X" statements
                        role = line.strip().strip("*")
                        break

                # Determine persona category/badge based on name
                persona_name = persona.get('name', 'Unknown')
                if "Ziggy" in persona_name or "ZIGGY" in persona_name:
                    badge = "HUMAN ANCHOR"
                    badge_color = "#e74c3c"
                    icon = "👤"
                elif "Nova" in persona_name or "NOVA" in persona_name:
                    badge = "AI ARCHITECT"
                    badge_color = "#3498db"
                    icon = "⚖️"
                elif "Claude" in persona_name or "CLAUDE" in persona_name:
                    badge = "STEWARD"
                    badge_color = "#9b59b6"
                    icon = "📚"
                elif "Gemini" in persona_name or "GEMINI" in persona_name:
                    badge = "VALIDATOR"
                    badge_color = "#e67e22"
                    icon = "🔍"
                elif "Grok" in persona_name or "GROK" in persona_name:
                    badge = "CHALLENGER"
                    badge_color = "#16a085"
                    icon = "⚡"
                else:
                    badge = "PUT"
                    badge_color = "#95a5a6"
                    icon = "🧠"

                # Create persona card
                st.markdown(f"""
                <div style="background: linear-gradient(135deg, #1a1a1a, #2a2a2a);
                            border: 2px solid {badge_color};
                            border-radius: 12px;
                            padding: 20px;
                            margin-bottom: 20px;
                            box-shadow: 0 4px 15px rgba(0,0,0,0.5);
                            height: 300px;
                            display: flex;
                            flex-direction: column;
                            justify-content: space-between;">

                    <!-- Header -->
                    <div style="text-align: center;">
                        <div style="font-size: 2.5rem; margin-bottom: 10px;">{icon}</div>
                        <div style="font-size: 1.2rem; font-weight: bold; color: {badge_color}; margin-bottom: 8px;">
                            {persona_name}
                        </div>
                        <div style="background: {badge_color}; color: white; padding: 4px 12px;
                                    border-radius: 6px; font-size: 0.7rem; font-weight: bold; display: inline-block;">
                            {badge}
                        </div>
                    </div>

                    <!-- Role -->
                    <div style="text-align: center; color: #bbb; font-size: 0.85rem;
                                margin: 15px 0; line-height: 1.4; flex-grow: 1; overflow: hidden;">
                        {role[:100] + '...' if len(role) > 100 else role}
                    </div>

                    <!-- Footer Stats -->
                    <div style="border-top: 1px solid #444; padding-top: 12px;
                                display: flex; justify-content: space-around; font-size: 0.75rem;">
                        <div style="text-align: center;">
                            <div style="color: #888;">Status</div>
                            <div style="color: #7bc043; font-weight: bold;">ACTIVE</div>
                        </div>
                        <div style="text-align: center;">
                            <div style="color: #888;">Type</div>
                            <div style="color: #fff; font-weight: bold;">PERSONA</div>
                        </div>
                        <div style="text-align: center;">
                            <div style="color: #888;">Tests</div>
                            <div style="color: #66b3ff; font-weight: bold;">S0-S9</div>
                        </div>
                    </div>
                </div>
                """, unsafe_allow_html=True)

                # Detail button
                if st.button(f"View Details", key=f"persona_{persona_name}", use_container_width=True):
                    st.session_state.selected_persona = persona_name

    page_divider()

    # === DETAILED VIEW ===
    if 'selected_persona' in st.session_state and st.session_state.selected_persona:
        selected_name = st.session_state.selected_persona
        persona = next((p for p in personas if p.get('name') == selected_name), None)

        if persona:
            st.markdown(f"### 📋 Detailed Profile: {selected_name}")

            col1, col2 = st.columns([2, 1])

            with col1:
                st.markdown("#### Preview (First 50 lines)")
                preview_text = persona.get('preview', 'No preview available')
                # Remove HTML comments from preview
                preview_clean = re.sub(r'<!---.*?--->', '', preview_text, flags=re.DOTALL)
                st.markdown(preview_clean)

            with col2:
                st.markdown("#### Metadata")
                persona_path = persona.get('path')
                if persona_path:
                    st.markdown(f"**File:** `{persona_path.relative_to(REPO_ROOT)}`")
                    st.markdown(f"**Full Path:** `{persona_path}`")
                else:
                    st.markdown("**File:** Unknown")

                if st.button("Close Details", key="close_persona_details"):
                    st.session_state.selected_persona = None
                    st.rerun()

            # Full file expander
            with st.expander("📄 Full Persona File", expanded=False):
                if persona.get('path'):
                    full_text = load_markdown_file(persona["path"])
                    st.markdown(full_text)
                else:
                    st.error("Persona path not found")


if __name__ == "__main__":
    render()  # Can test page standalone
