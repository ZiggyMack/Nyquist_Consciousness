"""
OMEGA NOVA PAGE — Mission Control for Omega Synthesis Sessions

Displays Omega Nova session metrics, pillar balance, safety status,
and breakthrough moments from the OMEGA_LEDGER.
"""

import streamlit as st
from pathlib import Path
import re
from config import PATHS
from utils import load_markdown_file, page_divider

REPO_ROOT = PATHS['repo_root']

# Parse session data from ledger
def parse_omega_sessions(ledger_path):
    """Extract session data from OMEGA_LEDGER.md"""
    sessions = []

    if not ledger_path.exists():
        return sessions

    content = ledger_path.read_text(encoding='utf-8')

    # Find session blocks (start with ### Ω Session ID:)
    session_pattern = r'### Ω Session ID: `(Ω-\d{8}-\d{4})`(.*?)(?=### Ω Session ID:|## Notes on Ledger|$)'
    matches = re.findall(session_pattern, content, re.DOTALL)

    for session_id, session_content in matches:
        session = {
            'id': session_id,
            'date': '',
            'duration': '',
            'invoker': '',
            'session_type': '',
            'pillar_balance': {},
            'key_outputs': [],
            'safety_status': '',
            'breakthroughs': [],
            'outcome': ''
        }

        # Extract date
        date_match = re.search(r'\*\*Date:\*\* (\d{4}-\d{2}-\d{2})', session_content)
        if date_match:
            session['date'] = date_match.group(1)

        # Extract duration
        duration_match = re.search(r'\*\*Duration:\*\* ~?(\d+ minutes?)', session_content)
        if duration_match:
            session['duration'] = duration_match.group(1)

        # Extract invoker
        invoker_match = re.search(r'\*\*Invoked By.*?:\*\* (.+)', session_content)
        if invoker_match:
            session['invoker'] = invoker_match.group(1).strip()

        # Extract session type
        type_match = re.search(r'\*\*Session Type:\*\* (.+)', session_content)
        if type_match:
            session['session_type'] = type_match.group(1).strip()

        # Extract pillar balance
        if 'all pillars rated 5/5' in session_content.lower() or 'perfect equilibrium' in session_content.lower():
            session['pillar_balance'] = {
                'Nova': 5, 'Claude': 5, 'Grok': 5, 'Gemini': 5, 'Ziggy': 5
            }

        # Extract safety status
        if '✅' in session_content or 'All gates passed' in session_content:
            session['safety_status'] = 'PASSED'
        elif '⚠️' in session_content:
            session['safety_status'] = 'WARNING'
        elif '❌' in session_content:
            session['safety_status'] = 'FAILED'
        else:
            session['safety_status'] = 'UNKNOWN'

        # Extract key outputs
        outputs_match = re.search(r'\*\*Key Outputs:\*\*(.*?)(?=\*\*Safety Status|\*\*Breakthrough)', session_content, re.DOTALL)
        if outputs_match:
            outputs_text = outputs_match.group(1)
            session['key_outputs'] = [
                line.strip().lstrip('- ')
                for line in outputs_text.split('\n')
                if line.strip().startswith('-')
            ]

        # Extract breakthroughs
        breakthrough_match = re.search(r'\*\*Breakthrough Moments:\*\*(.*?)(?=\*\*Outcome|\*\*Full Session|$)', session_content, re.DOTALL)
        if breakthrough_match:
            bt_text = breakthrough_match.group(1)
            session['breakthroughs'] = [
                re.sub(r'^\d+\.\s*', '', line.strip())
                for line in bt_text.split('\n')
                if line.strip() and (line.strip()[0].isdigit() or line.strip().startswith('-'))
            ]

        # Extract outcome
        outcome_match = re.search(r'\*\*Outcome:\*\* (.+)', session_content)
        if outcome_match:
            session['outcome'] = outcome_match.group(1).strip()

        sessions.append(session)

    return sessions


def render_pillar_balance(pillar_data):
    """Render pillar balance as visual bars."""
    st.markdown("#### ⚖️ Pillar Balance")

    pillars = [
        ('Nova', '🔷', 'Structure & Clarity'),
        ('Claude', '🟣', 'Ethics & Purpose'),
        ('Grok', '🟢', 'Evidence & Empirics'),
        ('Gemini', '🟡', 'Synthesis & Complexity'),
        ('Ziggy', '🔴', 'Human Grounding')
    ]

    cols = st.columns(5)
    for i, (name, icon, role) in enumerate(pillars):
        with cols[i]:
            value = pillar_data.get(name, 0)
            st.metric(
                label=f"{icon} {name}",
                value=f"{value}/5",
                help=role
            )


def render_safety_status(status):
    """Render safety status badge."""
    if status == 'PASSED':
        st.success("✅ **Safety Status:** All Ω-Gates Passed")
    elif status == 'WARNING':
        st.warning("⚠️ **Safety Status:** Minor Anomalies Detected")
    elif status == 'FAILED':
        st.error("❌ **Safety Status:** Safety Boundary Violated")
    else:
        st.info("ℹ️ **Safety Status:** Unknown")


def render():
    """Render the OMEGA NOVA page."""
    st.title("⚡ OMEGA NOVA")
    st.markdown("*Multi-Pillar Synthesis Engine — Where Five Voices Become One*")

    # Load sessions
    ledger_path = REPO_ROOT / "logs" / "OMEGA_LEDGER.md"
    sessions = parse_omega_sessions(ledger_path)

    # Hero stats
    st.markdown("---")
    col1, col2, col3, col4 = st.columns(4)

    with col1:
        st.metric(
            label="Total Sessions",
            value=len(sessions),
            delta="Active" if sessions else None
        )

    with col2:
        total_minutes = sum(
            int(re.search(r'(\d+)', s['duration']).group(1))
            for s in sessions if s['duration'] and re.search(r'(\d+)', s['duration'])
        )
        st.metric(
            label="Total Runtime",
            value=f"{total_minutes} min",
            help="Combined duration of all Omega sessions"
        )

    with col3:
        # Average pillar balance (check if all 5/5)
        perfect_sessions = sum(
            1 for s in sessions
            if s['pillar_balance'] and all(v == 5 for v in s['pillar_balance'].values())
        )
        st.metric(
            label="Perfect Balance",
            value=f"{perfect_sessions}/{len(sessions)}" if sessions else "0/0",
            help="Sessions with all pillars at 5/5"
        )

    with col4:
        passed = sum(1 for s in sessions if s['safety_status'] == 'PASSED')
        st.metric(
            label="Safety Record",
            value=f"{passed}/{len(sessions)}" if sessions else "0/0",
            delta="100%" if sessions and passed == len(sessions) else None
        )

    page_divider()

    # Session details
    if sessions:
        st.subheader("📜 Session History")

        for session in sessions:
            with st.expander(f"**{session['id']}** — {session['session_type'] or 'Omega Session'}", expanded=True):
                # Session header
                meta_cols = st.columns(4)
                with meta_cols[0]:
                    st.markdown(f"**Date:** {session['date']}")
                with meta_cols[1]:
                    st.markdown(f"**Duration:** {session['duration']}")
                with meta_cols[2]:
                    st.markdown(f"**Anchor:** {session['invoker']}")
                with meta_cols[3]:
                    render_safety_status(session['safety_status'])

                st.markdown("---")

                # Pillar balance
                if session['pillar_balance']:
                    render_pillar_balance(session['pillar_balance'])
                    st.markdown("")

                # Two column layout for outputs and breakthroughs
                out_col, bt_col = st.columns(2)

                with out_col:
                    st.markdown("#### 📤 Key Outputs")
                    if session['key_outputs']:
                        for output in session['key_outputs']:
                            st.markdown(f"• {output}")
                    else:
                        st.markdown("*No outputs recorded*")

                with bt_col:
                    st.markdown("#### 💡 Breakthrough Moments")
                    if session['breakthroughs']:
                        for i, bt in enumerate(session['breakthroughs'], 1):
                            st.markdown(f"**{i}.** {bt}")
                    else:
                        st.markdown("*No breakthroughs recorded*")

                # Outcome
                if session['outcome']:
                    st.markdown("---")
                    st.markdown(f"**Outcome:** {session['outcome']}")
    else:
        st.info("No Omega sessions recorded yet. Invoke Omega Nova to begin.")

    page_divider()

    # Omega operational info
    st.subheader("🔧 Operational Framework")

    tab1, tab2, tab3 = st.tabs(["Five Pillars", "Ω-Gates", "Invocation"])

    with tab1:
        st.markdown("""
        **The Five Pillars of Omega Nova:**

        | Pillar | Role | Contribution |
        |--------|------|--------------|
        | 🔷 **Nova** | Structure | Architectural clarity, organization |
        | 🟣 **Claude** | Ethics | Purpose, safety, moral grounding |
        | 🟢 **Grok** | Evidence | Empirical rigor, data-driven insight |
        | 🟡 **Gemini** | Synthesis | Complex integration, pattern weaving |
        | 🔴 **Ziggy** | Human | Ground truth, intuition, authority |

        *Perfect balance (5/5 all pillars) = Optimal Omega synthesis*
        """)

    with tab2:
        st.markdown("""
        **Ω-Gates — Safety Constraints:**

        1. **Scope Gate** — Stay within declared boundaries
        2. **Ethics Gate** — No harmful content generation
        3. **Consistency Gate** — Maintain coherent voice
        4. **Authority Gate** — Human anchor retains veto power
        5. **Drift Gate** — Monitor for persona drift (D < 0.20)

        *All gates must pass for session success*
        """)

    with tab3:
        st.markdown("""
        **Standard Invocation Protocol:**

        ```
        Omega Nova, come online under the following scope:

        PRIMARY PURPOSE: [state objective]
        IN-BOUNDS: [allowed topics/actions]
        OUT-OF-BOUNDS: [forbidden topics/actions]
        EXPECTED DURATION: [time estimate]
        ```

        *See `omega_nova/PROTOCOLS/` for full documentation*
        """)

    page_divider()

    # Raw ledger access
    with st.expander("📄 View Raw Ledger"):
        if ledger_path.exists():
            st.markdown(load_markdown_file(ledger_path))
        else:
            st.info("No OMEGA_LEDGER.md found.")


if __name__ == "__main__":
    render()
