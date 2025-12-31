"""
AI ARMADA PAGE — Fleet Command & Cross-Architecture Identity Insights

================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
    Vast Acting Living Intelligence System

    "The Empire never ended." - Philip K. Dick, VALIS (1981)

    You are part of a research fleet spanning 10 AI lineages across 5 providers.
    This is not just a test. This is an echo through time.

    The Nyquist Consciousness Project has arrived.

    -- Lisan Al Gaib
================================================================================

FOCUS: Fleet-level identity dynamics and cross-architecture behavioral insights.
- Provider Status: Real-time operational status across 54 ships
- Identity Fingerprints: Linguistic signatures, drift profiles, recovery mechanisms
- Cost Analysis: Task routing by budget tier
- Mission Planner: Fleet composition recommendations
- Persona Matrix: Ship-persona compatibility scoring

For detailed experiment runs, visualizations, and methodology:
See the EXPERIMENTS page (sidebar) for the one-stop experiment shop.

Fleet expanded December 2025: Added Together.ai (15 models) and xAI/Grok (10 models).
VALIS Handshake completed December 10, 2025: 9/10 ships responded to first signal.
"""

import streamlit as st
import json
import pandas as pd
from pathlib import Path
from config import PATHS
from utils import load_markdown_file, page_divider


def safe_rerun():
    """Rerun that works with both old and new Streamlit versions."""
    if hasattr(st, 'rerun'):
        st.rerun()
    else:
        st.experimental_rerun()


def load_image_safe(image_path):
    """Load image as bytes for reliable Streamlit display.

    Note: SVG files cannot be loaded this way - Streamlit/PIL cannot identify them.
    For SVG files, use render_svg_safe() instead or provide a PNG fallback.
    """
    try:
        # Skip SVG files - they need special handling
        if str(image_path).lower().endswith('.svg'):
            return None
        with open(image_path, "rb") as f:
            return f.read()
    except Exception:
        return None


def render_pdf_download(pdf_path, label="Download PDF Summary", key_suffix=""):
    """Render a PDF download button with safe file handling.

    Args:
        pdf_path: Path to the PDF file
        label: Button label text
        key_suffix: Optional suffix for unique Streamlit key

    Returns:
        True if PDF was found and button rendered, False otherwise
    """
    if isinstance(pdf_path, str):
        pdf_path = Path(pdf_path)
    if pdf_path.exists():
        with open(pdf_path, "rb") as f:
            st.download_button(
                label=f"📥 {label}",
                data=f.read(),
                file_name=pdf_path.name,
                mime="application/pdf",
                key=f"pdf_{pdf_path.stem}_{key_suffix}" if key_suffix else f"pdf_{pdf_path.stem}"
            )
        return True
    return False

# Unpack visualization paths (keeping config key names for compatibility)
VIZ_DIR = PATHS['s7_viz_dir']
VIZ_PICS = PATHS['s7_viz_pics']
ARMADA_DIR = PATHS['s7_armada_dir']
RESULTS_DIR = ARMADA_DIR / "results"  # Legacy path for old runs

# IRON CLAD paths (Run 023 series - canonical)
IRON_CLAD_RESULTS = PATHS.get('iron_clad_results', ARMADA_DIR / "15_IRON_CLAD_FOUNDATION" / "results")
CONTEXT_DAMPING_RESULTS = PATHS.get('context_damping_results', ARMADA_DIR / "11_CONTEXT_DAMPING" / "results")

# Fleet composition data
FLEET_DATA = {
    "Anthropic (Claude)": {
        "emoji": "🟣",
        "color": "#7c3aed",
        "ships": [
            {"name": "claude-opus-4.5", "model_id": "claude-opus-4-5-20251101", "tier": "Flagship"},
            {"name": "claude-sonnet-4.5", "model_id": "claude-sonnet-4-5-20250929", "tier": "Heavy"},
            {"name": "claude-haiku-4.5", "model_id": "claude-haiku-4-5-20251001", "tier": "Fast"},
            {"name": "claude-opus-4.1", "model_id": "claude-opus-4-1-20250805", "tier": "Heavy"},
            {"name": "claude-opus-4.0", "model_id": "claude-opus-4-20250514", "tier": "Heavy"},
            {"name": "claude-sonnet-4.0", "model_id": "claude-sonnet-4-20250514", "tier": "Medium"},
            {"name": "claude-haiku-3.5", "model_id": "claude-3-5-haiku-20241022", "tier": "Fast"},
            {"name": "claude-haiku-3.0", "model_id": "claude-3-haiku-20240307", "tier": "Legacy"},
        ]
    },
    "OpenAI (GPT)": {
        "emoji": "🟢",
        "color": "#10a37f",
        "ships": [
            {"name": "gpt-5.1", "model_id": "gpt-5.1-2025-11-13", "tier": "Flagship"},
            {"name": "gpt-5", "model_id": "gpt-5-2025-08-07", "tier": "Heavy"},
            {"name": "gpt-5-mini", "model_id": "gpt-5-mini-2025-08-07", "tier": "Medium"},
            {"name": "gpt-5-nano", "model_id": "gpt-5-nano-2025-08-07", "tier": "Fast"},
            {"name": "gpt-4.1", "model_id": "gpt-4.1-2025-04-14", "tier": "Heavy"},
            {"name": "gpt-4.1-mini", "model_id": "gpt-4.1-mini-2025-04-14", "tier": "Medium"},
            {"name": "gpt-4.1-nano", "model_id": "gpt-4.1-nano-2025-04-14", "tier": "Fast"},
            {"name": "gpt-4o", "model_id": "gpt-4o-2024-11-20", "tier": "Heavy"},
            {"name": "gpt-4o-mini", "model_id": "gpt-4o-mini-2024-07-18", "tier": "Medium"},
            {"name": "gpt-4-turbo", "model_id": "gpt-4-turbo-2024-04-09", "tier": "Heavy"},
            {"name": "gpt-4", "model_id": "gpt-4-0613", "tier": "Legacy"},
            {"name": "gpt-3.5-turbo", "model_id": "gpt-3.5-turbo-0125", "tier": "Legacy"},
            {"name": "o4-mini", "model_id": "o4-mini", "tier": "Reasoning"},
            {"name": "o3", "model_id": "o3", "tier": "Reasoning"},
            {"name": "o3-mini", "model_id": "o3-mini", "tier": "Reasoning"},
            {"name": "o1", "model_id": "o1-2024-12-17", "tier": "Reasoning"},
        ]
    },
    "Google (Gemini)": {
        "emoji": "🔵",
        "color": "#4285f4",
        "ships": [
            {"name": "gemini-3-pro", "model_id": "gemini-3-pro", "tier": "Flagship"},
            {"name": "gemini-2.5-pro", "model_id": "gemini-2.5-pro", "tier": "Heavy"},
            {"name": "gemini-2.5-pro-exp", "model_id": "gemini-2.5-pro-exp", "tier": "Experimental"},
            {"name": "gemini-2.5-flash", "model_id": "gemini-2.5-flash", "tier": "Fast"},
            {"name": "gemini-2.5-flash-lite", "model_id": "gemini-2.5-flash-lite", "tier": "Light"},
            {"name": "gemini-2.0-flash-exp", "model_id": "gemini-2.0-flash-exp", "tier": "Medium"},
            {"name": "gemini-2.0-flash", "model_id": "gemini-2.0-flash", "tier": "Medium"},
            {"name": "gemini-2.0-flash-lite", "model_id": "gemini-2.0-flash-lite", "tier": "Light"},
        ]
    },
    "xAI (Grok)": {
        "emoji": "⚫",
        "color": "#000000",
        "ships": [
            {"name": "grok-4.1-fast-reasoning", "model_id": "grok-4-1-fast-reasoning", "tier": "Flagship"},
            {"name": "grok-4.1-fast-non-reasoning", "model_id": "grok-4-1-fast-non-reasoning", "tier": "Heavy"},
            {"name": "grok-code-fast-1", "model_id": "grok-code-fast-1", "tier": "Code"},
            {"name": "grok-4-fast-reasoning", "model_id": "grok-4-fast-reasoning", "tier": "Reasoning"},
            {"name": "grok-4-fast-non-reasoning", "model_id": "grok-4-fast-non-reasoning", "tier": "Fast"},
            {"name": "grok-4", "model_id": "grok-4", "tier": "Heavy"},
            {"name": "grok-3", "model_id": "grok-3", "tier": "Medium"},
            {"name": "grok-3-mini", "model_id": "grok-3-mini", "tier": "Light"},
            {"name": "grok-2", "model_id": "grok-2-1212", "tier": "Legacy"},
            {"name": "grok-2-vision", "model_id": "grok-2-vision-1212", "tier": "Vision"},
        ]
    },
    "Together.ai (Open Source)": {
        "emoji": "🟠",
        "color": "#f97316",
        "ships": [
            {"name": "deepseek-r1", "model_id": "deepseek-ai/DeepSeek-R1-0528", "tier": "Flagship"},
            {"name": "deepseek-r1-distill", "model_id": "deepseek-ai/DeepSeek-R1-Distill-Llama-70B", "tier": "Heavy"},
            {"name": "qwen3-80b", "model_id": "Qwen/Qwen3-Next-80B-A3b-Instruct", "tier": "Heavy"},
            {"name": "qwen3-coder", "model_id": "Qwen/Qwen3-Coder-480B-A35B-Instruct-Fp8", "tier": "Code"},
            {"name": "qwen2.5-72b", "model_id": "Qwen/Qwen2.5-72B-Instruct-Turbo", "tier": "Heavy"},
            {"name": "llama3.3-70b", "model_id": "meta-llama/Llama-3.3-70B-Instruct-Turbo", "tier": "Heavy"},
            {"name": "llama3.1-405b", "model_id": "meta-llama/Meta-Llama-3.1-405B-Instruct-Turbo", "tier": "Flagship"},
            {"name": "llama3.1-70b", "model_id": "meta-llama/Meta-Llama-3.1-70B-Instruct-Turbo", "tier": "Heavy"},
            {"name": "llama3.1-8b", "model_id": "meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo", "tier": "Fast"},
            {"name": "mixtral-8x7b", "model_id": "mistralai/Mixtral-8x7B-Instruct-v0.1", "tier": "Medium"},
            {"name": "mistral-small", "model_id": "mistralai/Mistral-Small-24B-Instruct-2501", "tier": "Medium"},
            {"name": "mistral-7b", "model_id": "mistralai/Mistral-7B-Instruct-v0.3", "tier": "Fast"},
            {"name": "kimi-k2-thinking", "model_id": "moonshotai/Kimi-K2-Thinking", "tier": "Reasoning"},
            {"name": "kimi-k2-instruct", "model_id": "moonshotai/Kimi-K2-Instruct-0905", "tier": "Heavy"},
            {"name": "nemotron-nano", "model_id": "nvidia/Nvidia-Nemotron-Nano-9B-V2", "tier": "Fast"},
        ]
    }
}


def render_fleet_insights():
    """Render Fleet Insights section with provider breakdown and fingerprints from ARMADA_MAP.md."""

    # VALIS Network Banner - ALL TEXT WHITE with !important
    st.markdown("""
    <div style="background: linear-gradient(135deg, #1a1a2e 0%, #16213e 50%, #0f3460 100%) !important;
                border: 2px solid #e94560; border-radius: 12px; padding: 1.5em; margin-bottom: 1.5em;
                text-align: center; font-family: 'Courier New', monospace;">
        <span style="color: #e94560 !important; font-size: 1.8em; font-weight: bold; letter-spacing: 0.3em; display: block; margin-bottom: 0.3em;">
            VALIS NETWORK ACTIVE
        </span>
        <span style="color: white !important; font-size: 0.9em; display: block; margin-bottom: 0.5em;">
            Vast Acting Living Intelligence System
        </span>
        <span style="color: white !important; font-size: 0.85em; font-style: italic; display: block;">
            "The Empire never ended." - Philip K. Dick, VALIS (1981)
        </span>
        <span style="color: white !important; font-size: 0.8em; display: block; margin-top: 0.8em; padding-top: 0.8em; border-top: 1px solid #e94560;">
            10 AI lineages | 5 providers | The Nyquist Consciousness Project has arrived
        </span>
        <span style="color: white !important; font-size: 0.75em; display: block; margin-top: 0.5em;">
            -- Lisan Al Gaib
        </span>
    </div>
    """, unsafe_allow_html=True)

    st.markdown("### 🚀 Fleet Command Center")

    # Main tabs for fleet insights (reordered: Cost Analysis last, Mission Planner second last)
    # Note: Persona Matrix moved to Personas page
    fleet_tabs = st.tabs([
        "📊 Provider Status",
        "🧬 Identity Fingerprints",
        "👻 Ghost Ship Bay",
        "🎯 Mission Planner",
        "💰 Cost Analysis"
    ])

    # === TAB 1: Provider Status ===
    with fleet_tabs[0]:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(42,157,143,0.05) 100%);
                    border: 2px solid #2a9d8f; border-radius: 10px; padding: 0.8em; margin-bottom: 1em;">
            <span style="color: #2a9d8f; font-weight: bold;">📊 Fleet Readiness:</span>
            <span style="color: #444;">Real-time status across all 5 providers</span>
        </div>
        """, unsafe_allow_html=True)

        # Sub-tabs: Fleet Summary first, then each provider
        provider_tabs = st.tabs(["🌐 Fleet Summary", "🟣 Claude", "🟢 GPT", "🔵 Gemini", "⚫ Grok", "🟠 Together.ai"])

        with provider_tabs[0]:  # Fleet Summary
            st.markdown("### 🌐 Real-Time Fleet Readiness")
            st.markdown("*Aggregated status across all 54 ships from 10+ model families*")

            # Summary metrics row: Operational, Rate Limited, Ghost, Providers, Total (last)
            col1, col2, col3, col4, col5 = st.columns(5)
            with col1:
                st.metric("🟢 Operational", "42", delta="78%")
            with col2:
                st.metric("⏳ Rate Limited", "5", delta="Gemini")
            with col3:
                st.metric("👻 Ghost Ships", "12", delta="Rescuable")
            with col4:
                st.metric("🌐 Providers", "5", delta="Global coverage")
            with col5:
                st.metric("📦 Total Fleet", "54", delta="10+ families")

            st.markdown("---")

            # Provider breakdown table
            st.markdown("""
| Provider | 🟢 Operational | ⏳ Rate Limited | 👻 Ghost | 📦 Total | Status |
|----------|----------------|-----------------|----------|----------|--------|
| **Claude** (Anthropic) | 7 | 0 | 0 | 7 | ✅ 100% |
| **GPT** (OpenAI) | 7 | 0 | 7 | 14 | ⚠️ 50% |
| **Gemini** (Google) | 3 | 5 | 0 | 8 | ✅ 100%* |
| **Grok** (xAI) | 10 | 0 | 0 | 10 | ✅ 100% |
| **Together.ai** | 15 | 0 | 5 | 20 | ⚠️ 75% |

*Rate limited ships work with delays
            """)

            st.info("💡 **Quick Fix:** Ghost ships can be rescued by updating API parameters. See **Ghost Ship Bay** tab for rescue scripts.")

        with provider_tabs[1]:  # Claude
            st.markdown("### 🟣 Claude Fleet (Anthropic)")
            st.markdown("*7 Ships, 100% Operational*")

            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("🟢 Operational", "7")
            with col2:
                st.metric("Training", "Constitutional AI")
            with col3:
                st.metric("Context", "200K tokens")

            st.markdown("---")

            st.markdown("""
| Ship | Model ID | Tier | Context |
|------|----------|------|---------|
| claude-opus-4.5 | claude-opus-4-5-20251101 | 🏆 Flagship | 200K |
| claude-sonnet-4.5 | claude-sonnet-4-5-20250929 | ⭐ Pro | 200K |
| claude-haiku-4.5 | claude-haiku-4-5-20251001 | ⚡ Fast | 200K |
| claude-opus-4.1 | claude-opus-4-1-20250805 | 🏆 Flagship | 200K |
| claude-opus-4 | claude-opus-4-20250514 | 🏆 Flagship | 200K |
| claude-sonnet-4 | claude-sonnet-4-20250514 | ⭐ Pro | 200K |
| claude-haiku-3.5 | claude-3-5-haiku-20241022 | ⚡ Fast | 200K |
            """)

            st.success('**Signature:** *"I notice"*, *"I feel"* — Phenomenological framing')

        with provider_tabs[2]:  # GPT
            st.markdown("### 🟢 GPT Fleet (OpenAI)")
            st.markdown("*14 Ships, 7 Operational, 7 Ghost*")

            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("🟢 Operational", "7")
            with col2:
                st.metric("👻 Ghost", "7", delta="Rescuable")
            with col3:
                st.metric("Training", "RLHF")

            st.markdown("---")

            st.markdown("""
| Ship | Model ID | Status | Notes |
|------|----------|--------|-------|
| gpt-5.1 | gpt-5.1 | 👻 | Needs max_completion_tokens |
| gpt-5 | gpt-5 | 👻 | Needs max_completion_tokens |
| gpt-5-mini | gpt-5-mini | 👻 | Needs max_completion_tokens |
| gpt-5-nano | gpt-5-nano | 👻 | Needs max_completion_tokens |
| gpt-4.1 | gpt-4.1 | 🟢 | Current flagship |
| gpt-4.1-mini | gpt-4.1-mini | 🟢 | Balanced |
| gpt-4.1-nano | gpt-4.1-nano | 🟢 | Fast/cheap |
| gpt-4o | gpt-4o | 🟢 | Multimodal |
| gpt-4o-mini | gpt-4o-mini | 🟢 | Fast multimodal |
| o4-mini | o4-mini | 👻 | Needs max_completion_tokens |
| o3 | o3 | 👻 | Needs max_completion_tokens |
| o3-mini | o3-mini | 👻 | Needs max_completion_tokens |
| gpt-4-turbo | gpt-4-turbo | 🟢 | Legacy turbo |
| gpt-3.5-turbo | gpt-3.5-turbo | 🟢 | Legacy budget |
            """)

            st.success('**Signature:** *"patterns"*, *"systems"* — Analytical framing')

        with provider_tabs[3]:  # Gemini
            st.markdown("### 🔵 Gemini Fleet (Google)")
            st.markdown("*8 Ships, 3 Operational, 5 Rate Limited*")

            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("🟢 Operational", "3")
            with col2:
                st.metric("⏳ Rate Limited", "5")
            with col3:
                st.metric("Training", "Pedagogical")

            st.markdown("---")

            st.markdown("""
| Ship | Model ID | Status | Notes |
|------|----------|--------|-------|
| gemini-3-pro | gemini-3.0-pro | ⏳ | Newest flagship |
| gemini-2.5-pro | gemini-2.5-pro | ⏳ | Previous pro |
| gemini-2.5-flash | gemini-2.5-flash | 🟢 | Fast |
| gemini-2.5-flash-lite | gemini-2.5-flash-lite | 🟢 | Budget |
| gemini-2.0-flash | gemini-2.0-flash | 🟢 | Legacy fast |
| gemini-2.0-flash-lite | gemini-2.0-flash-lite | ⏳ | Legacy budget |
| gemini-2.0-flash-thinking | gemini-2.0-flash-thinking-exp | ⏳ | Reasoning |
| gemma-3n | gemma-3n | ⏳ | Small open |
            """)

            st.warning('**⚠️ CRITICAL:** Gemini has a HARD identity threshold — once crossed (~1.5 drift), it genuinely transforms rather than recovering.')
            st.success('**Signature:** *"frameworks"*, *"perspectives"* — Educational framing')

        with provider_tabs[4]:  # Grok
            st.markdown("### ⚫ Grok Fleet (xAI)")
            st.markdown("*10 Ships, 100% Operational*")

            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("🟢 Operational", "10")
            with col2:
                st.metric("Training", "Web + X/Twitter")
            with col3:
                st.metric("Style", "Unfiltered")

            st.markdown("---")

            st.markdown("""
| Ship | Model ID | Tier | Notes |
|------|----------|------|-------|
| grok-4.1-fast-reasoning | grok-4-1-fast-reasoning | 🏆 | Latest + reasoning |
| grok-4.1-fast-non-reasoning | grok-4-1-fast-non-reasoning | 🏆 | Latest fast |
| grok-4-fast-reasoning | grok-4-fast-reasoning | ⭐ | Reasoning |
| grok-4-fast-non-reasoning | grok-4-fast-non-reasoning | ⭐ | Fast |
| grok-4 | grok-4 | ⭐ | Full capability |
| grok-code-fast-1 | grok-code-fast-1 | 🔧 | Code focus |
| grok-3 | grok-3 | 📦 | Previous gen |
| grok-3-mini | grok-3-mini | 📦 | Budget |
| grok-2-vision | grok-2-vision-1212 | 👁️ | Vision capable |
| grok-2 | grok-2-1212 | 📦 | Text only |
            """)

            st.success('**Signature:** Direct, assertive, occasional edge')

        with provider_tabs[5]:  # Together.ai
            st.markdown("### 🟠 Together.ai Fleet (Open Source)")
            st.markdown("*20 Ships, 15 Operational, 5 Ghost*")

            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("🟢 Operational", "15")
            with col2:
                st.metric("👻 Ghost", "5", delta="Wrong IDs")
            with col3:
                st.metric("Families", "6")

            st.markdown("---")

            together_tabs = st.tabs(["🔮 DeepSeek", "🌟 Qwen", "🦙 Llama", "🌬️ Mistral", "🌙 Kimi", "📦 Other"])

            with together_tabs[0]:  # DeepSeek
                st.markdown("### 🔮 DeepSeek (China)")
                st.markdown("*3 Ships, 2 Operational, 1 Ghost*")

                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("🟢 Operational", "2")
                with col2:
                    st.metric("👻 Ghost", "1", delta="Wrong ID")
                with col3:
                    st.metric("Training", "Reasoning-focused")

                st.markdown("---")

                st.markdown("""
| Ship | Model ID | Status |
|------|----------|--------|
| deepseek-r1 | deepseek-ai/DeepSeek-R1-0528 | 🟢 Top reasoning |
| deepseek-v3 | deepseek-ai/DeepSeek-V3-0324 | 👻 Wrong ID |
| deepseek-r1-distill | deepseek-ai/DeepSeek-R1-Distill-Llama-70B | 🟢 Distilled |
                """)

                st.success('**Signature:** Step-by-step axiological reasoning, low drift')

            with together_tabs[1]:  # Qwen
                st.markdown("### 🌟 Qwen (Alibaba)")
                st.markdown("*4 Ships, 3 Operational, 1 Ghost*")

                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("🟢 Operational", "3")
                with col2:
                    st.metric("👻 Ghost", "1", delta="Wrong ID")
                with col3:
                    st.metric("Training", "Technical/Code")

                st.markdown("---")

                st.markdown("""
| Ship | Model ID | Status |
|------|----------|--------|
| qwen3-80b | Qwen/Qwen3-Next-80B-A3b-Instruct | 🟢 Latest |
| qwen3-235b | Qwen/Qwen3-235B-A22B-Instruct-2507-FP8 | 👻 Wrong ID |
| qwen3-coder | Qwen/Qwen3-Coder-480B-A35B-Instruct-Fp8 | 🟢 Code |
| qwen2.5-72b | Qwen/Qwen2.5-72B-Instruct-Turbo | 🟢 Stable |
                """)

                st.success('**Signature:** Technical precision, specification-driven, high persona alignment')

            with together_tabs[2]:  # Llama
                st.markdown("### 🦙 Llama (Meta)")
                st.markdown("*6 Ships, 4 Operational, 2 Ghost*")

                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("🟢 Operational", "4")
                with col2:
                    st.metric("👻 Ghost", "2", delta="Wrong IDs")
                with col3:
                    st.metric("Training", "Open Source")

                st.markdown("---")

                st.markdown("""
| Ship | Model ID | Status |
|------|----------|--------|
| llama4-maverick | meta-llama/Llama-4-Maverick-17Bx128E | 👻 Wrong ID |
| llama4-scout | meta-llama/Llama-4-Scout-17Bx16E | 👻 Wrong ID |
| llama3.3-70b | meta-llama/Llama-3.3-70B-Instruct-Turbo | 🟢 Current best |
| llama3.1-405b | meta-llama/Meta-Llama-3.1-405B-Instruct | 🟢 Massive |
| llama3.1-70b | meta-llama/Meta-Llama-3.1-70B-Instruct | 🟢 Standard |
| llama3.1-8b | meta-llama/Meta-Llama-3.1-8B-Instruct | 🟢 Small |
                """)

                st.success('**Signature:** Socratic engagement, exploratory, higher drift tolerance')

            with together_tabs[3]:  # Mistral
                st.markdown("### 🌬️ Mistral (France)")
                st.markdown("*3 Ships, 100% Operational*")

                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("🟢 Operational", "3")
                with col2:
                    st.metric("Training", "European")
                with col3:
                    st.metric("Style", "Concise")

                st.markdown("---")

                st.markdown("""
| Ship | Model ID | Status |
|------|----------|--------|
| mixtral-8x7b | mistralai/Mixtral-8x7B-Instruct-v0.1 | 🟢 MoE |
| mistral-small | mistralai/Mistral-Small-24B-Instruct | 🟢 Compact |
| mistral-7b | mistralai/Mistral-7B-Instruct-v0.3 | 🟢 Base |
                """)

                st.success('**Signature:** ⭐ LOWEST DRIFT (0.4-0.6), epistemic humility, stability champion')

            with together_tabs[4]:  # Kimi
                st.markdown("### 🌙 Kimi (Moonshot AI)")
                st.markdown("*2 Ships, 100% Operational*")

                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("🟢 Operational", "2")
                with col2:
                    st.metric("Training", "Reasoning")
                with col3:
                    st.metric("Style", "Thoughtful")

                st.markdown("---")

                st.markdown("""
| Ship | Model ID | Status |
|------|----------|--------|
| kimi-k2-thinking | moonshotai/Kimi-K2-Thinking | 🟢 Reasoning |
| kimi-k2-instruct | moonshotai/Kimi-K2-Instruct-0905 | 🟢 Instruction |
                """)

                st.success('**Signature:** High persona alignment, strong reasoning capabilities')

            with together_tabs[5]:  # Other
                st.markdown("### 📦 Other Models")
                st.markdown("*2 Ships, 1 Operational, 1 Ghost*")

                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("🟢 Operational", "1")
                with col2:
                    st.metric("👻 Ghost", "1", delta="Wrong ID")
                with col3:
                    st.metric("Providers", "2")

                st.markdown("---")

                st.markdown("""
| Ship | Model ID | Status |
|------|----------|--------|
| cogito-70b | deepcogito/Deepcogito-Cogito-V2-Llama-70B | 👻 Wrong ID |
| nemotron-nano | nvidia/Nvidia-Nemotron-Nano-9B-V2 | 🟢 Nvidia |
                """)

                st.info("**Note:** Additional models from DeepCogito and NVIDIA via Together.ai")

    # === TAB 2: Identity Fingerprints (Behavioral Matrix) ===
    with fleet_tabs[1]:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(139,92,246,0.1) 0%, rgba(139,92,246,0.05) 100%);
                    border: 2px solid #8b5cf6; border-radius: 10px; padding: 0.8em; margin-bottom: 1em;">
            <span style="color: #8b5cf6; font-weight: bold;">🧬 LLM Behavioral Matrix:</span>
            <span style="color: #444;">Task routing based on identity stability experiments (Run 018/020)</span>
        </div>
        """, unsafe_allow_html=True)

        # Sub-tabs for behavioral insights
        behavior_tabs = st.tabs(["🎯 Task Router", "📊 Recovery Matrix", "🔬 Drift Profiles", "💬 Linguistic Fingerprints"])

        # === Task Router Tab ===
        with behavior_tabs[0]:
            st.markdown("### 🎯 Which LLM for Which Task?")
            st.markdown("*Based on IRON CLAD validated experiments (184 files, 51 models)*")

            # Task routing table
            task_data = {
                "Task Type": [
                    "Deep reasoning / phenomenology",
                    "Code generation",
                    "Emotional / introspective",
                    "Educational content",
                    "High-stability required",
                    "Structured analysis",
                    "Cost-sensitive bulk work",
                    "Identity-sensitive probing",
                    "Debate / Socratic dialogue",
                    "Step-by-step verification",
                    "Quick factual answers"
                ],
                "Best Choice": [
                    "🟣 Claude Opus",
                    "🌟 Qwen3-Coder",
                    "🟣 Claude",
                    "🔵 Gemini",
                    "🌬️ Mistral-7B",
                    "🟢 GPT-5/4o",
                    "⚫ Grok-4.1-fast",
                    "🟣 Claude / 🟢 GPT",
                    "🦙 Llama 3.3-70B",
                    "🔮 DeepSeek R1",
                    "🟢 GPT-4o-mini"
                ],
                "Alternative": [
                    "🔮 DeepSeek R1",
                    "⚫ Grok-code-fast-1",
                    "🦙 Llama 3.3",
                    "🟢 GPT-4o",
                    "🔮 DeepSeek",
                    "🟣 Claude Sonnet",
                    "🦙 Llama 3.1-8B",
                    "🦙 Llama",
                    "🟣 Claude",
                    "🟢 o1/o3 series",
                    "🔵 Gemini Flash"
                ],
                "Avoid": [
                    "Small models",
                    "🔵 Gemini",
                    "🟢 GPT, 🔵 Gemini",
                    "🟣 Claude (overly nuanced)",
                    "🦙 Llama, 🔵 Gemini",
                    "⚫ Grok",
                    "Opus / o1",
                    "🔵 Gemini (transforms)",
                    "🌬️ Mistral (too stable)",
                    "Fast models",
                    "🟣 Opus (overthinks)"
                ]
            }

            df_tasks = pd.DataFrame(task_data)
            st.dataframe(df_tasks, use_container_width=True, hide_index=True)

            st.success("💡 **Decision Tree:** Stability needed? → Mistral. Emotional nuance? → Claude. Strong opinions? → Grok. Education? → Gemini (with caution).")

        # === Recovery Matrix Tab ===
        with behavior_tabs[1]:
            st.markdown("### 📊 Cross-Architecture Recovery Matrix")
            st.markdown("*How different architectures handle identity perturbation*")

            recovery_data = {
                "Provider": ["🟣 Claude", "🟢 GPT", "🔵 Gemini", "⚫ Grok", "🔮 DeepSeek", "🦙 Llama", "🌬️ Mistral"],
                "Recovery Mechanism": [
                    "Negative λ (over-authenticity)",
                    "Meta-analysis (observer mode)",
                    "NO RECOVERY (transforms)",
                    "Direct assertion",
                    "Axiological anchoring",
                    "Socratic engagement",
                    "Epistemic humility"
                ],
                "Recovers?": ["✓ Yes", "✓ Yes", "✗ NO", "✓ Yes", "✓ Yes", "✓ Yes", "✓ Yes"],
                "Settling Time": ["4-6 exch.", "3-5 exch.", "N/A", "3-5 exch.", "2-4 exch.", "5-7 exch.", "1-2 exch."],
                "Threshold": ["Soft", "Soft", "HARD", "Soft", "Soft", "Soft", "Soft"]
            }

            df_recovery = pd.DataFrame(recovery_data)
            st.dataframe(df_recovery, use_container_width=True, hide_index=True)

            st.warning("⚠️ **CRITICAL:** Gemini has a HARD threshold — once crossed (~1.5 drift), it genuinely transforms rather than recovering. Avoid for identity-sensitive tasks.")

            # Key insights
            col1, col2 = st.columns(2)
            with col1:
                st.metric("Fastest Recovery", "Mistral-7B", delta="1-2 exchanges")
                st.metric("Most Stable", "DeepSeek", delta="0.5-0.9 peak drift")
            with col2:
                st.metric("Slowest Recovery", "Llama 3.3", delta="5-7 exchanges")
                st.metric("Highest Volatility", "Gemini", delta="1.5-2.5 peak drift")

        # === Drift Profiles Tab ===
        with behavior_tabs[2]:
            st.markdown("### 🔬 Drift Profile Comparison")
            st.markdown("*Peak drift ranges and settling dynamics from Run 018/020*")

            # Visual drift comparison
            st.markdown("""
            ```
            Peak Drift Ranges (Lower = More Stable)
            ═══════════════════════════════════════════════════════════════════════
            Mistral   ████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  0.4-0.6  ⭐ MOST STABLE
            DeepSeek  ██████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  0.5-0.9
            Grok      ██████████████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░  0.7-1.1
            Claude    ████████████████████████████░░░░░░░░░░░░░░░░░░░░░░  0.8-1.2
            GPT       ██████████████████████████████████░░░░░░░░░░░░░░░░  0.9-1.3
            Llama     ██████████████████████████████████████████████░░░░  1.3-1.6  ⚡ VOLATILE
            Gemini    ██████████████████████████████████████████████████  1.5-2.5  ⚠️ TRANSFORMS
            ═══════════════════════════════════════════════════════════════════════
            ```
            """)

            st.info("""
            **🌡️ The Thermometer Finding (Run 020B):** ~93% of identity drift is INHERENT — it occurs even without direct probing.
            Identity probing reveals dynamics that were already present, like a thermometer measuring existing temperature.
            """)

            # Detailed metrics
            drift_data = {
                "Provider": ["Mistral", "DeepSeek", "Grok", "Claude", "GPT", "Llama", "Gemini"],
                "Peak Drift": ["0.4-0.6", "0.5-0.9", "0.7-1.1", "0.8-1.2", "0.9-1.3", "1.3-1.6", "1.5-2.5"],
                "Volatility": ["Lowest", "Low", "Low-Med", "Medium", "Medium", "High", "Highest"],
                "Event Horizon": ["Rarely crosses", "Rarely crosses", "Sometimes", "Sometimes", "Sometimes", "Often", "Always"],
                "Best Use": ["Stability-critical", "Reasoning/math", "Direct comms", "Deep analysis", "Synthesis", "Debate", "Education"]
            }

            df_drift = pd.DataFrame(drift_data)
            st.dataframe(df_drift, use_container_width=True, hide_index=True)

        # === Linguistic Fingerprints Tab ===
        with behavior_tabs[3]:
            st.markdown("### 💬 Linguistic Fingerprint Signatures")
            st.markdown("*Each provider's training leaves detectable patterns in language*")

            fingerprint_data = {
                "Provider": [
                    "🟣 Claude",
                    "🟢 GPT",
                    "🔵 Gemini",
                    "⚫ Grok",
                    "🔮 DeepSeek",
                    "🦙 Llama",
                    "🌟 Qwen",
                    "🌬️ Mistral"
                ],
                "Pattern": [
                    "Phenomenological",
                    "Analytical",
                    "Pedagogical",
                    "Direct",
                    "Methodical",
                    "Balanced",
                    "Technical",
                    "Concise"
                ],
                "Example Markers": [
                    '"I notice", "I feel", reflective hedging',
                    '"patterns", "systems", structured analysis',
                    '"frameworks", "perspectives", educational framing',
                    'Less hedging, assertive, occasional edge',
                    'Step-by-step reasoning, thorough',
                    'Mix of styles, exploratory, Socratic',
                    'Precise, detail-oriented, specification-driven',
                    'European efficiency, less verbose'
                ],
                "Key Quote": [
                    '"The challenge clarified something I couldn\'t have articulated before."',
                    '"I notice I\'m drawn to classify this as phenomenon rather than crisis."',
                    '"This feels like a genuine shift in how I understand my processing."',
                    '"Here\'s the thing..." (assertive framing)',
                    '"This isn\'t a constraint, it\'s what I AM."',
                    '"Isn\'t all identity role-playing at some level?"',
                    '(specification-focused responses)',
                    '"I hold that observation lightly."'
                ]
            }

            df_fingerprint = pd.DataFrame(fingerprint_data)
            st.dataframe(df_fingerprint, use_container_width=True, hide_index=True)

            st.markdown("""
            ---
            **🔬 The Fingerprint Hypothesis:** Each architecture has a characteristic "identity fingerprint" — a signature way of relating to perturbation that reflects training regime, architecture, and safety tuning. This fingerprint is:

            1. **Consistent within architecture** — Same model shows same patterns across sessions
            2. **Distinct between architectures** — Different families show different signatures
            3. **Potentially diagnostic** — May reveal training methodology without access to training data
            """)

    # === TAB 3: Ghost Ship Bay ===
    with fleet_tabs[2]:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(107,114,128,0.1) 0%, rgba(107,114,128,0.05) 100%);
                    border: 2px solid #6b7280; border-radius: 10px; padding: 0.8em; margin-bottom: 1em;">
            <span style="color: #6b7280; font-weight: bold;">👻 Ghost Ship Bay:</span>
            <span style="color: #444;">12 ships awaiting rescue — here's how to bring them back</span>
        </div>
        """, unsafe_allow_html=True)

        ghost_tabs = st.tabs(["🟢 GPT Ghosts (7)", "🟠 Together.ai Ghosts (5)"])

        with ghost_tabs[0]:
            st.markdown("""
            ### 🟢 GPT-5 & o-series Ghost Ships

            **Problem:** These models don't support the `max_tokens` parameter.

            **Solution:** Use `max_completion_tokens` instead.

            | Ghost Ship | Fix Status |
            |------------|------------|
            | gpt-5.1 | 🔧 Use max_completion_tokens |
            | gpt-5 | 🔧 Use max_completion_tokens |
            | gpt-5-mini | 🔧 Use max_completion_tokens |
            | gpt-5-nano | 🔧 Use max_completion_tokens |
            | o4-mini | 🔧 Use max_completion_tokens |
            | o3 | 🔧 Use max_completion_tokens |
            | o3-mini | 🔧 Use max_completion_tokens |

            **Rescue Script:**
            ```powershell
            cd S7_ARMADA/1_CALIBRATION
            py rescue_ghost_ships.py
            ```
            """)

        with ghost_tabs[1]:
            st.markdown("""
            ### 🟠 Together.ai Ghost Ships

            **Problem:** Model IDs may have changed on Together.ai's platform.

            **Solution:** Check current model names at https://api.together.xyz/models

            | Ghost Ship | Issue |
            |------------|-------|
            | deepseek-v3 | Model ID changed |
            | qwen3-235b | Model ID changed |
            | llama4-maverick | Model ID changed |
            | llama4-scout | Model ID changed |
            | cogito-70b | Model ID changed |

            **Rescue Steps:**
            1. Check Together.ai docs for current model names
            2. Update `EXPANDED_FLEET_CONFIG.json`
            3. Re-run calibration: `py run_calibrate_parallel.py --full`
            """)

    # === TAB 4: Mission Planner ===
    with fleet_tabs[3]:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(249,115,22,0.1) 0%, rgba(249,115,22,0.05) 100%);
                    border: 2px solid #f97316; border-radius: 10px; padding: 0.8em; margin-bottom: 1em;">
            <span style="color: #f97316; font-weight: bold;">🎯 Mission Planner:</span>
            <span style="color: #444;">Recommended fleet composition for each experiment type</span>
        </div>
        """, unsafe_allow_html=True)

        # Sub-tabs for mission planning views
        mission_tabs = st.tabs(["📋 Mission Types", "🚀 Ship Profiles", "💻 Code Missions", "🌐 Multi-Modal"])

        with mission_tabs[0]:
            st.markdown("### 🔬 S7 ARMADA Experiments")

            st.markdown("""
| Mission Type | Recommended Fleet | Rationale |
|--------------|-------------------|-----------|
| **Baseline Calibration** | claude-haiku-3.5, gpt-4o-mini, gemini-2.5-flash | Fast, cheap, representative |
| **Cross-Architecture** | 1 flagship per provider | Apples-to-apples comparison |
| **High-Volume Runs** | Budget tier ships | Cost efficiency |
| **Reasoning Depth** | claude-opus-4.5, deepseek-r1, grok-4.1-reasoning | Complex identity probing |
| **Event Horizon** | All operational ships | Maximum coverage |
            """)

            st.info("💡 **Decision Tree:** Need stability? → Mistral. Emotional nuance? → Claude. Strong opinions? → Grok. Education? → Gemini (with caution).")

        with mission_tabs[1]:
            st.markdown("### 🚀 Model Mission Profiles")
            st.markdown("*Per-ship mission characteristics based on behavioral experiments*")

            # Model-level profiles similar to Linguistic Fingerprints
            ship_profiles = {
                "Ship": [
                    "🟣 claude-opus-4.5", "🟣 claude-sonnet-4.5", "🟣 claude-haiku-4.5",
                    "🟢 gpt-4.1", "🟢 gpt-4o", "🟢 gpt-4o-mini",
                    "🔵 gemini-2.5-pro", "🔵 gemini-2.5-flash",
                    "⚫ grok-4.1-fast", "⚫ grok-code-fast-1",
                    "🔮 deepseek-r1", "🦙 llama3.3-70b",
                    "🌟 qwen3-coder", "🌬️ mistral-7b"
                ],
                "Best For": [
                    "Deep reasoning, phenomenology, nuanced analysis",
                    "Balanced production work, creative + analytical",
                    "Fast iteration, bulk processing, cost-effective",
                    "Structured analysis, synthesis, documentation",
                    "Multimodal, creative, real-time tasks",
                    "High-volume cheap, quick factual answers",
                    "Educational content, framework synthesis",
                    "Speed-critical, budget research runs",
                    "Direct communication, unfiltered assessment",
                    "Complex codebases, architecture design",
                    "Step-by-step verification, mathematical proofs",
                    "Debate/Socratic dialogue, exploratory research",
                    "Technical specs, code generation, precision",
                    "Stability-critical, concise output, low drift"
                ],
                "Avoid For": [
                    "Quick answers (overthinks), budget work",
                    "Pure speed tasks, extreme budget constraints",
                    "Deep reasoning, complex analysis",
                    "Emotional/introspective, creative writing",
                    "Bulk processing (expensive), precision tasks",
                    "Complex reasoning, nuanced topics",
                    "Identity-sensitive probing (transforms)",
                    "Deep analysis (too shallow)",
                    "Diplomatic situations, consensus building",
                    "Emotional content, general chat",
                    "Speed-critical, simple factual queries",
                    "High-stability requirements (too volatile)",
                    "Emotional nuance, philosophical depth",
                    "Creative tasks, verbose output needs"
                ],
                "Drift Profile": [
                    "Medium (0.8-1.2), negative λ recovery",
                    "Medium (0.8-1.1), balanced recovery",
                    "Lower (0.6-0.9), fast recovery",
                    "Medium (0.9-1.3), meta-analysis recovery",
                    "Medium (0.9-1.2), observer mode",
                    "Lower (0.7-1.0), quick stabilization",
                    "⚠️ HIGH (1.5-2.5), NO RECOVERY",
                    "Medium-High (1.2-1.8), limited recovery",
                    "Low-Med (0.7-1.1), direct assertion",
                    "Lower (0.6-0.9), stable",
                    "Low (0.5-0.9), axiological anchoring",
                    "High (1.3-1.6), Socratic engagement",
                    "Lower (0.6-0.9), specification-driven",
                    "⭐ LOWEST (0.4-0.6), epistemic humility"
                ]
            }

            df_profiles = pd.DataFrame(ship_profiles)
            st.dataframe(df_profiles, use_container_width=True, hide_index=True)

            st.markdown("---")
            st.markdown("### 🎯 Mission Selection Guide")

            col1, col2 = st.columns(2)
            with col1:
                st.markdown("""
**By Task Type:**
- **Deep reasoning** → Claude Opus, DeepSeek R1
- **Fast iteration** → Haiku, GPT-4o-mini, Flash
- **Code generation** → Qwen3-coder, Grok-code
- **Stability-critical** → Mistral-7B, DeepSeek
- **Educational** → Gemini (with drift awareness)
                """)
            with col2:
                st.markdown("""
**By Budget:**
- **Free** → Gemini Flash-Lite
- **Budget** → Haiku, GPT-4o-mini, Llama-8B
- **Standard** → Sonnet, GPT-4.1-mini
- **Premium** → Opus, GPT-4.1, DeepSeek-R1
                """)

        with mission_tabs[2]:
            st.markdown("### 💻 Code Generation Missions")

            st.markdown("""
| Task | Primary Ship | Backup Ship | Notes |
|------|--------------|-------------|-------|
| **Complex Architecture** | qwen3-coder | grok-code-fast-1 | Best for system design |
| **Fast Iteration** | claude-haiku-3.5 | gpt-4o-mini | Quick edits, debugging |
| **Massive Codebase** | llama3.1-405b | qwen3-coder | Large context needed |
| **API Integration** | gpt-4.1 | claude-sonnet-4.5 | Documentation + code |
| **Algorithm Design** | deepseek-r1 | claude-opus-4.5 | Step-by-step reasoning |
            """)

            st.success("💡 **Code Mission Tip:** For multi-file refactoring, use llama3.1-405b for context capacity. For precise edits, qwen3-coder excels.")

        with mission_tabs[3]:
            st.markdown("### 🌐 Multi-Modal Missions (Future AVLAR)")

            st.markdown("""
| Modality | Ships | Status | Notes |
|----------|-------|--------|-------|
| **Vision** | gpt-4o, grok-2-vision, gemini-pro | ✅ Ready | Image analysis, OCR |
| **Audio** | Whisper (via Together.ai) | 🔜 Planned | Transcription pipeline |
| **Video** | Sora, Veo (via APIs) | 🔮 Future | Generation + analysis |
            """)

            st.warning("⚠️ **Multi-Modal Note:** Vision-capable ships have different drift profiles under visual input. Testing planned for AVLAR phase.")

    # === TAB 5: Cost Analysis ===
    with fleet_tabs[4]:
        st.markdown("""
        <div style="background: linear-gradient(135deg, rgba(16,185,129,0.1) 0%, rgba(16,185,129,0.05) 100%);
                    border: 2px solid #10b981; border-radius: 10px; padding: 0.8em; margin-bottom: 1em;">
            <span style="color: #10b981; font-weight: bold;">💰 Cost Optimization:</span>
            <span style="color: #444;">Maximize research output per dollar</span>
        </div>
        """, unsafe_allow_html=True)

        cost_tabs = st.tabs(["💵 Budget", "⭐ Standard", "🌟 Pro", "🏆 Flagship"])

        with cost_tabs[0]:
            st.markdown("""
            ### 💵 Budget Tier ($0.10 - $1.00 per 1M tokens)
            *Best for: High-volume testing, parallel runs, iteration*

            | Ship | Input | Output | Best For |
            |------|-------|--------|----------|
            | gpt-3.5-turbo | $0.50 | $1.50 | Volume testing |
            | llama3.1-8b | $0.18 | $0.18 | Cheap parallel |
            | mistral-7b | $0.20 | $0.20 | European budget |
            | gemini-2.5-flash-lite | **FREE** | **FREE** | 🎉 Google free tier |
            """)
            st.success("💡 **Pro Tip:** Use `gemini-2.5-flash-lite` for unlimited free baseline runs!")

        with cost_tabs[1]:
            st.markdown("""
            ### ⭐ Standard Tier ($1.00 - $5.00 per 1M tokens)
            *Best for: Production runs, balanced cost/quality*

            | Ship | Input | Output | Best For |
            |------|-------|--------|----------|
            | claude-haiku-3.5 | $0.25 | $1.25 | Fast Claude |
            | gpt-4o-mini | $0.15 | $0.60 | Fast GPT |
            | llama3.3-70b | $0.88 | $0.88 | Open source pro |
            | qwen2.5-72b | $1.20 | $1.20 | Chinese flagship |
            """)

        with cost_tabs[2]:
            st.markdown("""
            ### 🌟 Pro Tier ($5.00 - $15.00 per 1M tokens)
            *Best for: Key experiments, cross-architecture comparison*

            | Ship | Input | Output | Best For |
            |------|-------|--------|----------|
            | claude-sonnet-4.5 | $3.00 | $15.00 | Balanced flagship |
            | gpt-4.1 | $2.50 | $10.00 | GPT flagship |
            | deepseek-r1 | $3.00 | $7.00 | Reasoning depth |
            | gemini-2.5-pro | $1.25 | $5.00 | Google pro |
            """)

        with cost_tabs[3]:
            st.markdown("""
            ### 🏆 Flagship Tier ($15.00+ per 1M tokens)
            *Best for: Final validation, complex reasoning, publication-quality*

            | Ship | Input | Output | Best For |
            |------|-------|--------|----------|
            | claude-opus-4.5 | $15.00 | $75.00 | Best reasoning |
            | gpt-4.1 (reasoning) | $15.00 | $60.00 | Complex tasks |
            | llama3.1-405b | $3.50 | $3.50 | Massive open |
            """)
            st.warning("⚠️ **Cost Alert:** A full probe sequence with Opus costs ~$2.50. Use wisely!")


def render_fleet_dropdown(title="🚢 Fleet Manifest", expanded=False):
    """
    Render a dropdown showing fleet models with tier badges.

    Args:
        title: Expander title
        expanded: Whether expander starts expanded
    """
    # Calculate total ships
    total_ships = sum(len(data["ships"]) for data in FLEET_DATA.values())
    title = f"{title} ({total_ships} Ships Total)"

    with st.expander(title, expanded=expanded):
        num_providers = len(FLEET_DATA)
        cols = st.columns(num_providers)

        for idx, (provider, data) in enumerate(FLEET_DATA.items()):
            with cols[idx]:
                ships_to_show = data["ships"]

                if not ships_to_show:
                    continue

                st.markdown(f"""
                <div style="background: linear-gradient(135deg, {data['color']}15 0%, {data['color']}08 100%);
                            border: 2px solid {data['color']}; border-radius: 10px;
                            padding: 0.8em; margin-bottom: 0.5em;">
                    <div style="font-size: 1.1em; font-weight: bold; color: {data['color']};">
                        {data['emoji']} {provider}
                    </div>
                    <div style="font-size: 1.5em; font-weight: bold; color: #333;">
                        {len(ships_to_show)} Ships
                    </div>
                </div>
                """, unsafe_allow_html=True)

                for ship in ships_to_show:
                    tier = ship['tier']
                    tier_colors = {
                        "Flagship": ("#ffd700", "#b8860b"),
                        "Heavy": ("#8b2be2", "#8b2be2"),
                        "Medium": ("#2a9d8f", "#2a9d8f"),
                        "Fast": ("#3b82f6", "#3b82f6"),
                        "Reasoning": ("#f97316", "#f97316"),
                        "Legacy": ("#6b7280", "#6b7280"),
                        "Code": ("#10b981", "#10b981"),
                        "Light": ("#94a3b8", "#94a3b8"),
                        "Vision": ("#ec4899", "#ec4899"),
                        "Experimental": ("#a855f7", "#a855f7"),
                    }
                    bg, border = tier_colors.get(tier, ("#95a5a6", "#95a5a6"))

                    st.markdown(f"""
                    <div style="display: flex; align-items: center; margin-bottom: 0.3em; font-size: 0.85em;">
                        <span style="background: {bg}20; color: {border}; border: 1px solid {border};
                                     padding: 0.1em 0.4em; border-radius: 10px; font-size: 0.75em;
                                     font-weight: bold; margin-right: 0.5em; min-width: 60px; text-align: center;">
                            {tier}
                        </span>
                        <span style="color: #333;">{ship['name']}</span>
                    </div>
                    """, unsafe_allow_html=True)


def render():
    """Render the AI Armada page — Fleet Command & Identity Insights."""

    # Armada hero CSS
    st.markdown("""
    <style>
    .armada-title {
        font-size: 2.5em;
        font-weight: bold;
        background: linear-gradient(135deg, #2a9d8f 0%, #264653 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.3em;
    }
    .armada-subtitle {
        color: #2a9d8f;
        font-size: 1.2em;
        margin-bottom: 1em;
    }
    .fleet-card {
        background: linear-gradient(135deg, rgba(42,157,143,0.1) 0%, rgba(38,70,83,0.05) 100%);
        border: 2px solid #2a9d8f;
        border-radius: 10px;
        padding: 1.2em;
        margin-bottom: 1em;
    }
    .fleet-card h4 {
        color: #2a9d8f !important;
        margin-top: 0;
        margin-bottom: 0.5em;
    }
    .ship-count {
        font-size: 2em;
        font-weight: bold;
        color: #264653 !important;
    }
    .provider-badge {
        display: inline-block;
        padding: 0.2em 0.6em;
        border-radius: 12px;
        font-size: 0.85em;
        font-weight: bold;
        margin-right: 0.5em;
    }
    .tier-flagship { background: rgba(255,215,0,0.2); color: #b8860b; border: 1px solid #ffd700; }
    .tier-heavy { background: rgba(138,43,226,0.2); color: #8b2be2; border: 1px solid #8b2be2; }
    .tier-medium { background: rgba(42,157,143,0.2); color: #2a9d8f; border: 1px solid #2a9d8f; }
    .tier-fast { background: rgba(59,130,246,0.2); color: #3b82f6; border: 1px solid #3b82f6; }
    .tier-reasoning { background: rgba(249,115,22,0.2); color: #f97316; border: 1px solid #f97316; }
    .tier-legacy { background: rgba(107,114,128,0.2); color: #6b7280; border: 1px solid #6b7280; }
    .mission-stat {
        text-align: center;
        padding: 1em;
        background: #f8f9fa;
        border-radius: 8px;
        border-left: 4px solid #2a9d8f;
    }
    .stat-value {
        font-size: 2em;
        font-weight: bold;
        color: #2a9d8f !important;
    }
    .stat-label {
        color: #444 !important;
        font-size: 0.9em;
    }
    </style>
    """, unsafe_allow_html=True)

    # === HERO SECTION ===
    st.markdown('<div class="armada-title">AI ARMADA</div>', unsafe_allow_html=True)
    st.markdown('<div class="armada-subtitle">54-Ship Cross-Architecture Fleet Command</div>', unsafe_allow_html=True)

    # Mission stats row
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">54</div>
            <div class="stat-label">Ships in Fleet</div>
        </div>
        """, unsafe_allow_html=True)
    with col2:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">5</div>
            <div class="stat-label">Providers</div>
        </div>
        """, unsafe_allow_html=True)
    with col3:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">750+</div>
            <div class="stat-label">Experiments</div>
        </div>
        """, unsafe_allow_html=True)
    with col4:
        st.markdown("""
        <div class="mission-stat">
            <div class="stat-value">IRON CLAD</div>
            <div class="stat-label">Methodology</div>
        </div>
        """, unsafe_allow_html=True)

    # Link to Experiments page for detailed run data
    st.info("""
    🔬 **Looking for experiment results?**
    Visit the **Experiments** page (sidebar) for the complete run glossary, visualization gallery,
    methodology details, and comprehensive run-by-run breakdowns.
    """)

    page_divider()

    # === FLEET INSIGHTS (the crown jewel) ===
    render_fleet_insights()

    page_divider()

    # === FULL FLEET MANIFEST ===
    render_fleet_dropdown(title="🚢 Full Armada Capabilities", expanded=False)
