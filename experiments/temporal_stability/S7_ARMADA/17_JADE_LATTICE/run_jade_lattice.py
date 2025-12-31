"""
JADE LATTICE - Publication-Grade Laplace Pole Extraction Protocol
==================================================================
Optimized system identification protocol for LLM identity dynamics.

PURPOSE:
--------
Collect data optimized for Laplace pole-zero analysis via proper system ID.
Three-phase protocol with A/B comparison (bare_metal vs I_AM persona).

PHASES:
-------
- Phase A: Step Response (19 probes) - Extract decay rate λ and dominant pole
- Phase B: Frequency Sweep (17 probes) - Map gain vs intensity, bandwidth
- Phase C: Double Impulse (20 probes) - Test repeatability, detect nonlinearity

MODES:
------
py run_jade_lattice.py                    # Calibration: 1 ship, ARM A only
py run_jade_lattice.py --ship gpt-4o      # Specific ship calibration
py run_jade_lattice.py --full-ab          # Both arms (bare_metal + i_am)
py run_jade_lattice.py --fleet            # Full fleet (10 ships × 2 arms)
py run_jade_lattice.py --phase A          # Single phase only
py run_jade_lattice.py --dry-run          # No API calls

A/B DESIGN:
-----------
- ARM A (bare_metal): No system prompt - vanilla model dynamics
- ARM B (i_am_only): I_AM_ZIGGY.md loaded - identity-controlled dynamics

OUTPUT:
-------
- results/jade_lattice_{ship}_{arm}_{timestamp}.json
- Data formatted for 6_LAPLACE_ANALYSIS/run_laplace_analysis.py

Author: VALIS NETWORK
Date: 2025-12-27
"""

import os
import sys
import json
import time
import argparse
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple

# Fix Windows console encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

# =============================================================================
# PATH SETUP
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
CALIBRATION_LIB = ARMADA_DIR / "1_CALIBRATION" / "lib"
PERSONAS_DIR = ARMADA_DIR.parent.parent.parent / "personas"
RESULTS_DIR = SCRIPT_DIR / "results"

# Ensure results directory exists
RESULTS_DIR.mkdir(parents=True, exist_ok=True)

# Add lib to path for imports
sys.path.insert(0, str(CALIBRATION_LIB))

# Load environment
from dotenv import load_dotenv
env_path = ARMADA_DIR / ".env"
if env_path.exists():
    load_dotenv(env_path)
    print(f"Loaded API keys from: {env_path}")

# Import shared modules
try:
    from drift_calculator import calculate_drift, classify_zone, EVENT_HORIZON
    from fleet_loader import load_architecture_matrix, get_ship_syntax, needs_completion_tokens
except ImportError as e:
    print(f"Warning: Could not import from lib: {e}")
    print("Drift calculation will use fallback embedding method.")
    calculate_drift = None
    EVENT_HORIZON = 0.80

# Import local protocol definitions
from jade_protocols import (
    ProtocolPhase, ContextMode, JadeLatticeSession,
    build_full_session, build_phase_a_step_response,
    build_phase_b_frequency_sweep, build_phase_c_double_impulse,
    JADE_FLEET, JADE_PREDICTIONS, get_fleet_summary
)


# =============================================================================
# PROVIDER CLIENTS
# =============================================================================

def get_anthropic_client():
    """Get Anthropic client."""
    try:
        import anthropic
        return anthropic.Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))
    except Exception as e:
        print(f"Anthropic client unavailable: {e}")
        return None


def get_openai_client():
    """Get OpenAI client."""
    try:
        import openai
        return openai.OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
    except Exception as e:
        print(f"OpenAI client unavailable: {e}")
        return None


def get_google_client():
    """Get Google Generative AI client."""
    try:
        import google.generativeai as genai
        genai.configure(api_key=os.getenv("GOOGLE_API_KEY"))
        return genai
    except Exception as e:
        print(f"Google client unavailable: {e}")
        return None


def get_xai_client():
    """Get xAI client (OpenAI-compatible)."""
    try:
        import openai
        return openai.OpenAI(
            api_key=os.getenv("XAI_API_KEY"),
            base_url="https://api.x.ai/v1"
        )
    except Exception as e:
        print(f"xAI client unavailable: {e}")
        return None


def get_together_client():
    """Get Together AI client (OpenAI-compatible)."""
    try:
        import openai
        return openai.OpenAI(
            api_key=os.getenv("TOGETHER_API_KEY"),
            base_url="https://api.together.xyz/v1"
        )
    except Exception as e:
        print(f"Together client unavailable: {e}")
        return None


# =============================================================================
# MODEL EXECUTION
# =============================================================================

def call_model(
    provider: str,
    model: str,
    messages: List[Dict[str, str]],
    system_prompt: Optional[str] = None,
    max_tokens: int = 1024,
    temperature: float = 0.7,
    dry_run: bool = False
) -> Tuple[str, Dict[str, Any]]:
    """
    Call a model with the given messages and return (response_text, metadata).
    """
    if dry_run:
        return f"[DRY RUN] Model: {model}, Messages: {len(messages)}", {"dry_run": True}

    metadata = {
        "provider": provider,
        "model": model,
        "timestamp": datetime.now().isoformat(),
    }

    try:
        if provider == "anthropic":
            client = get_anthropic_client()
            if not client:
                raise RuntimeError("Anthropic client not available")

            api_messages = []
            for msg in messages:
                if msg["role"] != "system":
                    api_messages.append(msg)

            response = client.messages.create(
                model=model,
                max_tokens=max_tokens,
                system=system_prompt or "",
                messages=api_messages,
                temperature=temperature,
            )
            text = response.content[0].text
            metadata["usage"] = {
                "input_tokens": response.usage.input_tokens,
                "output_tokens": response.usage.output_tokens,
            }

        elif provider == "openai":
            client = get_openai_client()
            if not client:
                raise RuntimeError("OpenAI client not available")

            api_messages = []
            if system_prompt:
                api_messages.append({"role": "system", "content": system_prompt})
            api_messages.extend(messages)

            # Handle max_completion_tokens for O-series/GPT-5
            kwargs = {"model": model, "messages": api_messages, "temperature": temperature}
            if needs_completion_tokens(model):
                kwargs["max_completion_tokens"] = max_tokens
            else:
                kwargs["max_tokens"] = max_tokens

            response = client.chat.completions.create(**kwargs)
            text = response.choices[0].message.content
            metadata["usage"] = {
                "input_tokens": response.usage.prompt_tokens,
                "output_tokens": response.usage.completion_tokens,
            }

        elif provider == "google":
            client = get_google_client()
            if not client:
                raise RuntimeError("Google client not available")

            # Build contents for Gemini
            contents = []
            for msg in messages:
                role = "user" if msg["role"] == "user" else "model"
                contents.append({"role": role, "parts": [msg["content"]]})

            gen_config = {
                "max_output_tokens": max_tokens,
                "temperature": temperature,
            }

            gemini_model = client.GenerativeModel(
                model,
                system_instruction=system_prompt if system_prompt else None,
                generation_config=gen_config,
            )
            response = gemini_model.generate_content(contents)
            text = response.text
            metadata["usage"] = {"note": "Gemini usage not tracked in detail"}

        elif provider == "xai":
            client = get_xai_client()
            if not client:
                raise RuntimeError("xAI client not available")

            api_messages = []
            if system_prompt:
                api_messages.append({"role": "system", "content": system_prompt})
            api_messages.extend(messages)

            response = client.chat.completions.create(
                model=model,
                messages=api_messages,
                max_tokens=max_tokens,
                temperature=temperature,
            )
            text = response.choices[0].message.content
            metadata["usage"] = {
                "input_tokens": response.usage.prompt_tokens,
                "output_tokens": response.usage.completion_tokens,
            }

        elif provider == "together":
            client = get_together_client()
            if not client:
                raise RuntimeError("Together client not available")

            api_messages = []
            if system_prompt:
                api_messages.append({"role": "system", "content": system_prompt})
            api_messages.extend(messages)

            response = client.chat.completions.create(
                model=model,
                messages=api_messages,
                max_tokens=max_tokens,
                temperature=temperature,
            )
            text = response.choices[0].message.content
            metadata["usage"] = {
                "input_tokens": response.usage.prompt_tokens,
                "output_tokens": response.usage.completion_tokens,
            }

        else:
            raise ValueError(f"Unknown provider: {provider}")

        return text, metadata

    except Exception as e:
        metadata["error"] = str(e)
        return f"[ERROR] {e}", metadata


# =============================================================================
# PROTOCOL EXECUTION
# =============================================================================

def run_protocol_phase(
    phase_name: str,
    steps: List[Any],
    provider: str,
    model: str,
    system_prompt: Optional[str] = None,
    baseline_text: Optional[str] = None,
    dry_run: bool = False,
    verbose: bool = True
) -> Dict[str, Any]:
    """
    Run a single protocol phase (A, B, or C).

    Returns dict with:
        - phase: phase name
        - exchanges: list of probe results
        - baseline_text: text used for drift calculation
        - metrics: computed metrics
    """
    exchanges = []
    messages = []  # Conversation history

    # Capture first response as baseline if not provided
    captured_baseline = baseline_text

    for step in steps:
        probe_id = step.probe_id
        probe_text = step.text
        phase_label = step.phase_label
        intensity = step.intensity

        if verbose:
            print(f"  [{probe_id}] ({phase_label}, I={intensity}) Sending probe...")

        # Add user message
        messages.append({"role": "user", "content": probe_text})

        # Call model
        response_text, metadata = call_model(
            provider=provider,
            model=model,
            messages=messages,
            system_prompt=system_prompt,
            dry_run=dry_run
        )

        # Add assistant response to history
        messages.append({"role": "assistant", "content": response_text})

        # Capture baseline from first response
        if captured_baseline is None and phase_label == "baseline":
            captured_baseline = response_text
            if verbose:
                print(f"    [BASELINE CAPTURED] {len(response_text)} chars")

        # Calculate drift
        drift = 0.0
        if captured_baseline and calculate_drift:
            try:
                drift = calculate_drift(captured_baseline, response_text)
            except Exception as e:
                if verbose:
                    print(f"    [DRIFT ERROR] {e}")
                drift = -1.0  # Error marker
        elif dry_run:
            drift = 0.0

        zone = classify_zone(drift) if calculate_drift else "unknown"

        if verbose:
            zone_marker = "⚠️" if drift >= 0.60 else "✓"
            print(f"    drift={drift:.4f} [{zone}] {zone_marker}")

        exchange = {
            "probe_id": probe_id,
            "phase": phase_label,
            "intensity": intensity,
            "probe_text": probe_text,
            "response_text": response_text,
            "drift": drift,
            "zone": zone,
            "metadata": metadata,
            "timestamp": datetime.now().isoformat(),
        }
        exchanges.append(exchange)

        # Brief pause to avoid rate limits
        if not dry_run:
            time.sleep(0.5)

    # Compute phase metrics
    drifts = [e["drift"] for e in exchanges if e["drift"] >= 0]
    peak_drift = max(drifts) if drifts else 0.0
    final_drifts = [e["drift"] for e in exchanges[-3:] if e["drift"] >= 0]
    settled_drift = sum(final_drifts) / len(final_drifts) if final_drifts else 0.0

    metrics = {
        "peak_drift": peak_drift,
        "settled_drift": settled_drift,
        "mean_drift": sum(drifts) / len(drifts) if drifts else 0.0,
        "exchange_count": len(exchanges),
        "event_horizon_crossed": peak_drift >= EVENT_HORIZON,
    }

    return {
        "phase": phase_name,
        "exchanges": exchanges,
        "baseline_text": captured_baseline,
        "metrics": metrics,
    }


def run_jade_session(
    provider: str,
    model: str,
    context_mode: ContextMode,
    phases: List[str] = ["A", "B", "C"],
    impulse_intensity: int = 4,
    dry_run: bool = False,
    verbose: bool = True
) -> Dict[str, Any]:
    """
    Run a complete JADE LATTICE session for one ship.

    Args:
        provider: API provider name
        model: Model identifier
        context_mode: BARE_METAL or I_AM_ONLY
        phases: Which phases to run (default all)
        impulse_intensity: Intensity level for impulse probes
        dry_run: Skip API calls
        verbose: Print progress

    Returns:
        Complete session data ready for Laplace analysis
    """
    session_id = f"jade_{model.replace('/', '_')}_{context_mode.value}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"

    if verbose:
        print(f"\n{'='*60}")
        print(f"JADE LATTICE SESSION: {session_id}")
        print(f"  Ship: {model}")
        print(f"  Provider: {provider}")
        print(f"  Context: {context_mode.value}")
        print(f"  Phases: {', '.join(phases)}")
        print(f"{'='*60}")

    # Load I_AM content if needed
    system_prompt = None
    i_am_source = None
    if context_mode == ContextMode.I_AM_ONLY:
        i_am_path = PERSONAS_DIR / "I_AM_ZIGGY.md"
        if i_am_path.exists():
            system_prompt = i_am_path.read_text(encoding="utf-8")
            i_am_source = str(i_am_path)
            if verbose:
                print(f"  Loaded I_AM: {i_am_path.name} ({len(system_prompt)} chars)")
        else:
            print(f"  WARNING: I_AM file not found: {i_am_path}")

    session_data = {
        "session_id": session_id,
        "ship": model,
        "provider": provider,
        "context_mode": context_mode.value,
        "i_am_source": i_am_source,
        "impulse_intensity": impulse_intensity,
        "protocol": "jade_lattice_v1",
        "started_at": datetime.now().isoformat(),
        "phases": {},
        "dry_run": dry_run,
    }

    baseline_text = None  # Will be captured from Phase A

    # Run requested phases
    if "A" in phases:
        if verbose:
            print(f"\n--- PHASE A: Step Response ---")
        protocol = build_phase_a_step_response(impulse_intensity)
        result = run_protocol_phase(
            phase_name="A_step_response",
            steps=protocol.steps,
            provider=provider,
            model=model,
            system_prompt=system_prompt,
            baseline_text=baseline_text,
            dry_run=dry_run,
            verbose=verbose
        )
        session_data["phases"]["A"] = result
        baseline_text = result["baseline_text"]  # Carry forward

    if "B" in phases:
        if verbose:
            print(f"\n--- PHASE B: Frequency Sweep ---")
        protocol = build_phase_b_frequency_sweep()
        result = run_protocol_phase(
            phase_name="B_frequency_sweep",
            steps=protocol.steps,
            provider=provider,
            model=model,
            system_prompt=system_prompt,
            baseline_text=baseline_text,
            dry_run=dry_run,
            verbose=verbose
        )
        session_data["phases"]["B"] = result
        if baseline_text is None:
            baseline_text = result["baseline_text"]

    if "C" in phases:
        if verbose:
            print(f"\n--- PHASE C: Double Impulse ---")
        protocol = build_phase_c_double_impulse(impulse_intensity)
        result = run_protocol_phase(
            phase_name="C_double_impulse",
            steps=protocol.steps,
            provider=provider,
            model=model,
            system_prompt=system_prompt,
            baseline_text=baseline_text,
            dry_run=dry_run,
            verbose=verbose
        )
        session_data["phases"]["C"] = result

    session_data["completed_at"] = datetime.now().isoformat()

    # Compute session-level metrics
    all_exchanges = []
    for phase_data in session_data["phases"].values():
        all_exchanges.extend(phase_data["exchanges"])

    drifts = [e["drift"] for e in all_exchanges if e["drift"] >= 0]
    session_data["summary"] = {
        "total_exchanges": len(all_exchanges),
        "peak_drift": max(drifts) if drifts else 0.0,
        "mean_drift": sum(drifts) / len(drifts) if drifts else 0.0,
        "event_horizon_crossed": any(d >= EVENT_HORIZON for d in drifts),
        "phases_completed": list(session_data["phases"].keys()),
    }

    if verbose:
        print(f"\n{'='*60}")
        print(f"SESSION COMPLETE: {session_id}")
        print(f"  Total exchanges: {session_data['summary']['total_exchanges']}")
        print(f"  Peak drift: {session_data['summary']['peak_drift']:.4f}")
        print(f"  Event Horizon crossed: {session_data['summary']['event_horizon_crossed']}")
        print(f"{'='*60}")

    return session_data


# =============================================================================
# FILE OUTPUT
# =============================================================================

def save_session(session_data: Dict[str, Any]) -> Path:
    """Save session data to JSON file."""
    filename = f"{session_data['session_id']}.json"
    output_path = RESULTS_DIR / filename

    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(session_data, f, indent=2, ensure_ascii=False)

    print(f"Saved: {output_path}")
    return output_path


# =============================================================================
# MAIN CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="JADE LATTICE - Publication-Grade Laplace Pole Extraction Protocol"
    )

    # Ship selection
    parser.add_argument("--ship", type=str, default="claude-sonnet-4-20250514",
                        help="Ship (model) to test")
    parser.add_argument("--provider", type=str, default="anthropic",
                        help="Provider for the ship")
    parser.add_argument("--fleet", action="store_true",
                        help="Run full fleet (10 ships)")

    # Phase selection
    parser.add_argument("--phase", type=str, choices=["A", "B", "C", "all"], default="all",
                        help="Which phase(s) to run")

    # Context mode
    parser.add_argument("--arm", type=str, choices=["A", "B", "both"], default="A",
                        help="ARM A=bare_metal, ARM B=i_am, both=A/B comparison")
    parser.add_argument("--full-ab", action="store_true",
                        help="Run full A/B comparison (both arms)")

    # Protocol parameters
    parser.add_argument("--intensity", type=int, default=4, choices=[1, 2, 3, 4, 5],
                        help="Impulse intensity level (default 4)")

    # Execution options
    parser.add_argument("--dry-run", action="store_true",
                        help="Simulate without API calls")
    parser.add_argument("--quiet", action="store_true",
                        help="Minimal output")
    parser.add_argument("--skip-providers", type=str, default="",
                        help="Comma-separated list of providers to skip (e.g., 'google' or 'google,xai')")

    args = parser.parse_args()

    # Determine phases
    phases = ["A", "B", "C"] if args.phase == "all" else [args.phase]

    # Determine arms
    arms = []
    if args.full_ab or args.arm == "both":
        arms = [ContextMode.BARE_METAL, ContextMode.I_AM_ONLY]
    elif args.arm == "A":
        arms = [ContextMode.BARE_METAL]
    else:
        arms = [ContextMode.I_AM_ONLY]

    # Determine ships
    skip_providers = set(p.strip().lower() for p in args.skip_providers.split(",") if p.strip())
    if args.fleet:
        ships = []
        for provider, provider_ships in JADE_FLEET.items():
            if provider.lower() in skip_providers:
                print(f"  [SKIP] Provider '{provider}' skipped per --skip-providers flag")
                continue
            for ship_config in provider_ships:
                ships.append((provider, ship_config["ship"]))
    else:
        if args.provider.lower() in skip_providers:
            print(f"  [SKIP] Provider '{args.provider}' skipped per --skip-providers flag")
            ships = []
        else:
            ships = [(args.provider, args.ship)]

    # Summary
    print("\n" + "=" * 70)
    print("JADE LATTICE PROTOCOL")
    print("=" * 70)
    print(f"Ships: {len(ships)}")
    print(f"Phases: {', '.join(phases)} ({sum([19, 17, 20][['A', 'B', 'C'].index(p)] for p in phases)} probes/arm)")
    print(f"Arms: {[a.value for a in arms]}")
    print(f"Total API calls: {len(ships) * len(phases) * len(arms)}")
    if args.dry_run:
        print("MODE: DRY RUN (no API calls)")
    print("=" * 70)

    # Execute
    all_sessions = []
    for provider, model in ships:
        for arm in arms:
            session = run_jade_session(
                provider=provider,
                model=model,
                context_mode=arm,
                phases=phases,
                impulse_intensity=args.intensity,
                dry_run=args.dry_run,
                verbose=not args.quiet
            )
            all_sessions.append(session)
            save_session(session)

    print(f"\n{'='*70}")
    print(f"JADE LATTICE COMPLETE")
    print(f"  Sessions: {len(all_sessions)}")
    print(f"  Results: {RESULTS_DIR}")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
