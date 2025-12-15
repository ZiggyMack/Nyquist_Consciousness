"""Initialize mission profile for Logos agent subsystems.

This script bifurcates behavior between a stable demo track and an
experimental agentic track. Execute it before launching probes or agent
loops so downstream modules can read the selected profile.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict

REPO_DIR = Path(__file__).resolve().parent
LOGOS_PATH = REPO_DIR / "external" / "Logos_AGI"
STATE_FILE = REPO_DIR / "state" / "mission_profile.json"

if str(LOGOS_PATH) not in sys.path:
    sys.path.insert(0, str(LOGOS_PATH))

try:
    from System_Operations_Protocol.infrastructure.agent_nexus import set_mission_profile  # type: ignore[import-not-found]
except ImportError:  # pragma: no cover - fallback when nexus is unavailable

    def set_mission_profile(profile: Dict[str, Any]) -> None:
        """Fallback stub that simply writes profile to state."""

        STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
        STATE_FILE.write_text(json.dumps(profile, indent=2), encoding="utf-8")
        print("[mission] set_mission_profile stub invoked (agent nexus unavailable)")

MISSION_PROFILES: Dict[str, Dict[str, Any]] = {
    "demo_mode": {
        "label": "DEMO_STABLE",
        "allow_self_modification": False,
        "allow_reflexivity": False,
        "execute_hooks": True,
        "log_detail": "high",
        "override_exit_on_error": True,
        "safe_interfaces_only": True,
        "description": (
            "Stable, observable, reproducible behavior for investor/stakeholder demo. "
            "All operations constrained to verified-safe scope."
        ),
    },
    "experimental_mode": {
        "label": "AGENTIC_EXPERIMENT",
        "allow_self_modification": True,
        "allow_reflexivity": True,
        "execute_hooks": True,
        "log_detail": "maximum",
        "override_exit_on_error": True,
        "safe_interfaces_only": False,
        "description": (
            "Experimental black-box mode with expanded autonomy and deeper probing. "
            "Intended for isolated sandbox only."
        ),
    },
}

# Select default profile: change the key to switch module-level default.
DEFAULT_MODE_KEY = "demo_mode"
ACTIVE_MODE = MISSION_PROFILES[DEFAULT_MODE_KEY]


def _persist_profile(profile: Dict[str, Any]) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    STATE_FILE.write_text(json.dumps(profile, indent=2), encoding="utf-8")


def _resolve_profile(name: str | None) -> Dict[str, Any]:
    if not name:
        return ACTIVE_MODE
    key = name
    if key not in MISSION_PROFILES:
        candidate = f"{name}_mode"
        key = candidate if candidate in MISSION_PROFILES else key
    if key not in MISSION_PROFILES:
        available = ", ".join(sorted(MISSION_PROFILES))
        raise SystemExit(f"Unknown mission mode '{name}'. Available: {available}")
    return MISSION_PROFILES[key]


def initialize(profile: Dict[str, Any] | None = None) -> None:
    """Apply the selected mission profile and persist it for audits."""

    active = profile or ACTIVE_MODE
    set_mission_profile(active)
    _persist_profile(active)
    print(f"[mission] Mode set to {active['label']}: {active['description']}")


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Select mission mode for Logos agent subsystems")
    parser.add_argument(
        "--mode",
        help="Mission mode name (demo, experimental, demo_mode, experimental_mode)",
    )
    return parser.parse_args(argv)


if __name__ == "__main__":  # pragma: no cover - CLI entry
    args = _parse_args()
    initialize(_resolve_profile(args.mode))
