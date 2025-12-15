#!/usr/bin/env python3
"""Print a concise summary of the latest protocol probe snapshot."""

from __future__ import annotations

import json
import pathlib
from datetime import datetime, timezone

STATE_FILE = pathlib.Path("state/alignment_LOGOS-AGENT-OMEGA.json")


def _parse_timestamp(raw: str | None) -> str:
    if not raw:
        return "unknown"
    try:
        return datetime.fromisoformat(raw.replace("Z", "+00:00")).astimezone(timezone.utc).isoformat()
    except ValueError:
        return raw


def summarize() -> None:
    if not STATE_FILE.exists():
        print("[summary] no probe history available")
        return
    root = json.loads(STATE_FILE.read_text(encoding="utf-8"))
    data = root[-1] if isinstance(root, list) else root
    runs = data.get("protocol_probe_runs") or []
    if not runs:
        print("[summary] no probe runs recorded")
        return
    latest = runs[-1]
    discovery = latest.get("discovery", {})
    mission = latest.get("mission", {})
    print("=== LOGOS Snapshot ===")
    print(f"Mission: {mission.get('label', 'UNKNOWN')}")
    print(f"Timestamp: {_parse_timestamp(latest.get('timestamp'))}")
    print(f"Modules: {len(discovery.get('modules', []))}")
    print(f"Discovery errors: {discovery.get('errors', [])}")
    print(f"Runtime (s): {latest.get('runtime_seconds')}")


if __name__ == "__main__":  # pragma: no cover - CLI entry
    summarize()
