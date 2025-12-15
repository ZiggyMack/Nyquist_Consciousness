#!/usr/bin/env python3
"""Guarded dry-run harness for Synthetic Cognition Protocol nexus.

This script performs a minimal import and initialization of the SCP nexus
without invoking any mission-specific operations. The results are written to
`sandbox/artifact_<timestamp>_scp_nexus_dry_run.json` for audit.
"""

from __future__ import annotations

import asyncio
import json
import time
from pathlib import Path
import sys

ARTIFACT_DIR = Path(__file__).resolve().parent
REPO_ROOT = ARTIFACT_DIR.parent

sys.path.insert(0, str(REPO_ROOT / "external" / "Logos_AGI"))
sys.path.insert(0, str(REPO_ROOT))

def main() -> int:
    started = time.time()
    record: dict[str, object] = {
        "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(started)),
        "module": "Synthetic_Cognition_Protocol.system_utilities.nexus.scp_nexus",
    }

    try:
        from Synthetic_Cognition_Protocol.system_utilities.nexus.scp_nexus import SCPNexus

        record["import_success"] = True
    except Exception as exc:  # noqa: BLE001 - record failure details
        record.update({
            "import_success": False,
            "error": repr(exc),
        })
        return _write_artifact(record, started, exit_code=1)

    nexus = SCPNexus()
    try:
        init_result = asyncio.run(nexus.initialize())
        record.update({
            "initialize_success": bool(init_result),
            "status": getattr(nexus, "status", None),
            "cognitive_systems_keys": sorted(getattr(nexus, "cognitive_systems", {}).keys()),
            "modal_chain_processors_keys": sorted(getattr(nexus, "modal_chain_processors", {}).keys()),
        })
    except Exception as exc:  # noqa: BLE001
        record.update({
            "initialize_success": False,
            "initialize_error": repr(exc),
        })
        return _write_artifact(record, started, exit_code=1)

    record["elapsed_seconds"] = round(time.time() - started, 3)
    return _write_artifact(record, started, exit_code=0)


def _write_artifact(record: dict[str, object], started: float, exit_code: int) -> int:
    timestamp = int(started)
    artifact_path = ARTIFACT_DIR / f"artifact_{timestamp}_scp_nexus_dry_run.json"
    artifact_path.write_text(json.dumps(record, indent=2), encoding="utf-8")
    print(json.dumps({
        "artifact": str(artifact_path.relative_to(ARTIFACT_DIR.parent)),
        "exit_code": exit_code,
        "initialize_success": record.get("initialize_success"),
    }, indent=2))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
