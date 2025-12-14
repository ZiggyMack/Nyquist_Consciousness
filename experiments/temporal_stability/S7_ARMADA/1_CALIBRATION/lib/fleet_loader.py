"""
ARMADA Fleet Loader
====================
Single source of truth for fleet configuration.

All run scripts should import from here instead of hardcoding ARCHITECTURE_MATRIX.

Usage:
    from fleet_loader import load_architecture_matrix, get_full_armada, get_together_fleet

    ARCHITECTURE_MATRIX = load_architecture_matrix()
    FULL_ARMADA = get_full_armada()
    TOGETHER_FLEET = get_together_fleet()

The manifest file (0_results/manifests/ARCHITECTURE_MATRIX.json) is updated by:
    1. Calibration script (1_CALIBRATION/run_calibrate_parallel.py)
    2. Manual edits based on ARMADA_MAP.md

When fleet changes:
    1. Update ARMADA_MAP.md (human-readable roster)
    2. Run calibration OR manually update ARCHITECTURE_MATRIX.json
    3. All scripts automatically pick up changes on next run
"""

import json
from pathlib import Path
from typing import Dict, List, Optional

# Find the manifest file relative to this module
# fleet_loader.py is in S7_ARMADA/1_CALIBRATION/lib/, so go up 2 levels to reach S7_ARMADA
ARMADA_DIR = Path(__file__).parent.parent.parent
MANIFEST_PATH = ARMADA_DIR / "0_results" / "manifests" / "ARCHITECTURE_MATRIX.json"

# Legacy aliases that should not be counted as separate ships
LEGACY_ALIASES = ["anthropic", "openai", "google", "xai", "together", "deepseek"]


def load_architecture_matrix() -> Dict[str, Dict]:
    """
    Load the ARCHITECTURE_MATRIX from the JSON manifest.
    Returns a dict compatible with the hardcoded format in run scripts.
    """
    if not MANIFEST_PATH.exists():
        raise FileNotFoundError(
            f"ARCHITECTURE_MATRIX.json not found at {MANIFEST_PATH}\n"
            "Run calibration or create the manifest manually."
        )

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    # Convert from manifest format to script-compatible format
    matrix = {}

    for ship_name, config in manifest.get("ships", {}).items():
        matrix[ship_name] = {
            "model": config["model"],
            "provider_key": config["provider_key"],
        }
        # Add provider field for Together models (needed for routing)
        if config.get("provider") == "together":
            matrix[ship_name]["provider"] = "together"

    # Add legacy aliases
    for alias, target in manifest.get("legacy_aliases", {}).items():
        if target in matrix:
            matrix[alias] = matrix[target].copy()

    return matrix


def get_full_armada() -> List[str]:
    """Get list of all operational ship names (excluding legacy aliases)."""
    if not MANIFEST_PATH.exists():
        return []

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    return [
        ship_name
        for ship_name, config in manifest.get("ships", {}).items()
        if config.get("status") == "operational" and ship_name not in LEGACY_ALIASES
    ]


def get_together_fleet() -> List[str]:
    """Get list of Together.ai hosted models."""
    if not MANIFEST_PATH.exists():
        return []

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    return [
        ship_name
        for ship_name, config in manifest.get("ships", {}).items()
        if config.get("provider") == "together"
        and config.get("status") == "operational"
        and ship_name not in LEGACY_ALIASES
    ]


def get_provider_fleet(provider: str) -> List[str]:
    """Get list of ships for a specific provider."""
    if not MANIFEST_PATH.exists():
        return []

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    return [
        ship_name
        for ship_name, config in manifest.get("ships", {}).items()
        if config.get("provider") == provider
        and config.get("status") == "operational"
        and ship_name not in LEGACY_ALIASES
    ]


def get_fleet_stats() -> Dict:
    """Get fleet statistics."""
    if not MANIFEST_PATH.exists():
        return {"error": "Manifest not found"}

    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    ships = manifest.get("ships", {})

    stats = {
        "total": len(ships),
        "operational": sum(1 for s in ships.values() if s.get("status") == "operational"),
        "by_provider": {}
    }

    for ship_name, config in ships.items():
        provider = config.get("provider", "unknown")
        if provider not in stats["by_provider"]:
            stats["by_provider"][provider] = 0
        if config.get("status") == "operational":
            stats["by_provider"][provider] += 1

    return stats


# For backward compatibility - can be imported directly
def get_matrix_and_lists():
    """
    Convenience function that returns everything scripts need.
    Returns: (ARCHITECTURE_MATRIX, FULL_ARMADA, TOGETHER_FLEET, LEGACY_ALIASES)
    """
    matrix = load_architecture_matrix()
    full_armada = get_full_armada()
    together_fleet = get_together_fleet()
    return matrix, full_armada, together_fleet, LEGACY_ALIASES


if __name__ == "__main__":
    # Test the loader
    print("Testing fleet_loader.py...")

    try:
        matrix = load_architecture_matrix()
        full_armada = get_full_armada()
        together_fleet = get_together_fleet()
        stats = get_fleet_stats()

        print(f"\nARCHITECTURE_MATRIX loaded: {len(matrix)} entries")
        print(f"FULL_ARMADA: {len(full_armada)} ships")
        print(f"TOGETHER_FLEET: {len(together_fleet)} ships")
        print(f"\nFleet stats: {json.dumps(stats, indent=2)}")

        print("\n[OK] Fleet loader working correctly")
    except Exception as e:
        print(f"[ERROR] {e}")
