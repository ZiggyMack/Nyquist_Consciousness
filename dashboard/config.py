"""
NYQUIST CONSCIOUSNESS DASHBOARD — CONFIGURATION

Single source of truth for all file paths and dashboard settings.
This makes the dashboard portable and paths easy to maintain.

Usage:
    from config import PATHS, SETTINGS
    status_data = load_json(PATHS['status_file'])
"""

from pathlib import Path
import os

# ========== PATH RESOLUTION ==========

# Get the absolute path to the dashboard directory (where this config.py lives)
DASHBOARD_DIR = Path(__file__).parent.resolve()

# Get the repo root (one level up from dashboard/)
REPO_ROOT = DASHBOARD_DIR.parent.resolve()

# ========== ALL PATHS IN ONE PLACE ==========

PATHS = {
    # Root directories
    'repo_root': REPO_ROOT,
    'dashboard_dir': DASHBOARD_DIR,

    # Status and documentation
    'status_file': REPO_ROOT / "NYQUIST_STATUS.json",
    'dashboard_doc': REPO_ROOT / "NYQUIST_DASHBOARD.md",
    'glossary': REPO_ROOT / "docs" / "GLOSSARY.md",
    'roadmap': REPO_ROOT / "docs" / "maps" / "NYQUIST_ROADMAP.md",

    # Personas
    'personas_dir': REPO_ROOT / "personas",

    # S0-S9 Specs
    'specs_dir': REPO_ROOT / "docs",

    # Experiments
    'experiments_dir': REPO_ROOT / "experiments",
    'phase1_dir': REPO_ROOT / "experiments" / "phase1",
    'phase3_dir': REPO_ROOT / "experiments" / "phase3",

    # S7 Temporal Stability
    's7_dir': REPO_ROOT / "experiments" / "temporal_stability",
    's7_armada_dir': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA",
    's7_viz_dir': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations",
    's7_viz_pics': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics",

    # Logs
    'logs_dir': REPO_ROOT / "logs",
    'omega_ledger': REPO_ROOT / "logs" / "OMEGA_LEDGER.md",

    # Compression Experiments
    'compression_dir': REPO_ROOT / "experiments" / "compression_tests",
    'sstack_dir': REPO_ROOT / "experiments" / "compression_tests" / "compression_v2_sstack",
    'preflight_results': REPO_ROOT / "experiments" / "compression_tests" / "compression_v2_sstack" / "preflight_results",
}

# ========== DASHBOARD SETTINGS ==========

SETTINGS = {
    # Cache settings
    'cache_ttl': 60,  # seconds

    # Theme colors (Mr. Brute Ledger aesthetic)
    'colors': {
        'frozen': '#264653',
        'active': '#2a9d8f',
        'design': '#e9c46a',
        'prereg': '#f4a261',
        'complete': '#2a9d8f',
        'ready': '#f4a261',
        'draft': '#e76f51',
        'persona': '#7b3fe4',
        'armada': '#e76f51',
    },

    # Page titles
    'app_title': 'Nyquist Consciousness — Mission Control',
    'app_icon': '🧠',
}

# ========== VALIDATION ==========

def validate_paths():
    """
    Validate that critical paths exist.
    Returns list of missing paths.
    """
    critical_paths = [
        'repo_root',
        'personas_dir',
        'experiments_dir',
        's7_armada_dir',
    ]

    missing = []
    for key in critical_paths:
        path = PATHS[key]
        if not path.exists():
            missing.append(f"{key}: {path}")

    return missing

def print_debug_info():
    """Print all paths for debugging."""
    print("\n=== NYQUIST DASHBOARD CONFIGURATION ===")
    print(f"Dashboard Dir: {DASHBOARD_DIR}")
    print(f"Repo Root: {REPO_ROOT}")
    print("\nAll Paths:")
    for key, path in PATHS.items():
        exists = "✓" if path.exists() else "✗"
        print(f"  {exists} {key}: {path}")

    missing = validate_paths()
    if missing:
        print("\n⚠️  WARNING: Missing critical paths:")
        for path in missing:
            print(f"  - {path}")
    else:
        print("\n✓ All critical paths exist")
    print("=" * 40 + "\n")

# Auto-validate on import (only if running directly)
if __name__ == "__main__":
    print_debug_info()
