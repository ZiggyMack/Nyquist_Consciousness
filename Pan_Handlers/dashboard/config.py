"""
PAN HANDLERS DASHBOARD — CONFIGURATION

Single source of truth for all file paths and dashboard settings.
This makes the dashboard portable and paths easy to maintain.

Usage:
    from config import PATHS, SETTINGS
    projects = load_json(PATHS['projects_file'])
"""

from pathlib import Path

# ========== PATH RESOLUTION ==========

# Get the absolute path to the dashboard directory (where this config.py lives)
DASHBOARD_DIR = Path(__file__).parent.resolve()

# Get the Pan Handlers root (one level up from dashboard/)
PAN_HANDLERS_ROOT = DASHBOARD_DIR.parent.resolve()

# Get the Nyquist Consciousness repo root (one level up from Pan_Handlers/)
REPO_ROOT = PAN_HANDLERS_ROOT.parent.resolve()

# ========== ALL PATHS IN ONE PLACE ==========

PATHS = {
    # Root directories
    'repo_root': REPO_ROOT,
    'pan_handlers_root': PAN_HANDLERS_ROOT,
    'dashboard_dir': DASHBOARD_DIR,

    # Data files
    'projects_file': PAN_HANDLERS_ROOT / "projects.json",
    'manifests_dir': PAN_HANDLERS_ROOT / "manifests",

    # Project directories (for flagship projects)
    'projects_dir': PAN_HANDLERS_ROOT / "projects",

    # Connected repos (Nyquist integration)
    'nyquist_status': REPO_ROOT / "NYQUIST_STATUS.json",
    'nyquist_personas': REPO_ROOT / "personas",
    'nyquist_experiments': REPO_ROOT / "experiments",
    'nyquist_docs': REPO_ROOT / "docs",

    # S7 Armada (for Matrix page stats)
    's7_armada_dir': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA",

    # Publication status
    'publication_status': REPO_ROOT / "publication_status.json",
}

# ========== DASHBOARD SETTINGS ==========

SETTINGS = {
    # Cache settings
    'cache_ttl': 60,  # seconds

    # Theme colors (Pan Handlers green aesthetic)
    'colors': {
        'primary': '#00ff41',        # Matrix green
        'secondary': '#2a9d8f',      # Teal
        'accent': '#f4a261',         # Orange
        'gold': '#ffd700',           # Gold
        'purple': '#9b59b6',         # Purple
        'red': '#e74c3c',            # Red
        'dark_bg': '#0a0a0a',        # Near black
        'card_bg': '#1a1a1a',        # Dark gray
        # Status badges
        'active': '#00ff41',
        'complete': '#2a9d8f',
        'incubating': '#ffd700',
        'concept': '#f4a261',
        'archived': '#666666',
    },

    # Page titles
    'app_title': 'Pan Handlers — The Grand Hall',
    'app_icon': '🍳',

    # Tracks for project categorization
    'tracks': [
        'Research / Theory',
        'Education / Healthcare',
        'Governance / Democracy',
        'Intelligence / Governance',
        'Biomedical Research',
        'Justice / Social Systems',
    ],
}

# ========== VALIDATION ==========

def validate_paths():
    """
    Validate that critical paths exist.
    Returns list of missing paths.
    """
    critical_paths = [
        'pan_handlers_root',
        'projects_file',
        'manifests_dir',
    ]

    missing = []
    for key in critical_paths:
        path = PATHS[key]
        if not path.exists():
            missing.append(f"{key}: {path}")

    return missing


def print_debug_info():
    """Print all paths for debugging."""
    print("\n=== PAN HANDLERS DASHBOARD CONFIGURATION ===")
    print(f"Dashboard Dir: {DASHBOARD_DIR}")
    print(f"Pan Handlers Root: {PAN_HANDLERS_ROOT}")
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
    print("=" * 45 + "\n")


# Auto-validate on import (only if running directly)
if __name__ == "__main__":
    print_debug_info()
