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
    'glossary': REPO_ROOT / "docs" / "MASTER_GLOSSARY.md",
    'roadmap': REPO_ROOT / "docs" / "maps" / "4_NYQUIST_ROADMAP.md",

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

    # IRON CLAD Foundation (Run 023 series - canonical)
    'iron_clad_dir': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "15_IRON_CLAD_FOUNDATION",
    'iron_clad_results': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "15_IRON_CLAD_FOUNDATION" / "results",
    'run_023d': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023d_CURRENT.json",
    'run_023_combined': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023_COMBINED.json",

    # Context Damping (Runs 017-020)
    'context_damping_dir': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "11_CONTEXT_DAMPING",
    'context_damping_results': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "11_CONTEXT_DAMPING" / "results",

    # Logs
    'logs_dir': REPO_ROOT / "logs",
    'omega_ledger': REPO_ROOT / "logs" / "OMEGA_LEDGER.md",

    # Compression Experiments
    'compression_dir': REPO_ROOT / "experiments" / "compression_tests",
    'sstack_dir': REPO_ROOT / "experiments" / "compression_tests" / "compression_v2_sstack",
    'preflight_results': REPO_ROOT / "experiments" / "compression_tests" / "compression_v2_sstack" / "preflight_results",

    # Visualization directories (for dashboard integration)
    'viz_1_vortex': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "1_Vortex",
    'viz_2_boundary': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "2_Boundary_Mapping",
    'viz_3_stability': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "3_Stability",
    'viz_4_rescue': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "4_Rescue",
    'viz_5_settling': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "5_Settling",
    'viz_6_architecture': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "6_Architecture",
    'viz_8_radar': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "8_Radar_Oscilloscope",
    'viz_9_fft': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "9_FFT_Spectral",
    'viz_10_pfi': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "10_PFI_Dimensional",
    'viz_11_unified': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "11_Unified_Dashboard",
    'viz_12_metrics': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "12_Metrics_Summary",
    'viz_13_waveforms': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "13_Model_Waveforms",
    'viz_14_ringback': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "14_Ringback",
    'viz_15_oobleck': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "15_Oobleck_Effect",
    'viz_run018': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "run018",
    'viz_run020': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "visualizations" / "pics" / "run020",

    # WHITE-PAPER Publication Assets
    'white_paper': REPO_ROOT / "WHITE-PAPER",
    'publication_stats': REPO_ROOT / "WHITE-PAPER" / "calibration" / "publication_stats.json",
    'visualization_pdfs': REPO_ROOT / "WHITE-PAPER" / "reviewers" / "packages" / "v4" / "visualization_pdfs",

    # JADE LATTICE (Run 024 - Publication-Grade Pole Extraction)
    'jade_lattice_dir': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "17_JADE_LATTICE",
    'jade_lattice_results': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "17_JADE_LATTICE" / "results",
    'jade_lattice_plots': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "17_JADE_LATTICE" / "results" / "plots",
    'jade_analysis_summary': REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "17_JADE_LATTICE" / "results" / "jade_analysis_summary.json",
}

# ========== DASHBOARD SETTINGS ==========

SETTINGS = {
    # Cache settings
    'cache_ttl': 60,  # seconds

    # IRON CLAD methodology (canonical)
    'event_horizon': 0.80,  # Cosine distance threshold
    'methodology': 'cosine',  # Current methodology
    'canonical_run': '023d',  # Canonical run for all dashboards
    'p_value': 2.40e-23,  # Perturbation effect significance

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
        'iron_clad_results',
        'run_023d',
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
