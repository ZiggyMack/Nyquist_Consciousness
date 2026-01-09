"""
ESSENCE EXTRACTION - Configuration
===================================
Central configuration for data sources and output paths.

Edit this file to point at your experiment data.
"""

from pathlib import Path

# =============================================================================
# PATHS
# =============================================================================

# This experiment directory
EXPERIMENT_DIR = Path(__file__).parent.parent

# Results output directory
RESULTS_DIR = EXPERIMENT_DIR / "results"

# Documentation directory
DOCS_DIR = EXPERIMENT_DIR / "0_docs"

# =============================================================================
# DATA SOURCES - ALL SPOKES FEED INTO THIS HUB
# =============================================================================

# S7_ARMADA spoke directories
S7_ARMADA_DIR = EXPERIMENT_DIR.parent / "temporal_stability" / "S7_ARMADA"

# -----------------------------------------------------------------------------
# SPOKE 1: 11_CONTEXT_DAMPING (Runs 017-020)
# -----------------------------------------------------------------------------
CONTEXT_DAMPING_DIR = S7_ARMADA_DIR / "11_CONTEXT_DAMPING" / "results"

# -----------------------------------------------------------------------------
# SPOKE 2: 15_IRON_CLAD_FOUNDATION (Run 023 series)
# -----------------------------------------------------------------------------
IRON_CLAD_DIR = S7_ARMADA_DIR / "15_IRON_CLAD_FOUNDATION" / "results"

# -----------------------------------------------------------------------------
# SPOKE 3: 17_JADE_LATTICE (Run 024 - I_AM A/B testing)
# -----------------------------------------------------------------------------
JADE_LATTICE_DIR = S7_ARMADA_DIR / "17_JADE_LATTICE" / "results"

# -----------------------------------------------------------------------------
# SPOKE 4: 14_CONSCIOUSNESS (Gold Rush, Diamond Rush, Quartz Rush)
# -----------------------------------------------------------------------------
CONSCIOUSNESS_DIR = S7_ARMADA_DIR / "14_CONSCIOUSNESS" / "results"

# =============================================================================
# DATA SOURCES REGISTRY
# =============================================================================
# All extraction efforts flow through this registry.
# Add new data sources here as they become available.

DATA_SOURCES = {
    # --- CONTEXT DAMPING (Spoke 1) ---
    # IRON CLAD original threshold experiment (2488 subjects)
    "018": CONTEXT_DAMPING_DIR / "S7_run_018_CURRENT.json",
    # Conversation log format (248 subjects, rich dialogue)
    "020b": CONTEXT_DAMPING_DIR / "S7_run_020B_CURRENT.json",

    # --- IRON CLAD FOUNDATION (Spoke 2) ---
    # Probe sequence format (4505 experiments)
    "023": IRON_CLAD_DIR / "S7_run_023_CURRENT.json",
    # Extended settling experiments (750 experiments)
    "023d": IRON_CLAD_DIR / "S7_run_023d_CURRENT.json",

    # --- JADE LATTICE (Spoke 3) ---
    # I_AM A/B testing sessions (115+ sessions, 50 models)
    # Note: JADE uses individual session files, not a single JSON
    "jade_lattice": JADE_LATTICE_DIR,  # Directory of jade_*.json files
    # Aggregated analysis summary
    "jade_summary": JADE_LATTICE_DIR / "jade_analysis_summary.json",

    # --- CONSCIOUSNESS (Spoke 4) ---
    # Gold Rush mining runs
    "gold_rush": CONSCIOUSNESS_DIR,  # Directory of gold_rush_*.json files
}

# Data source types (some are files, some are directories)
DATA_SOURCE_TYPES = {
    "018": "file",
    "020b": "file",
    "023": "file",
    "023d": "file",
    "jade_lattice": "directory",  # Contains jade_*.json session files
    "jade_summary": "file",
    "gold_rush": "directory",  # Contains gold_rush_*.json files
}

# To add new data sources:
# DATA_SOURCES["my_experiment"] = Path("/path/to/my_experiment_results.json")
# DATA_SOURCE_TYPES["my_experiment"] = "file"  # or "directory"

# =============================================================================
# OUTPUT LOCATIONS
# =============================================================================

# Model essence profiles
ESSENCE_OUTPUT_DIR = RESULTS_DIR / "model_essences"

# Double-dip mining results
DOUBLE_DIP_OUTPUT_DIR = RESULTS_DIR / "double_dip"

# Triple-dip harvesting results
TRIPLE_DIP_OUTPUT_DIR = RESULTS_DIR / "triple_dip"

# Calibration update reports
CALIBRATION_OUTPUT_DIR = RESULTS_DIR / "calibration_updates"

# Temporal tracking (future enhancement)
TEMPORAL_OUTPUT_DIR = RESULTS_DIR / "temporal"

# =============================================================================
# EXTRACTION SETTINGS
# =============================================================================

# Minimum word count to analyze a response
MIN_WORDS = 10

# Maximum word count for a single response (truncate if longer)
MAX_WORDS = 10000

# Normalization base (per N words)
NORMALIZATION_BASE = 1000

# =============================================================================
# PROVIDER DETECTION
# =============================================================================

# Patterns for auto-detecting provider from model name
PROVIDER_PATTERNS = {
    "anthropic": ["claude"],
    "openai": ["gpt", "o1", "o3", "o4"],
    "google": ["gemini", "palm"],
    "xai": ["grok"],
    "together": ["llama", "mistral", "qwen", "deepseek", "kimi", "yi"],
    "meta": ["llama"],
}

def detect_provider(model_name: str) -> str:
    """Auto-detect provider from model name."""
    model_lower = model_name.lower()

    for provider, patterns in PROVIDER_PATTERNS.items():
        if any(p in model_lower for p in patterns):
            return provider

    return "unknown"

# =============================================================================
# LOGGING
# =============================================================================

# Enable verbose output
VERBOSE = True

# Log level for file operations
LOG_LEVEL = "INFO"

# =============================================================================
# VALIDATION
# =============================================================================

def validate_data_sources() -> dict:
    """Check which data sources are available."""
    status = {}
    for name, path in DATA_SOURCES.items():
        source_type = DATA_SOURCE_TYPES.get(name, "file")
        exists = path.exists()

        if source_type == "directory" and exists:
            # Count files in directory
            json_files = list(path.glob("*.json"))
            status[name] = {
                "path": str(path),
                "type": "directory",
                "exists": True,
                "file_count": len(json_files),
                "size_mb": round(sum(f.stat().st_size for f in json_files) / 1024 / 1024, 2)
            }
        else:
            status[name] = {
                "path": str(path),
                "type": "file",
                "exists": exists,
                "size_mb": round(path.stat().st_size / 1024 / 1024, 2) if exists else 0
            }
    return status

def ensure_output_dirs():
    """Create output directories if they don't exist."""
    for dir_path in [
        RESULTS_DIR,
        ESSENCE_OUTPUT_DIR,
        DOUBLE_DIP_OUTPUT_DIR,
        TRIPLE_DIP_OUTPUT_DIR,
        CALIBRATION_OUTPUT_DIR,
        TEMPORAL_OUTPUT_DIR,
    ]:
        dir_path.mkdir(parents=True, exist_ok=True)

# =============================================================================
# MAIN (for testing config)
# =============================================================================

if __name__ == "__main__":
    print("ESSENCE EXTRACTION Configuration")
    print("=" * 50)

    print("\nData Sources:")
    for name, status in validate_data_sources().items():
        exists = "OK" if status["exists"] else "MISSING"
        size = f"{status['size_mb']} MB" if status["exists"] else ""
        print(f"  {name}: [{exists}] {size}")
        print(f"         {status['path']}")

    print("\nOutput Directories:")
    ensure_output_dirs()
    print(f"  Essences: {ESSENCE_OUTPUT_DIR}")
    print(f"  Double-Dip: {DOUBLE_DIP_OUTPUT_DIR}")
    print(f"  Triple-Dip: {TRIPLE_DIP_OUTPUT_DIR}")
    print(f"  Calibration: {CALIBRATION_OUTPUT_DIR}")

    print("\nConfiguration valid!")
