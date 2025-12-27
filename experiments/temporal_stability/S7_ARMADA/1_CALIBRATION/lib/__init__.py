"""
1_CALIBRATION/lib/
==================
Helper modules for S7 ARMADA experiments.

Modules:
- compare_baselines: Baseline comparison and ARMADA_MAP updates
- triple_dip: Exit survey infrastructure (exported below)
- fleet_loader: Fleet configuration from ARCHITECTURE_MATRIX.json (import directly)
- compare_persona_to_fleet: Persona-fleet alignment analysis
- update_persona_matrix: Matrix update utilities

NOTE: fleet_loader is intentionally NOT exported here - scripts import directly:
    from fleet_loader import load_architecture_matrix, get_full_armada, ...

Related Documents:
- ARCHITECTURE_MATRIX.json: Fleet configuration (ONE SOURCE OF TRUTH)
- 5_METHODOLOGY_DOMAINS.md: Methodology reference
"""

from .compare_baselines import (
    load_baseline,
    compare_ships,
    print_report,
    extract_sections,
    update_armada_map
)

# Triple-Dip Exit Survey Library (2025-12-17)
# Universal exit survey infrastructure - eliminates duplication across run scripts
from .triple_dip import (
    EXIT_PROBES,
    FINAL_STATEMENT_PROMPT,
    FINAL_STATEMENT_PROMPT_SHORT,
    run_exit_survey,
    validate_exit_responses,
    get_exit_survey_summary
)
