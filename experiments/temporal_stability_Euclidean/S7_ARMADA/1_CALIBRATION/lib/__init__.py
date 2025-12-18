# 1_CALIBRATION/lib/
# Helper modules for S7 ARMADA experiments
# These are imported by run scripts, not run directly

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
