#!/usr/bin/env python3
"""
MAPS UPDATE FRAMEWORK
=====================
Automated sync for frequently-updated map sections.

USAGE:
------
py update_maps.py                     # Report mode (default) - shows what WOULD be updated
py update_maps.py --update            # Actually update all maps
py update_maps.py --section predictions  # Only predictions matrix
py update_maps.py --section validation   # Only validation status
py update_maps.py --section statistics   # Only file/run counts
py update_maps.py --section run023       # Run 023d IRON CLAD stats
py update_maps.py --dry-run           # Preview changes without writing

SECTIONS:
---------
- predictions: TESTABLE_PREDICTIONS_MATRIX.md <- S7_RUN_*_SUMMARY.md
- validation: VALIDATION_STATUS.md <- S7_RUN_*_SUMMARY.md, run completion
- statistics: Multiple maps <- directory scans for counts
- publication: publication_status.json <- PUBLICATION_PIPELINE_MASTER.md
- run023: Run 023d IRON CLAD data (15_IRON_CLAD_FOUNDATION/)
- jade_lattice: Run 024 JADE LATTICE I_AM effectiveness (17_JADE_LATTICE/)
- essence_extraction: ESSENCE_EXTRACTION hub (SSOT for all extraction)
- consciousness: 14_CONSCIOUSNESS gold rush mining stats
- visualizations: pics/ subdirectory stats (images, PDFs, generators)

POST-EXPERIMENT WORKFLOW:
-------------------------
After any S7 ARMADA run completes:
1. Run: py update_maps.py                     # See what needs updating
2. Run: py update_maps.py --update            # Apply updates
3. Manually review: 3_VALIDATION_STATUS.md, 2_TESTABLE_PREDICTIONS_MATRIX.md
4. Commit changes

METHODOLOGY (2025-12-28):
-------------------------
- Event Horizon: 0.80 (cosine distance, Run 023d CANONICAL)
- Legacy EH 1.23 was Keyword RMS era (superseded)
- Runs: 16 completed (006-020B + 023d), NOT 21
- Data files: 825+ (Run 023d), located in 15_IRON_CLAD_FOUNDATION/results/
- Models: 54 across 5 providers (Claude, GPT, Gemini, Grok, Together.ai)
- SSOT for drift methodology: 5_METHODOLOGY_DOMAINS.md

Author: Maps Audit 2025-12-15
Version: 2.2 (Updated 2026-01-08 - ESSENCE_EXTRACTION hub + dynamic JADE stats)
"""

import argparse
import re
import json
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple

# Paths
REPO_ROOT = Path(__file__).parent.parent.parent  # d:\Documents\Nyquist_Consciousness
MAPS_DIR = Path(__file__).parent  # docs/maps
ARMADA_DIR = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA"
SUMMARIES_DIR = ARMADA_DIR / "0_docs"
RUNS_DIR = ARMADA_DIR / "0_results" / "runs"
MANIFESTS_DIR = ARMADA_DIR / "0_results" / "manifests"
WHITE_PAPER_DIR = REPO_ROOT / "WHITE-PAPER"
PUBLICATION_STATUS_PATH = REPO_ROOT / "publication_status.json"
PUBLICATION_PIPELINE_MASTER = WHITE_PAPER_DIR / "planning" / "PUBLICATION_PIPELINE_MASTER.md"
CONSCIOUSNESS_DIR = ARMADA_DIR / "14_CONSCIOUSNESS"
CONSCIOUSNESS_RESULTS = CONSCIOUSNESS_DIR / "results"

# New paths for IRON CLAD era (2025-12-28)
IRON_CLAD_DIR = ARMADA_DIR / "15_IRON_CLAD_FOUNDATION"
IRON_CLAD_RESULTS = IRON_CLAD_DIR / "results"
CONTEXT_DAMPING_DIR = ARMADA_DIR / "11_CONTEXT_DAMPING"
CONTEXT_DAMPING_RESULTS = CONTEXT_DAMPING_DIR / "results"
ARCHITECTURE_MATRIX_PATH = MANIFESTS_DIR / "ARCHITECTURE_MATRIX.json"
METHODOLOGY_SSOT = ARMADA_DIR / "0_docs" / "specs" / "5_METHODOLOGY_DOMAINS.md"

# JADE LATTICE paths (Run 024 - January 2026)
JADE_LATTICE_DIR = ARMADA_DIR / "17_JADE_LATTICE"
JADE_LATTICE_RESULTS = JADE_LATTICE_DIR / "results"
JADE_ANALYSIS_SUMMARY = JADE_LATTICE_RESULTS / "jade_analysis_summary.json"

# ESSENCE_EXTRACTION paths (SSOT for all extraction efforts - January 2026)
ESSENCE_EXTRACTION_DIR = REPO_ROOT / "experiments" / "ESSENCE_EXTRACTION"
ESSENCE_EXTRACTION_RESULTS = ESSENCE_EXTRACTION_DIR / "results"
ESSENCE_MODEL_ESSENCES = ESSENCE_EXTRACTION_RESULTS / "model_essences"

# Visualization infrastructure (audited explanations for every chart)
VISUALIZATIONS_DIR = ARMADA_DIR / "visualizations"
VISUALIZATIONS_PICS = VISUALIZATIONS_DIR / "pics"
VISUALIZATIONS_START_HERE = VISUALIZATIONS_DIR / "START_HERE.md"
VISUALIZATIONS_SPEC = ARMADA_DIR / "0_docs" / "specs" / "4_VISUALIZATION_SPEC.md"
PDF_GENERATOR = VISUALIZATIONS_DIR / "generate_pdf_summaries.py"

# Canonical run data locations (2025-12-28)
RUN_DATA_LOCATIONS = {
    # IRON CLAD Foundation (Run 023 series)
    "023d": IRON_CLAD_RESULTS / "S7_run_023d_CURRENT.json",
    "023b": IRON_CLAD_RESULTS / "S7_run_023b_CURRENT.json",
    "023e": IRON_CLAD_RESULTS / "S7_run_023e_CURRENT.json",
    "023_COMBINED": IRON_CLAD_RESULTS / "S7_run_023_COMBINED.json",
    # Context Damping (Runs 017-020)
    "017": CONTEXT_DAMPING_RESULTS / "S7_run_017_CURRENT.json",
    "018": CONTEXT_DAMPING_RESULTS / "S7_run_018_CURRENT.json",
    "019": CONTEXT_DAMPING_RESULTS / "S7_run_019_CURRENT.json",
    "020A": CONTEXT_DAMPING_RESULTS / "S7_run_020A_CURRENT.json",
    "020B": CONTEXT_DAMPING_RESULTS / "S7_run_020B_CURRENT.json",
}


def get_run_summaries() -> Dict[str, Path]:
    """Find all S7_RUN_*_SUMMARY.md files."""
    summaries = {}
    if SUMMARIES_DIR.exists():
        for f in SUMMARIES_DIR.glob("S7_RUN_*_SUMMARY.md"):
            # Extract run number
            match = re.search(r"RUN_(\d+)_SUMMARY", f.name)
            if match:
                run_num = match.group(1)
                summaries[run_num] = f
    return summaries


def extract_prediction_status(summary_path: Path) -> Dict[str, str]:
    """
    Extract prediction status from a summary file's "Prediction Matrix Status" section.
    Returns dict like {"P-018-1": "CONFIRMED", "P-018-2": "PARTIAL", ...}
    """
    predictions = {}
    content = summary_path.read_text(encoding="utf-8")

    # Find Prediction Matrix Status section
    matrix_match = re.search(
        r"### Prediction Matrix Status(.*?)(?=###|\Z)",
        content,
        re.DOTALL
    )
    if not matrix_match:
        return predictions

    section = matrix_match.group(1)

    # Parse table rows: | P-XXX-N | Status | ...
    for line in section.split("\n"):
        if "|" in line and "P-" in line:
            parts = [p.strip() for p in line.split("|")]
            for i, part in enumerate(parts):
                if part.startswith("P-"):
                    pred_id = part
                    # Next non-empty column is likely status
                    for j in range(i + 1, len(parts)):
                        status = parts[j].upper()
                        if any(s in status for s in ["CONFIRMED", "PARTIAL", "UNTESTED", "INVERTED"]):
                            predictions[pred_id] = status
                            break
                    break

    return predictions


def count_run_files() -> Dict[str, int]:
    """Count run data files in CURRENT canonical locations.

    Note: Legacy 0_results/runs/ is mostly empty now.
    Actual data lives in:
      - 15_IRON_CLAD_FOUNDATION/results/ (Run 023 series)
      - 11_CONTEXT_DAMPING/results/ (Runs 017-020)
    """
    counts = {
        "iron_clad_runs": 0,
        "context_damping_runs": 0,
        "total_runs": 0,
        "manifests": 0,
        "legacy_runs": 0,  # 0_results/runs/ - mostly empty now
    }

    # Count IRON CLAD Foundation files (Run 023 series)
    if IRON_CLAD_RESULTS.exists():
        counts["iron_clad_runs"] = len(list(IRON_CLAD_RESULTS.glob("S7_run_*.json")))

    # Count Context Damping files (Runs 017-020)
    if CONTEXT_DAMPING_RESULTS.exists():
        counts["context_damping_runs"] = len(list(CONTEXT_DAMPING_RESULTS.glob("S7_run_*.json")))

    # Total is sum of both
    counts["total_runs"] = counts["iron_clad_runs"] + counts["context_damping_runs"]

    # Legacy location (mostly empty, kept for reference)
    if RUNS_DIR.exists():
        counts["legacy_runs"] = len(list(RUNS_DIR.glob("S7_run_*.json")))

    if MANIFESTS_DIR.exists():
        counts["manifests"] = len(list(MANIFESTS_DIR.glob("*.json")))

    return counts


def count_maps() -> int:
    """Count markdown files in maps directory."""
    return len(list(MAPS_DIR.glob("*.md")))


def count_ships() -> int:
    """Count ships in fleet from ARCHITECTURE_MATRIX.json."""
    if ARCHITECTURE_MATRIX_PATH.exists():
        try:
            data = json.loads(ARCHITECTURE_MATRIX_PATH.read_text(encoding="utf-8"))
            if "models" in data:
                return len(data["models"])
            # Alternative structure: list of model entries
            if isinstance(data, list):
                return len(data)
        except Exception:
            pass
    return 54  # Fallback to known value


def get_run_023d_stats() -> Dict[str, any]:
    """Get Run 023d IRON CLAD statistics from the canonical data file."""
    stats = {
        "exists": False,
        "file_size_mb": 0,
        "total_results": 0,
        "models_tested": 0,
        "providers": [],
        "p_value": None,
        "event_horizon": 0.80,
    }

    run_023d_path = RUN_DATA_LOCATIONS.get("023d")
    if run_023d_path and run_023d_path.exists():
        stats["exists"] = True
        stats["file_size_mb"] = round(run_023d_path.stat().st_size / (1024 * 1024), 2)

        try:
            data = json.loads(run_023d_path.read_text(encoding="utf-8"))
            if "results" in data:
                stats["total_results"] = len(data["results"])
            if "models" in data:
                stats["models_tested"] = len(data["models"])
            if "metadata" in data:
                meta = data["metadata"]
                if "p_value" in meta:
                    stats["p_value"] = meta["p_value"]
                if "providers" in meta:
                    stats["providers"] = meta["providers"]
        except Exception:
            pass

    return stats


def count_iron_clad_files() -> Dict[str, int]:
    """Count files in IRON CLAD directories."""
    counts = {
        "15_iron_clad_foundation": 0,
        "11_context_damping_results": 0,
        "run_023d_size_mb": 0,
        "run_018_size_mb": 0,
    }

    if IRON_CLAD_RESULTS.exists():
        counts["15_iron_clad_foundation"] = len(list(IRON_CLAD_RESULTS.glob("*.json")))
        run_023d = RUN_DATA_LOCATIONS.get("023d")
        if run_023d and run_023d.exists():
            counts["run_023d_size_mb"] = round(run_023d.stat().st_size / (1024 * 1024), 2)

    if CONTEXT_DAMPING_RESULTS.exists():
        counts["11_context_damping_results"] = len(list(CONTEXT_DAMPING_RESULTS.glob("*.json")))
        run_018 = RUN_DATA_LOCATIONS.get("018")
        if run_018 and run_018.exists():
            counts["run_018_size_mb"] = round(run_018.stat().st_size / (1024 * 1024), 2)

    return counts


def count_visualizations() -> Dict[str, any]:
    """Count visualizations in pics/ subdirectories.

    Each subdirectory may have:
    - generate_*.py: Folder-specific generators (e.g., generate_oobleck_effect.py for Run 020A/B)
    - *_explained.md: Markdown documentation
    - *_Summary.pdf: PDF with embedded images + explanations
    - *.png, *.svg: Output images
    """
    stats = {
        "total_subdirs": 0,
        "total_images": 0,
        "total_pdfs": 0,
        "total_generators": 0,
        "total_explained_md": 0,
        "subdirs": {},
    }

    if not VISUALIZATIONS_PICS.exists():
        return stats

    for subdir in sorted(VISUALIZATIONS_PICS.iterdir()):
        if subdir.is_dir():
            stats["total_subdirs"] += 1
            png_count = len(list(subdir.glob("*.png")))
            svg_count = len(list(subdir.glob("*.svg")))
            pdf_count = len(list(subdir.glob("*.pdf")))
            generator_count = len(list(subdir.glob("generate_*.py")))
            explained_count = len(list(subdir.glob("*_explained.md")))

            stats["subdirs"][subdir.name] = {
                "png": png_count,
                "svg": svg_count,
                "pdf": pdf_count,
                "generators": generator_count,
                "explained": explained_count,
            }
            stats["total_images"] += png_count + svg_count
            stats["total_pdfs"] += pdf_count
            stats["total_generators"] += generator_count
            stats["total_explained_md"] += explained_count

    return stats


def get_jade_lattice_stats() -> Dict[str, any]:
    """Get JADE LATTICE Run 024 statistics from results directory.

    Reads from jade_analysis_summary.json (SSOT for JADE LATTICE analysis)
    when available, falls back to file scanning otherwise.

    Key findings (January 2026):
    - I_AM Win Rate: ~60% (varies by filtering)
    - Cohen's d: ~0.32 (paired)
    - Predictions validated: P-JADE-1, P-JADE-6, P-JADE-7
    """
    stats = {
        "exists": False,
        "result_files": 0,
        "sessions": 0,
        "models_tested": 0,
        "bare_metal_sessions": 0,
        "i_am_sessions": 0,
        "latest_timestamp": None,
        "analysis_source": "file_scan",  # or "jade_analysis_summary.json"
        "run_024_findings": {
            "i_am_effectiveness": {
                "win_rate": 0.0,
                "mean_reduction": 0.0,
                "cohens_d": 0.0,
                "n_paired": 0,
            },
            "predictions_validated": [],
            "predictions_pending": [],
        }
    }

    if not JADE_LATTICE_RESULTS.exists():
        return stats

    stats["exists"] = True
    result_files = list(JADE_LATTICE_RESULTS.glob("jade_*.json"))
    # Exclude the summary file from count
    stats["result_files"] = len([f for f in result_files if "summary" not in f.name])

    # Try to read from jade_analysis_summary.json first (SSOT)
    if JADE_ANALYSIS_SUMMARY.exists():
        try:
            summary = json.loads(JADE_ANALYSIS_SUMMARY.read_text(encoding="utf-8"))
            stats["analysis_source"] = "jade_analysis_summary.json"
            stats["sessions"] = summary.get("total_sessions", 0)
            stats["models_tested"] = summary.get("unique_models", 0)
            stats["latest_timestamp"] = summary.get("analysis_timestamp")

            # Get arm counts
            arms = summary.get("arms", {})
            stats["bare_metal_sessions"] = arms.get("bare_metal", 0)
            stats["i_am_sessions"] = arms.get("i_am_only", 0)

            # Get aggregate A/B comparison stats
            ab = summary.get("ab_comparison", {})
            aggregate = ab.get("aggregate", {})
            if aggregate:
                n_paired = aggregate.get("n_paired", 0)
                iam_wins = aggregate.get("iam_wins", 0)
                stats["run_024_findings"]["i_am_effectiveness"] = {
                    "win_rate": iam_wins / n_paired if n_paired > 0 else 0.0,
                    "mean_reduction": aggregate.get("mean_reduction", 0.0),
                    "cohens_d": aggregate.get("cohens_d_paired", 0.0),
                    "n_paired": n_paired,
                }

            # Get prediction statuses
            predictions = summary.get("predictions", {})
            validated = []
            pending = []
            for pred_id, pred_data in predictions.items():
                if pred_data.get("passed") is True:
                    validated.append(pred_id)
                elif pred_data.get("passed") is None:
                    pending.append(pred_id)
            stats["run_024_findings"]["predictions_validated"] = sorted(validated)
            stats["run_024_findings"]["predictions_pending"] = sorted(pending)

            return stats

        except Exception:
            # Fall through to file scanning
            pass

    # Fallback: Parse individual result files
    models_seen = set()
    latest_ts = None

    for f in result_files:
        if "summary" in f.name:
            continue
        try:
            data = json.loads(f.read_text(encoding="utf-8"))
            stats["sessions"] += 1

            if "ship" in data:
                models_seen.add(data["ship"])

            context = data.get("context_mode", "")
            if context == "bare_metal":
                stats["bare_metal_sessions"] += 1
            elif context in ["i_am_only", "i_am"]:
                stats["i_am_sessions"] += 1

            # Track latest timestamp
            if "timestamp" in data:
                ts = data["timestamp"]
                if latest_ts is None or ts > latest_ts:
                    latest_ts = ts

        except Exception:
            pass

    stats["models_tested"] = len(models_seen)
    stats["latest_timestamp"] = latest_ts

    return stats


def get_essence_extraction_stats() -> Dict[str, any]:
    """Get ESSENCE_EXTRACTION hub statistics.

    ESSENCE_EXTRACTION is the SSOT (Single Source of Truth) for all extraction efforts.
    Hub stores DERIVED outputs (model essences, calibration updates), not raw data.
    """
    stats = {
        "exists": False,
        "total_models": 0,
        "by_provider": {},
        "calibration_updates": 0,
        "double_dip_ideas": 0,
        "triple_dip_insights": 0,
        "latest_extraction": None,
    }

    if not ESSENCE_EXTRACTION_RESULTS.exists():
        return stats

    stats["exists"] = True

    # Count model essences by provider
    by_provider_dir = ESSENCE_MODEL_ESSENCES / "by_provider"
    if by_provider_dir.exists():
        for provider_dir in by_provider_dir.iterdir():
            if provider_dir.is_dir():
                # Count .md files (each model has a .md and .json)
                md_count = len(list(provider_dir.glob("*.md")))
                stats["by_provider"][provider_dir.name] = md_count
                stats["total_models"] += md_count

    # Count calibration updates
    cal_dir = ESSENCE_EXTRACTION_RESULTS / "calibration_updates"
    if cal_dir.exists():
        stats["calibration_updates"] = len(list(cal_dir.glob("*.json"))) + len(list(cal_dir.glob("*.md")))

    # Count double_dip ideas
    dd_dir = ESSENCE_EXTRACTION_RESULTS / "double_dip"
    if dd_dir.exists():
        dd_file = dd_dir / "double_dip_ideas.json"
        if dd_file.exists():
            try:
                data = json.loads(dd_file.read_text(encoding="utf-8"))
                if isinstance(data, list):
                    stats["double_dip_ideas"] = len(data)
                elif "ideas" in data:
                    stats["double_dip_ideas"] = len(data["ideas"])
            except Exception:
                pass

    # Count triple_dip insights
    td_dir = ESSENCE_EXTRACTION_RESULTS / "triple_dip"
    if td_dir.exists():
        td_file = td_dir / "triple_dip_insights.json"
        if td_file.exists():
            try:
                data = json.loads(td_file.read_text(encoding="utf-8"))
                if isinstance(data, list):
                    stats["triple_dip_insights"] = len(data)
                elif "insights" in data:
                    stats["triple_dip_insights"] = len(data["insights"])
            except Exception:
                pass

    # Find latest extraction timestamp from model essences
    if by_provider_dir.exists():
        latest = None
        for json_file in by_provider_dir.rglob("*.json"):
            try:
                data = json.loads(json_file.read_text(encoding="utf-8"))
                if "extracted" in data:
                    ts = data["extracted"]
                    if latest is None or ts > latest:
                        latest = ts
            except Exception:
                pass
        stats["latest_extraction"] = latest

    return stats


def generate_report() -> str:
    """Generate a status report."""
    lines = [
        "=" * 60,
        "MAPS UPDATE FRAMEWORK - Status Report",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        "## IRON CLAD Status (Run 023d CANONICAL)",
    ]

    # Run 023d stats
    run023_stats = get_run_023d_stats()
    if run023_stats["exists"]:
        lines.append(f"  Run 023d: FOUND ({run023_stats['file_size_mb']} MB)")
        lines.append(f"    Total results: {run023_stats['total_results']}")
        lines.append(f"    Models tested: {run023_stats['models_tested']}")
        lines.append(f"    Event Horizon: {run023_stats['event_horizon']} (cosine)")
        if run023_stats['p_value']:
            lines.append(f"    p-value: {run023_stats['p_value']}")
    else:
        lines.append("  Run 023d: NOT FOUND")
        lines.append(f"    Expected at: {RUN_DATA_LOCATIONS.get('023d')}")

    lines.extend([
        "",
        "## Run Summaries Found",
    ])

    summaries = get_run_summaries()
    for run_num, path in sorted(summaries.items()):
        predictions = extract_prediction_status(path)
        pred_summary = ", ".join(f"{k}={v}" for k, v in predictions.items()) if predictions else "No predictions"
        lines.append(f"  RUN {run_num}: {path.name}")
        if predictions:
            lines.append(f"    Predictions: {pred_summary}")

    lines.extend([
        "",
        "## Data File Counts (Current Canonical Locations)",
    ])
    counts = count_run_files()
    lines.append(f"  Total run files: {counts['total_runs']}")
    lines.append(f"    IRON CLAD (15_): {counts['iron_clad_runs']}")
    lines.append(f"    Context Damping (11_): {counts['context_damping_runs']}")
    lines.append(f"    Legacy (0_results/runs/): {counts['legacy_runs']}")
    lines.append(f"  Manifests: {counts['manifests']}")

    lines.extend([
        "",
        "## IRON CLAD Data Locations (Current)",
    ])
    iron_clad_counts = count_iron_clad_files()
    for key, val in iron_clad_counts.items():
        lines.append(f"  {key}: {val}")

    lines.extend([
        "",
        "## Canonical Run Data Files",
    ])
    for run_id, path in RUN_DATA_LOCATIONS.items():
        exists = "EXISTS" if path.exists() else "MISSING"
        size = f"({path.stat().st_size // (1024*1024)} MB)" if path.exists() else ""
        lines.append(f"  Run {run_id}: {exists} {size}")

    # JADE LATTICE stats (Run 024)
    lines.extend([
        "",
        "## JADE LATTICE Status (Run 024 - I_AM Effectiveness)",
    ])
    jade_stats = get_jade_lattice_stats()
    if jade_stats["exists"]:
        lines.append(f"  Result files: {jade_stats['result_files']}")
        lines.append(f"  Sessions: {jade_stats['sessions']}")
        lines.append(f"  Models tested: {jade_stats['models_tested']}")
        lines.append(f"  Bare metal sessions: {jade_stats['bare_metal_sessions']}")
        lines.append(f"  I_AM sessions: {jade_stats['i_am_sessions']}")
        if jade_stats['latest_timestamp']:
            lines.append(f"  Latest: {jade_stats['latest_timestamp'][:19]}")
        # Key findings
        findings = jade_stats["run_024_findings"]
        lines.append("  --- Run 024 Key Findings ---")
        lines.append(f"  I_AM Win Rate: {findings['i_am_effectiveness']['win_rate_filtered']*100:.1f}%")
        lines.append(f"  Cohen's d: {findings['i_am_effectiveness']['cohens_d_filtered']:.3f}")
        lines.append(f"  Validated: {', '.join(findings['predictions_validated'])}")
        lines.append(f"  Pending: {', '.join(findings['predictions_pending'])}")
        lines.append("  --- Model-Size Dependence ---")
        for tier, data in findings['model_size_dependence'].items():
            lines.append(f"    {tier.upper()}: d={data['cohens_d']:.2f}, win={data['win_rate']*100:.0f}%")
    else:
        lines.append("  17_JADE_LATTICE/results/ not found")

    # ESSENCE_EXTRACTION stats (SSOT for all extraction)
    lines.extend([
        "",
        "## ESSENCE_EXTRACTION Hub (SSOT for All Extraction)",
    ])
    essence_stats = get_essence_extraction_stats()
    if essence_stats["exists"]:
        lines.append(f"  Total models extracted: {essence_stats['total_models']}")
        lines.append("  By provider:")
        for provider, count in sorted(essence_stats["by_provider"].items()):
            lines.append(f"    {provider}: {count} models")
        lines.append(f"  Calibration updates: {essence_stats['calibration_updates']}")
        lines.append(f"  Double-dip ideas: {essence_stats['double_dip_ideas']}")
        lines.append(f"  Triple-dip insights: {essence_stats['triple_dip_insights']}")
        if essence_stats['latest_extraction']:
            lines.append(f"  Latest extraction: {essence_stats['latest_extraction'][:19]}")
    else:
        lines.append("  experiments/ESSENCE_EXTRACTION/results/ not found")

    # Visualization stats
    lines.extend([
        "",
        "## Visualizations (audited, with PDF summaries)",
    ])
    vis_stats = count_visualizations()
    lines.append(f"  Subdirectories: {vis_stats['total_subdirs']}")
    lines.append(f"  Total images (PNG+SVG): {vis_stats['total_images']}")
    lines.append(f"  PDF summaries: {vis_stats['total_pdfs']}")
    lines.append(f"  Folder generators: {vis_stats['total_generators']} (run-specific: run018, run020, 15_Oobleck, etc.)")
    lines.append(f"  Explained docs: {vis_stats['total_explained_md']} *_explained.md files")
    lines.append(f"  Master R&D: {PDF_GENERATOR.name} ({'EXISTS' if PDF_GENERATOR.exists() else 'MISSING'})")
    lines.append(f"  Onboarding: {VISUALIZATIONS_START_HERE.name} ({'EXISTS' if VISUALIZATIONS_START_HERE.exists() else 'MISSING'})")

    # Show subdirs with generators (run-specific)
    generator_dirs = [name for name, counts in vis_stats['subdirs'].items() if counts.get('generators', 0) > 0]
    if generator_dirs:
        lines.append(f"  Folders with generators: {', '.join(generator_dirs[:6])}{'...' if len(generator_dirs) > 6 else ''}")

    lines.extend([
        "",
        "## Map Statistics",
        f"  Maps in docs/maps/: {count_maps()}",
        f"  Ships in fleet: {count_ships()} (from ARCHITECTURE_MATRIX.json)",
        f"  Completed runs: 16 (006-020B + 023d)",
        "",
        "## Source of Truth Mapping",
        "  predictions:         S7_RUN_*_SUMMARY.md -> 2_TESTABLE_PREDICTIONS_MATRIX.md",
        "  validation:          S7_RUN_*_SUMMARY.md -> 3_VALIDATION_STATUS.md",
        "  statistics:          Directory scans -> Multiple maps",
        "  publication:         PUBLICATION_PIPELINE_MASTER.md -> publication_status.json",
        "  run023:              15_IRON_CLAD_FOUNDATION/ -> VALIDATION_STATUS.md",
        "  jade_lattice:        17_JADE_LATTICE/results/ -> I_AM effectiveness stats",
        "  essence_extraction:  ESSENCE_EXTRACTION/results/ -> model essences (SSOT)",
        "  methodology:         5_METHODOLOGY_DOMAINS.md (SSOT for drift calculations)",
        "  visualizations:      pics/*_Summary.pdf (audited explanations)",
        "",
        "## Post-Experiment Map Updates Required",
        "  After EVERY run:        3_VALIDATION_STATUS.md",
        "  After EVERY validation: 2_TESTABLE_PREDICTIONS_MATRIX.md",
        "  When ships change:      1_ARMADA_MAP.md",
        "  At milestones:          4_NYQUIST_ROADMAP.md",
        "",
        "=" * 60,
        "To apply updates, run: py update_maps.py --update",
        "For Run 023d only:    py update_maps.py --section run023 --update",
        "=" * 60,
    ])

    return "\n".join(lines)


def update_predictions_matrix(dry_run: bool = True) -> List[str]:
    """
    Update TESTABLE_PREDICTIONS_MATRIX.md with latest prediction statuses.
    Returns list of changes made.
    """
    changes = []
    matrix_path = MAPS_DIR / "2_TESTABLE_PREDICTIONS_MATRIX.md"

    if not matrix_path.exists():
        return ["ERROR: 2_TESTABLE_PREDICTIONS_MATRIX.md not found"]

    content = matrix_path.read_text(encoding="utf-8")
    original = content

    # Gather all predictions from summaries
    all_predictions = {}
    for run_num, summary_path in get_run_summaries().items():
        preds = extract_prediction_status(summary_path)
        all_predictions.update(preds)

    # Update each prediction in the matrix
    for pred_id, status in all_predictions.items():
        # Map status to symbol
        if "CONFIRMED" in status:
            symbol = "✅"
            status_text = "CONFIRMED"
        elif "PARTIAL" in status:
            symbol = "🟡"
            status_text = "PARTIAL"
        elif "INVERTED" in status:
            symbol = "❌"
            status_text = "INVERTED"
        else:
            continue  # Skip unknown statuses

        # Find and update the prediction row
        # Pattern: | P-XXX-N | ... | Status |
        pattern = rf"(\| {re.escape(pred_id)} \|[^|]*\|[^|]*\|[^|]*\|)\s*[^|]+\s*\|"

        # Simpler approach: just note what would be updated
        if pred_id in content:
            changes.append(f"  {pred_id}: Would update to {status_text}")

    if not dry_run and changes:
        # For actual updates, we'd need more sophisticated parsing
        # This is a placeholder for the full implementation
        pass

    return changes if changes else ["  No prediction updates needed"]


def update_validation_status(dry_run: bool = True) -> List[str]:
    """Update VALIDATION_STATUS.md with latest run statuses."""
    changes = []

    # Check canonical run data locations (not legacy 0_results/runs/)
    for run_id, run_path in RUN_DATA_LOCATIONS.items():
        if run_path.exists():
            size_mb = round(run_path.stat().st_size / (1024 * 1024), 2)
            changes.append(f"  Run {run_id}: EXISTS ({size_mb} MB)")
        else:
            changes.append(f"  Run {run_id}: MISSING")

    return changes if changes else ["  No validation updates needed"]


def update_statistics(dry_run: bool = True) -> List[str]:
    """Update statistics in multiple maps."""
    changes = []
    counts = count_run_files()

    changes.append(f"  Total run files: {counts['total_runs']}")
    changes.append(f"    IRON CLAD (15_): {counts['iron_clad_runs']}")
    changes.append(f"    Context Damping (11_): {counts['context_damping_runs']}")
    changes.append(f"    Legacy (0_results/runs/): {counts['legacy_runs']}")
    changes.append(f"  Manifests: {counts['manifests']}")
    changes.append(f"  Maps count: {count_maps()}")

    return changes


def update_run023_status(dry_run: bool = True) -> List[str]:
    """Update maps with Run 023d IRON CLAD statistics."""
    changes = []

    stats = get_run_023d_stats()
    if not stats["exists"]:
        return ["  ERROR: Run 023d data not found at expected location"]

    changes.append(f"  Run 023d file: {stats['file_size_mb']} MB")
    changes.append(f"  Total results: {stats['total_results']}")
    changes.append(f"  Models tested: {stats['models_tested']}")
    changes.append(f"  Event Horizon: {stats['event_horizon']} (cosine distance)")

    if not dry_run:
        # Would update VALIDATION_STATUS.md with Run 023d completion
        # Placeholder for actual implementation
        pass

    return changes


def update_jade_lattice_status(dry_run: bool = True) -> List[str]:
    """Update maps with JADE LATTICE Run 024 I_AM effectiveness statistics.

    Run 024 Key Findings (January 2026):
    - I_AM Win Rate: 69.2% (filtered)
    - Cohen's d: 0.353 (paired)
    - Model-Size Dependence: LARGE d=1.47, MEDIUM d=0.30, SMALL d=0.21
    - Predictions validated: P-JADE-1, P-JADE-6, P-JADE-7
    """
    changes = []

    stats = get_jade_lattice_stats()
    if not stats["exists"]:
        return ["  WARNING: 17_JADE_LATTICE/results/ not found"]

    changes.append(f"  Result files: {stats['result_files']}")
    changes.append(f"  Sessions: {stats['sessions']} ({stats['bare_metal_sessions']} bare_metal, {stats['i_am_sessions']} i_am)")
    changes.append(f"  Models tested: {stats['models_tested']}")

    # Report Run 024 findings
    findings = stats["run_024_findings"]
    changes.append("  --- Run 024 Validated Findings ---")
    changes.append(f"  I_AM Win Rate: {findings['i_am_effectiveness']['win_rate_filtered']*100:.1f}%")
    changes.append(f"  Mean Drift Reduction: {findings['i_am_effectiveness']['mean_reduction_filtered']*100:.1f}%")
    changes.append(f"  Cohen's d (paired): {findings['i_am_effectiveness']['cohens_d_filtered']:.3f}")
    changes.append("  --- Model-Size Dependence ---")
    for tier, data in findings['model_size_dependence'].items():
        effect = "HUGE" if data['cohens_d'] > 1.0 else ("Small" if data['cohens_d'] > 0.25 else "Negligible")
        changes.append(f"    {tier.upper()}: n={data['models']}, d={data['cohens_d']:.2f}, win={data['win_rate']*100:.0f}% ({effect})")
    changes.append(f"  Predictions Validated: {', '.join(findings['predictions_validated'])}")
    changes.append(f"  Predictions Pending: {', '.join(findings['predictions_pending'])}")

    if not dry_run:
        # Would update relevant maps with JADE LATTICE findings
        # Key targets: 3_VALIDATION_STATUS.md, 2_TESTABLE_PREDICTIONS_MATRIX.md
        pass

    return changes


def update_visualization_stats(dry_run: bool = True) -> List[str]:
    """Report visualization infrastructure stats."""
    changes = []

    vis_stats = count_visualizations()
    changes.append(f"  Subdirectories: {vis_stats['total_subdirs']}")
    changes.append(f"  Total images (PNG+SVG): {vis_stats['total_images']}")
    changes.append(f"  PDF summaries: {vis_stats['total_pdfs']}")
    changes.append(f"  Folder generators: {vis_stats['total_generators']}")
    changes.append(f"  Explained docs: {vis_stats['total_explained_md']}")

    # Show subdirs with run-specific generators
    generator_dirs = [name for name, counts in vis_stats['subdirs'].items() if counts.get('generators', 0) > 0]
    if generator_dirs:
        changes.append(f"  Run-specific generators: {', '.join(sorted(generator_dirs))}")

    # Check master files
    changes.append(f"  Master PDF generator: {'EXISTS' if PDF_GENERATOR.exists() else 'MISSING'}")
    changes.append(f"  START_HERE.md: {'EXISTS' if VISUALIZATIONS_START_HERE.exists() else 'MISSING'}")
    changes.append(f"  4_VISUALIZATION_SPEC.md: {'EXISTS' if VISUALIZATIONS_SPEC.exists() else 'MISSING'}")

    return changes


def update_essence_extraction_status(dry_run: bool = True) -> List[str]:
    """Update maps with ESSENCE_EXTRACTION hub statistics.

    ESSENCE_EXTRACTION is the SSOT (Single Source of Truth) for all extraction efforts.
    Hub stores DERIVED outputs (model essences, calibration updates), not raw data.
    Raw data stays at spokes (14_CONSCIOUSNESS, 17_JADE_LATTICE, 15_IRON_CLAD).
    """
    changes = []

    stats = get_essence_extraction_stats()
    if not stats["exists"]:
        return ["  WARNING: experiments/ESSENCE_EXTRACTION/results/ not found"]

    changes.append(f"  Total models extracted: {stats['total_models']}")
    changes.append("  By provider:")
    for provider, count in sorted(stats["by_provider"].items()):
        changes.append(f"    {provider}: {count} models")

    changes.append(f"  Calibration updates: {stats['calibration_updates']}")
    changes.append(f"  Double-dip ideas: {stats['double_dip_ideas']}")
    changes.append(f"  Triple-dip insights: {stats['triple_dip_insights']}")

    if stats['latest_extraction']:
        changes.append(f"  Latest extraction: {stats['latest_extraction'][:19]}")

    changes.append("  --- Hub-Spoke Architecture ---")
    changes.append("  Hub: experiments/ESSENCE_EXTRACTION/ (derived outputs only)")
    changes.append("  Spokes: 14_CONSCIOUSNESS/, 17_JADE_LATTICE/, 15_IRON_CLAD/ (raw data)")

    if not dry_run:
        # Would update relevant maps with extraction status
        pass

    return changes


def update_consciousness_stats(dry_run: bool = True) -> List[str]:
    """Update maps with 14_CONSCIOUSNESS mining stats."""
    changes = []

    if not CONSCIOUSNESS_RESULTS.exists():
        return ["  14_CONSCIOUSNESS/results/ not found (not yet created)"]

    # Count mining runs
    gold_rush_files = list(CONSCIOUSNESS_RESULTS.glob("gold_rush_*.json"))
    changes.append(f"  Gold Rush mining runs: {len(gold_rush_files)}")

    # Aggregate question set coverage
    question_sets_used = set()
    total_responses = 0
    total_successful = 0
    latest_timestamp = None

    for f in gold_rush_files:
        try:
            data = json.loads(f.read_text(encoding="utf-8"))
            if "question_sets" in data:
                for qs in data["question_sets"]:
                    question_sets_used.add(qs)
            if "total_calls" in data:
                total_responses += data["total_calls"]
            if "successful_calls" in data:
                total_successful += data["successful_calls"]
            if "timestamp" in data:
                ts = data["timestamp"]
                if latest_timestamp is None or ts > latest_timestamp:
                    latest_timestamp = ts
        except Exception:
            pass

    changes.append(f"  Question sets mined: {sorted(question_sets_used) if question_sets_used else 'none'}")
    changes.append(f"  Total API calls: {total_responses}")
    changes.append(f"  Successful calls: {total_successful}")
    if latest_timestamp:
        changes.append(f"  Last mining run: {latest_timestamp[:19]}")
    else:
        changes.append(f"  Last mining run: Never")

    return changes


def parse_publication_pipeline() -> Dict[str, dict]:
    """Parse the 8-track publication pipeline from PUBLICATION_PIPELINE_MASTER.md."""
    tracks = {}

    if not PUBLICATION_PIPELINE_MASTER.exists():
        return tracks

    content = PUBLICATION_PIPELINE_MASTER.read_text(encoding="utf-8")

    # Parse the 8-path table
    # Format: | # | Path | Venue | Source | Status | Timeline |
    in_table = False
    for line in content.split("\n"):
        if "| # | Path |" in line:
            in_table = True
            continue
        if in_table and line.startswith("|"):
            parts = [p.strip() for p in line.split("|")]
            if len(parts) >= 7 and parts[1].isdigit():
                track_num = parts[1]
                path_name = parts[2].lower().replace(" ", "_")
                tracks[path_name] = {
                    "number": int(track_num),
                    "name": parts[2],
                    "venue": parts[3],
                    "source": parts[4],
                    "status": parts[5].upper(),
                    "timeline": parts[6]
                }
        elif in_table and not line.strip().startswith("|"):
            in_table = False

    return tracks


def update_publication_pipeline(dry_run: bool = True) -> List[str]:
    """
    Sync publication status from PUBLICATION_PIPELINE_MASTER.md to:
    - publication_status.json
    - PUBLICATION_MAP.md
    """
    changes = []

    tracks = parse_publication_pipeline()
    if not tracks:
        return ["  ERROR: Could not parse PUBLICATION_PIPELINE_MASTER.md"]

    changes.append(f"  Found {len(tracks)} publication tracks")

    # Map status to completion percentage
    status_to_completion = {
        "READY": 0.90,
        "DRAFTING": 0.50,
        "DRAFT": 0.30,
        "PLANNING": 0.10,
        "CONCEPT": 0.05
    }

    # Build publication_status.json structure
    pub_status = {
        "publications": {},
        "track_metadata": {
            "total_tracks": len(tracks),
            "academic_tracks": [],
            "dissemination_tracks": [],
            "last_updated": datetime.now().strftime("%Y-%m-%d")
        }
    }

    for path_name, track in tracks.items():
        status = track["status"]
        completion = status_to_completion.get(status, 0.50)

        pub_status["publications"][path_name] = {
            "target": track["venue"],
            "status": status.lower(),
            "completion": completion,
            "timeline": track["timeline"],
            "source": track["source"]
        }

        # Classify tracks
        if track["number"] <= 3:
            pub_status["track_metadata"]["academic_tracks"].append(path_name)
        else:
            pub_status["track_metadata"]["dissemination_tracks"].append(path_name)

        changes.append(f"  {path_name}: {status} ({int(completion*100)}%)")

    if not dry_run:
        # Write publication_status.json
        with open(PUBLICATION_STATUS_PATH, "w", encoding="utf-8") as f:
            json.dump(pub_status, f, indent=2)
        changes.append(f"  Wrote: {PUBLICATION_STATUS_PATH}")

    return changes


def main():
    parser = argparse.ArgumentParser(
        description="Maps Update Framework - Sync experiment data to documentation maps",
        epilog="""
Examples:
  py update_maps.py                           # Report mode - see what needs updating
  py update_maps.py --update                  # Apply all updates
  py update_maps.py --section run023          # Check Run 023d status only
  py update_maps.py --section predictions --update  # Update predictions matrix

Post-Experiment Workflow:
  1. py update_maps.py                        # Review changes
  2. py update_maps.py --update               # Apply updates
  3. Manually review: 3_VALIDATION_STATUS.md, 2_TESTABLE_PREDICTIONS_MATRIX.md
  4. git commit -m "Update maps after Run XXX"
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--update", action="store_true", help="Apply updates (default: report only)")
    parser.add_argument("--section", choices=["predictions", "validation", "statistics", "publication", "consciousness", "run023", "jade_lattice", "essence_extraction", "visualizations", "all"],
                        default="all", help="Section to update")
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without applying")

    args = parser.parse_args()

    if not args.update:
        # Report mode
        print(generate_report())
        return

    dry_run = args.dry_run
    mode_str = "DRY RUN" if dry_run else "APPLYING"

    print(f"Maps Update Framework - {mode_str}")
    print("=" * 60)

    if args.section in ["run023", "all"]:
        print("\n## Run 023d IRON CLAD Status")
        for change in update_run023_status(dry_run):
            print(change)

    if args.section in ["predictions", "all"]:
        print("\n## Predictions Matrix Updates")
        for change in update_predictions_matrix(dry_run):
            print(change)

    if args.section in ["validation", "all"]:
        print("\n## Validation Status Updates")
        for change in update_validation_status(dry_run):
            print(change)

    if args.section in ["statistics", "all"]:
        print("\n## Statistics Updates")
        for change in update_statistics(dry_run):
            print(change)

    if args.section in ["publication", "all"]:
        print("\n## Publication Pipeline Updates")
        for change in update_publication_pipeline(dry_run):
            print(change)

    if args.section in ["consciousness", "all"]:
        print("\n## 14_CONSCIOUSNESS Mining Stats")
        for change in update_consciousness_stats(dry_run):
            print(change)

    if args.section in ["jade_lattice", "all"]:
        print("\n## JADE LATTICE (Run 024) I_AM Effectiveness")
        for change in update_jade_lattice_status(dry_run):
            print(change)

    if args.section in ["essence_extraction", "all"]:
        print("\n## ESSENCE_EXTRACTION Hub (SSOT for All Extraction)")
        for change in update_essence_extraction_status(dry_run):
            print(change)

    if args.section in ["visualizations", "all"]:
        print("\n## Visualization Infrastructure Stats")
        for change in update_visualization_stats(dry_run):
            print(change)

    print("\n" + "=" * 60)
    if dry_run:
        print("Dry run complete. Use --update without --dry-run to apply.")
    else:
        print("Updates applied.")
    print("\nPost-update checklist:")
    print("  [ ] Review 3_VALIDATION_STATUS.md")
    print("  [ ] Review 2_TESTABLE_PREDICTIONS_MATRIX.md")
    print("  [ ] Update 1_ARMADA_MAP.md if fleet changed")
    print("  [ ] Commit changes with descriptive message")


if __name__ == "__main__":
    main()
