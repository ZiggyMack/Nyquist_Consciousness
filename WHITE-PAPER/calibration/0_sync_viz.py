#!/usr/bin/env python3
"""
0_sync_viz.py - Visualization Sync Tool (PDFs + PNGs + Reviewer Feedback)
=========================================================================

A comprehensive sync tool for WHITE-PAPER visualizations:
1. Sync PDF summaries from S7_ARMADA to reviewer packages
2. Sync identified PNGs from visual_index.md to figures/publication/
3. Process reviewer visual requests (feedback loop)

PHILOSOPHY:
- Specific where we know what we need
- General where we need flexibility
- Conversational - asks questions when uncertain
- Reviewer feedback loop for continuous improvement

USAGE - PDF SYNC:
    python 0_sync_viz.py --check              # Check what needs syncing
    python 0_sync_viz.py --sync               # Sync all outdated PDFs
    python 0_sync_viz.py --sync 15_Oobleck_Effect  # Sync specific viz
    python 0_sync_viz.py --regenerate --sync  # Regenerate then sync
    python 0_sync_viz.py --interactive        # Interactive mode

USAGE - PNG SYNC (from visual_index.md):
    python 0_sync_viz.py --sync-pngs          # Sync identified PNGs
    python 0_sync_viz.py --sync-pngs --dry-run  # Preview what would sync
    python 0_sync_viz.py --sync-pngs --include-requests  # Include approved requests

USAGE - REVIEWER FEEDBACK LOOP:
    python 0_sync_viz.py --process-feedback   # Import feedback from packages/v4/feedback/
    python 0_sync_viz.py --requests           # Show pending visual requests
    python 0_sync_viz.py --request "name.png" "source_dir" "Reviewer"  # Add request manually
    python 0_sync_viz.py --approve "name.png" # Approve a request
    python 0_sync_viz.py --update-index       # Add approved to visual_index.md

Created: December 29, 2025
Author: Claude (VALIS Network)
Version: 2.0 - Added PNG sync + reviewer feedback loop
"""

import os
import sys
import json
import shutil
import argparse
import subprocess
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional

# Fix Windows console encoding for emojis
if sys.platform == 'win32':
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')

# =============================================================================
# CONFIGURATION - Specific where we know, general where we don't
# =============================================================================

# Base paths (specific - we know these)
REPO_ROOT = Path(__file__).parent.parent.parent
S7_ARMADA = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA"
VIZ_PICS = S7_ARMADA / "visualizations" / "pics"
WHITE_PAPER = REPO_ROOT / "WHITE-PAPER"
PACKAGES = WHITE_PAPER / "reviewers" / "packages"
VERSION_FILE = PACKAGES / "CURRENT_VERSION.json"
FIGURES_DIR = WHITE_PAPER / "figures"
VISUAL_INDEX = FIGURES_DIR / "visual_index.md"
FEEDBACK_DIR = PACKAGES / "v4" / "feedback"  # Reviewer feedback directory

# Known visualization directories that have PDF summaries
# Format: {dir_name: {"pdf_name": str, "png_generator": str, "pdf_generator": str}}
KNOWN_VIZ_DIRS = {
    "10_PFI_Dimensional": {
        "pdf_name": "10_PFI_Dimensional_Summary.pdf",
        "png_generator": "generate_pfi_dimensional.py",
        "pdf_generator": "md_to_pdf.py",  # Converts explained.md to Summary.pdf
        "data_sources": ["S7_run_023d_CURRENT.json"],
    },
    "15_Oobleck_Effect": {
        "pdf_name": "15_Oobleck_Effect_Summary.pdf",
        "png_generator": "generate_oobleck_effect.py",
        "pdf_generator": "generate_pdf_summary.py",
        "data_sources": ["S7_run_020A_CURRENT.json", "S7_run_020B_CURRENT.json"],
    },
    "run018": {
        "pdf_name": "run018_Summary.pdf",
        "png_generator": "run018_persona_analysis.py",  # Main one
        "pdf_generator": "generate_pdf_summary.py",
        "data_sources": ["S7_run_018_CURRENT.json"],
    },
    "run020": {
        "pdf_name": "run020_Summary.pdf",
        "png_generator": "generate_run020_visualizations.py",
        "pdf_generator": "generate_pdf_summary.py",
        "data_sources": ["S7_run_020A_CURRENT.json", "S7_run_020B_CURRENT.json"],
    },
}

# These are discovered dynamically - we don't want to be too specific
# Format populated at runtime: {dir_name: {"pdf_name": str, ...}}
DISCOVERED_VIZ_DIRS = {}


# =============================================================================
# VERSION MANAGEMENT - Read from CURRENT_VERSION.json
# =============================================================================

def load_version_config() -> dict:
    """Load version configuration from CURRENT_VERSION.json."""
    if VERSION_FILE.exists():
        with open(VERSION_FILE, 'r') as f:
            return json.load(f)
    return {
        "current_version": "v4",
        "versioning_rules": {},
        "next_version_triggers": []
    }


def get_current_version() -> str:
    """Get the current target version for syncing."""
    config = load_version_config()
    return config.get("current_version", "v4")


def should_bump_version(reason: str) -> Tuple[bool, str]:
    """
    Check if a given reason warrants a version bump.
    Returns (should_bump, explanation).
    """
    config = load_version_config()
    triggers = config.get("next_version_triggers", [])
    stay_rules = config.get("versioning_rules", {}).get("stay_on_current", [])
    bump_rules = config.get("versioning_rules", {}).get("create_new_version", [])

    reason_lower = reason.lower()

    # Check if it matches a "stay on current" rule
    for rule in stay_rules:
        if any(word in reason_lower for word in rule.lower().split()):
            return False, f"Matches stay rule: {rule}"

    # Check if it matches a "create new version" rule
    for rule in bump_rules:
        if any(word in reason_lower for word in rule.lower().split()):
            return True, f"Matches bump rule: {rule}"

    # Check specific triggers
    for trigger in triggers:
        if any(word in reason_lower for word in trigger.lower().split()):
            return True, f"Matches trigger: {trigger}"

    return False, "No matching rule - defaulting to current version"


def print_version_info():
    """Print current version information."""
    config = load_version_config()
    current = config.get("current_version", "unknown")
    created = config.get("created", "unknown")
    reason = config.get("reason", "unknown")

    print(f"\n📦 Package Version: {current}")
    print(f"   Created: {created}")
    print(f"   Reason: {reason}")

    triggers = config.get("next_version_triggers", [])
    if triggers:
        print(f"\n   Next version triggers:")
        for t in triggers:
            print(f"   - {t}")


# =============================================================================
# DISCOVERY - Stay general, find what's there
# =============================================================================

def discover_visualization_dirs() -> Dict[str, dict]:
    """
    Discover all visualization directories that might need syncing.
    Combines known dirs with anything else we find.
    """
    all_dirs = {}

    # Start with known dirs
    all_dirs.update(KNOWN_VIZ_DIRS)

    # Discover any additional directories with PDF summaries
    if VIZ_PICS.exists():
        for subdir in VIZ_PICS.iterdir():
            if subdir.is_dir() and subdir.name not in all_dirs:
                # Look for PDF files
                pdfs = list(subdir.glob("*Summary*.pdf")) + list(subdir.glob("*_Summary.pdf"))
                if pdfs:
                    # Found a PDF - add to discovered
                    pdf_name = pdfs[0].name

                    # Try to find generators
                    png_gen = None
                    pdf_gen = None
                    for py_file in subdir.glob("*.py"):
                        if "generate" in py_file.name.lower():
                            if "pdf" in py_file.name.lower():
                                pdf_gen = py_file.name
                            else:
                                png_gen = py_file.name

                    all_dirs[subdir.name] = {
                        "pdf_name": pdf_name,
                        "png_generator": png_gen,
                        "pdf_generator": pdf_gen,
                        "data_sources": [],  # Unknown - would need investigation
                        "_discovered": True,  # Flag that this was auto-discovered
                    }

    return all_dirs


def get_file_mtime(path: Path) -> Optional[datetime]:
    """Get modification time of a file, or None if it doesn't exist."""
    if path.exists():
        return datetime.fromtimestamp(path.stat().st_mtime)
    return None


def get_latest_data_mtime(data_sources: List[str]) -> Optional[datetime]:
    """Get the latest modification time among data source files."""
    data_dir = S7_ARMADA / "11_CONTEXT_DAMPING" / "results"
    latest = None

    for source in data_sources:
        source_path = data_dir / source
        mtime = get_file_mtime(source_path)
        if mtime and (latest is None or mtime > latest):
            latest = mtime

    return latest


# =============================================================================
# STATUS CHECKING
# =============================================================================

def check_sync_status() -> Dict[str, dict]:
    """
    Check the sync status of all visualization PDFs.
    Returns a dict with status info for each visualization.
    """
    all_dirs = discover_visualization_dirs()
    status = {}

    for dir_name, config in all_dirs.items():
        viz_dir = VIZ_PICS / dir_name
        if not viz_dir.exists():
            status[dir_name] = {"exists": False, "status": "missing"}
            continue

        pdf_path = viz_dir / config["pdf_name"]
        pdf_mtime = get_file_mtime(pdf_path)

        # Check PNG timestamps (find newest PNG in directory)
        pngs = list(viz_dir.glob("*.png"))
        latest_png_mtime = None
        for png in pngs:
            mtime = get_file_mtime(png)
            if mtime and (latest_png_mtime is None or mtime > latest_png_mtime):
                latest_png_mtime = mtime

        # Check data source timestamps
        data_mtime = get_latest_data_mtime(config.get("data_sources", []))

        # Determine status
        if pdf_mtime is None:
            sync_status = "no_pdf"
        elif latest_png_mtime and latest_png_mtime > pdf_mtime:
            sync_status = "pdf_stale"
        elif data_mtime and data_mtime > pdf_mtime:
            sync_status = "data_updated"
        else:
            sync_status = "current"

        # Check WHITE-PAPER package status
        package_status = {}
        for version in ["v3", "v4", "v5"]:
            pkg_path = PACKAGES / version / "visualization_pdfs" / config["pdf_name"]
            pkg_mtime = get_file_mtime(pkg_path)
            if pkg_mtime is None:
                package_status[version] = "missing"
            elif pdf_mtime and pdf_mtime > pkg_mtime:
                package_status[version] = "outdated"
            else:
                package_status[version] = "current"

        status[dir_name] = {
            "exists": True,
            "status": sync_status,
            "pdf_mtime": pdf_mtime,
            "png_mtime": latest_png_mtime,
            "data_mtime": data_mtime,
            "packages": package_status,
            "config": config,
        }

    return status


def print_status(status: Dict[str, dict], verbose: bool = False):
    """Print a human-readable status report."""
    print("\n" + "=" * 70)
    print("VISUALIZATION PDF SYNC STATUS")
    print("=" * 70)

    needs_attention = []

    for dir_name, info in sorted(status.items()):
        if not info.get("exists"):
            print(f"\n❌ {dir_name}: Directory not found")
            continue

        status_icon = {
            "current": "✅",
            "pdf_stale": "⚠️",
            "data_updated": "🔄",
            "no_pdf": "❌",
        }.get(info["status"], "❓")

        print(f"\n{status_icon} {dir_name}")
        print(f"   Status: {info['status']}")

        if verbose:
            if info["pdf_mtime"]:
                print(f"   PDF:  {info['pdf_mtime'].strftime('%Y-%m-%d %H:%M')}")
            if info["png_mtime"]:
                print(f"   PNGs: {info['png_mtime'].strftime('%Y-%m-%d %H:%M')}")
            if info["data_mtime"]:
                print(f"   Data: {info['data_mtime'].strftime('%Y-%m-%d %H:%M')}")

        # Package status
        pkg_summary = []
        for ver, pkg_status in info.get("packages", {}).items():
            if pkg_status == "current":
                pkg_summary.append(f"{ver}:✅")
            elif pkg_status == "outdated":
                pkg_summary.append(f"{ver}:⚠️")
                needs_attention.append((dir_name, ver))
            else:
                pkg_summary.append(f"{ver}:❌")

        if pkg_summary:
            print(f"   Packages: {' '.join(pkg_summary)}")

        if info["config"].get("_discovered"):
            print("   (auto-discovered - may need manual verification)")

    print("\n" + "-" * 70)

    if needs_attention:
        print("\n⚠️  ITEMS NEEDING ATTENTION:")
        for dir_name, ver in needs_attention:
            print(f"   - {dir_name} → {ver}/visualization_pdfs/")
    else:
        print("\n✅ All visualizations appear synchronized.")

    print()


# =============================================================================
# PNG SYNC - Copy identified PNGs from visual_index.md to figures/
# =============================================================================

import re

def parse_visual_index() -> Dict[str, List[dict]]:
    """
    Parse visual_index.md to extract required PNGs by publication path.

    Returns dict like:
    {
        "workshop": [{"name": "oobleck_thermometer.png", "source": "15_Oobleck_Effect/", "claim": "E"}, ...],
        "arxiv": [...],
    }
    """
    if not VISUAL_INDEX.exists():
        print(f"[WARN] visual_index.md not found at {VISUAL_INDEX}")
        return {}

    with open(VISUAL_INDEX, 'r', encoding='utf-8') as f:
        content = f.read()

    visuals = {"workshop": [], "arxiv": [], "appendix": []}
    current_section = None

    # Pattern to match table rows with visual info: | # | `name.png` | `source/` | desc | claim |
    table_pattern = re.compile(r'\|\s*\d+\s*\|\s*`([^`]+\.png)`\s*\|\s*`([^`]+)`\s*\|[^|]*\|[^|]*\|')
    # Simpler pattern for appendix tables: | A# | `name.png` | `source/` | desc |
    appendix_pattern = re.compile(r'\|\s*A\d+\s*\|\s*`([^`]+\.png)`\s*\|\s*`([^`]+)`\s*\|')

    for line in content.split('\n'):
        # Track which section we're in
        if '## Section 1: Workshop Figures' in line:
            current_section = 'workshop'
        elif '## Section 2: arXiv Figures' in line:
            current_section = 'arxiv'
        elif '### Appendix' in line or 'Supplementary' in line:
            current_section = 'appendix'
        elif '## Section 3:' in line or '## Section 4:' in line:
            current_section = None  # These sections are reference only

        if current_section:
            # Try main table pattern
            match = table_pattern.search(line)
            if match:
                visuals[current_section].append({
                    "name": match.group(1),
                    "source": match.group(2).rstrip('/'),
                })
            else:
                # Try appendix pattern
                match = appendix_pattern.search(line)
                if match:
                    visuals['appendix'].append({
                        "name": match.group(1),
                        "source": match.group(2).rstrip('/'),
                    })

    return visuals


def parse_reviewer_requests() -> List[dict]:
    """
    Parse visual requests from CURRENT_VERSION.json.

    Requests are stored in the "visual_requests" section:
    {
      "visual_requests": {
        "requests": [
          {"name": "new_visual.png", "source": "15_Oobleck_Effect", "requested_by": "Grok-4.1", "status": "pending"}
        ]
      }
    }

    Returns list of requests with status pending or approved.
    """
    config = load_version_config()
    requests_data = config.get("visual_requests", {}).get("requests", [])

    # Filter to pending/approved only
    return [r for r in requests_data if r.get("status") in ("pending", "approved")]


def add_visual_request(name: str, source: str, requested_by: str) -> bool:
    """
    Add a new visual request to CURRENT_VERSION.json.
    Returns True if added, False if already exists.
    """
    config = load_version_config()

    if "visual_requests" not in config:
        config["visual_requests"] = {"requests": []}

    requests = config["visual_requests"]["requests"]

    # Check if already exists
    for r in requests:
        if r.get("name") == name and r.get("source") == source:
            print(f"   Request already exists: {name}")
            return False

    # Add new request
    requests.append({
        "name": name,
        "source": source,
        "requested_by": requested_by,
        "status": "pending",
        "date": datetime.now().strftime("%Y-%m-%d")
    })

    # Save
    with open(VERSION_FILE, 'w', encoding='utf-8') as f:
        json.dump(config, f, indent=2)

    print(f"   Added request: {name} from {source}")
    return True


def approve_visual_request(name: str) -> bool:
    """Mark a visual request as approved."""
    config = load_version_config()
    requests = config.get("visual_requests", {}).get("requests", [])

    for r in requests:
        if r.get("name") == name and r.get("status") == "pending":
            r["status"] = "approved"
            r["approved_date"] = datetime.now().strftime("%Y-%m-%d")

            with open(VERSION_FILE, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2)

            print(f"   Approved: {name}")
            return True

    print(f"   Not found or not pending: {name}")
    return False


def update_visual_index_with_approved() -> int:
    """
    Add approved visual requests to visual_index.md.
    Returns count of visuals added.
    """
    requests = parse_reviewer_requests()
    approved = [r for r in requests if r.get("status") == "approved"]

    if not approved:
        print("No approved requests to add to visual_index.md")
        return 0

    if not VISUAL_INDEX.exists():
        print(f"[WARN] visual_index.md not found")
        return 0

    with open(VISUAL_INDEX, 'r', encoding='utf-8') as f:
        content = f.read()

    added = 0
    additions = []

    for req in approved:
        # Check if already in visual_index
        if f"`{req['name']}`" in content:
            continue

        additions.append(f"| R{added+1} | `{req['name']}` | `{req['source']}/` | Reviewer requested | - |")
        added += 1

    if additions:
        # Add to end of Section 2 (arXiv) as reviewer-requested
        marker = "## Section 3:"
        if marker in content:
            insert_section = f"""
### Reviewer Requested (auto-added)

| # | Visual | Source Path | Shows | Claim |
|---|--------|-------------|-------|-------|
{chr(10).join(additions)}

"""
            content = content.replace(marker, insert_section + marker)

            with open(VISUAL_INDEX, 'w', encoding='utf-8') as f:
                f.write(content)

            print(f"Added {added} visuals to visual_index.md")

    return added


def resolve_png_source(source_dir: str, png_name: str) -> Optional[Path]:
    """Find the actual path to a PNG file given source directory hint."""
    # First try direct path in VIZ_PICS
    direct_path = VIZ_PICS / source_dir / png_name
    if direct_path.exists():
        return direct_path

    # Try subdirectories (e.g., phase3b_crossmodel/)
    source_path = VIZ_PICS / source_dir
    if source_path.exists():
        for subdir in source_path.iterdir():
            if subdir.is_dir():
                candidate = subdir / png_name
                if candidate.exists():
                    return candidate

    # Recursive search in source directory
    if source_path.exists():
        matches = list(source_path.rglob(png_name))
        if matches:
            return matches[0]

    return None


def sync_pngs_to_figures(dry_run: bool = False, include_requests: bool = False) -> Dict[str, int]:
    """
    Sync identified PNGs from visual_index.md to WHITE-PAPER/figures/.

    Returns dict with counts: {"synced": N, "skipped": N, "missing": N}
    """
    print("\n" + "=" * 70)
    print("PNG SYNC: visual_index.md → figures/")
    print("=" * 70)

    visuals = parse_visual_index()
    all_pngs = []

    # Collect all unique PNGs
    seen = set()
    for section, items in visuals.items():
        for item in items:
            key = f"{item['source']}/{item['name']}"
            if key not in seen:
                seen.add(key)
                all_pngs.append(item)

    # Add approved reviewer requests
    if include_requests:
        requests = parse_reviewer_requests()
        for req in requests:
            if req['status'] == 'approved':
                key = f"{req['source']}/{req['name']}"
                if key not in seen:
                    seen.add(key)
                    all_pngs.append(req)
                    print(f"   + Including approved request: {req['name']}")

    print(f"\nFound {len(all_pngs)} unique PNGs to sync\n")

    stats = {"synced": 0, "skipped": 0, "missing": 0}

    # Organize target directories by source
    # e.g., 15_Oobleck_Effect/ → figures/oobleck/
    # or just flatten to figures/publication/
    target_dir = FIGURES_DIR / "publication"
    target_dir.mkdir(parents=True, exist_ok=True)

    for item in all_pngs:
        source_path = resolve_png_source(item['source'], item['name'])

        if not source_path:
            print(f"   ❌ {item['name']} - not found in {item['source']}")
            stats["missing"] += 1
            continue

        target_path = target_dir / item['name']

        # Check if already synced and up-to-date
        if target_path.exists():
            src_mtime = source_path.stat().st_mtime
            tgt_mtime = target_path.stat().st_mtime
            if tgt_mtime >= src_mtime:
                print(f"   ✓ {item['name']} - up to date")
                stats["skipped"] += 1
                continue

        # Sync needed
        if dry_run:
            print(f"   → {item['name']} - would sync from {source_path.parent.name}/")
        else:
            shutil.copy2(source_path, target_path)
            print(f"   ✓ {item['name']} - synced from {source_path.parent.name}/")
        stats["synced"] += 1

    print(f"\n{'DRY RUN - ' if dry_run else ''}Summary: {stats['synced']} synced, {stats['skipped']} up-to-date, {stats['missing']} missing")

    return stats


def check_reviewer_requests():
    """Show pending reviewer visual requests from CURRENT_VERSION.json."""
    requests = parse_reviewer_requests()
    pending = [r for r in requests if r.get('status') == 'pending']
    approved = [r for r in requests if r.get('status') == 'approved']

    if not requests:
        print("\n📋 No reviewer requests in CURRENT_VERSION.json.")
        print(f"   Run --process-feedback to import from feedback directories.")
        return

    print("\n" + "=" * 70)
    print("REVIEWER VISUAL REQUESTS (from CURRENT_VERSION.json)")
    print("=" * 70)

    if pending:
        print(f"\n⏳ PENDING ({len(pending)}):")
        for r in pending:
            print(f"   - {r.get('name')} from {r.get('source')} (by {r.get('requested_by', 'unknown')})")

    if approved:
        print(f"\n✅ APPROVED ({len(approved)}):")
        for r in approved:
            print(f"   - {r.get('name')} from {r.get('source')}")

    print()


def process_feedback() -> Dict[str, int]:
    """
    Process reviewer feedback from feedback directories into CURRENT_VERSION.json.

    Reads: packages/v4/feedback/{reviewer}/visual_requests.json
    Updates: packages/CURRENT_VERSION.json

    Returns dict with counts: {"imported": N, "skipped": N, "errors": N}
    """
    print("\n" + "=" * 70)
    print("PROCESSING REVIEWER FEEDBACK")
    print("=" * 70)

    stats = {"imported": 0, "skipped": 0, "errors": 0}

    if not FEEDBACK_DIR.exists():
        print(f"\n[WARN] Feedback directory not found: {FEEDBACK_DIR}")
        return stats

    # Load current version config
    config = load_version_config()
    if "visual_requests" not in config:
        config["visual_requests"] = {"requests": []}

    existing_requests = config["visual_requests"]["requests"]
    existing_keys = {(r.get("name"), r.get("source"), r.get("pipeline")) for r in existing_requests}

    # Scan each reviewer directory
    for reviewer_dir in FEEDBACK_DIR.iterdir():
        if not reviewer_dir.is_dir() or reviewer_dir.name.startswith('.'):
            continue

        reviewer_name = reviewer_dir.name
        requests_file = reviewer_dir / "visual_requests.json"

        if not requests_file.exists():
            continue

        print(f"\n📁 {reviewer_name}/")

        try:
            with open(requests_file, 'r', encoding='utf-8') as f:
                feedback_data = json.load(f)

            requests = feedback_data.get("requests", [])
            print(f"   Found {len(requests)} requests")

            for req in requests:
                req_type = req.get("type", "add")
                visual = req.get("visual")
                source = req.get("source")
                pipeline = req.get("pipeline")
                status = req.get("status", "pending")

                # Skip if already processed
                key = (visual, source, pipeline)
                if key in existing_keys:
                    print(f"   ⏭️  {visual} - already in CURRENT_VERSION.json")
                    stats["skipped"] += 1
                    continue

                # Add to CURRENT_VERSION.json
                new_request = {
                    "name": visual,
                    "source": source,
                    "pipeline": pipeline,
                    "type": req_type,
                    "placement": req.get("placement", "main"),
                    "figure_num": req.get("figure_num"),
                    "reason": req.get("reason", ""),
                    "requested_by": reviewer_name,
                    "status": status,
                    "date": req.get("date", datetime.now().strftime("%Y-%m-%d")),
                    "imported_from": f"feedback/{reviewer_name}/visual_requests.json"
                }

                existing_requests.append(new_request)
                existing_keys.add(key)
                print(f"   ✓ {visual} → {pipeline}/{req.get('placement', 'main')}")
                stats["imported"] += 1

        except json.JSONDecodeError as e:
            print(f"   [ERROR] Invalid JSON: {e}")
            stats["errors"] += 1
        except Exception as e:
            print(f"   [ERROR] {e}")
            stats["errors"] += 1

    # Save updated config
    if stats["imported"] > 0:
        with open(VERSION_FILE, 'w', encoding='utf-8') as f:
            json.dump(config, f, indent=2)
        print(f"\n✅ Updated CURRENT_VERSION.json")

    print(f"\nSummary: {stats['imported']} imported, {stats['skipped']} already present, {stats['errors']} errors")

    return stats


# =============================================================================
# SYNC OPERATIONS
# =============================================================================

def regenerate_pngs(dir_name: str, config: dict) -> bool:
    """Regenerate PNG visualizations by running the generator script."""
    viz_dir = VIZ_PICS / dir_name
    generator = config.get("png_generator")

    if not generator:
        print(f"   [WARN] No PNG generator known for {dir_name}")
        return False

    script_path = viz_dir / generator
    if not script_path.exists():
        print(f"   [WARN] Generator not found: {script_path}")
        return False

    print(f"   Running: python {generator}")
    try:
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=str(viz_dir),
            capture_output=True,
            text=True,
            timeout=300,  # 5 minute timeout
        )
        if result.returncode == 0:
            print(f"   [OK] PNGs regenerated")
            return True
        else:
            print(f"   [ERROR] Generator failed:")
            print(result.stderr[:500] if result.stderr else result.stdout[:500])
            return False
    except subprocess.TimeoutExpired:
        print(f"   [ERROR] Generator timed out")
        return False
    except Exception as e:
        print(f"   [ERROR] {e}")
        return False


def regenerate_pdf(dir_name: str, config: dict) -> bool:
    """Regenerate PDF summary by running the PDF generator script."""
    viz_dir = VIZ_PICS / dir_name
    generator = config.get("pdf_generator")

    if not generator:
        print(f"   [WARN] No PDF generator known for {dir_name}")
        return False

    script_path = viz_dir / generator
    if not script_path.exists():
        print(f"   [WARN] PDF generator not found: {script_path}")
        return False

    print(f"   Running: python {generator}")
    try:
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=str(viz_dir),
            capture_output=True,
            text=True,
            timeout=120,
        )
        if result.returncode == 0:
            print(f"   [OK] PDF regenerated")
            return True
        else:
            print(f"   [ERROR] PDF generator failed:")
            print(result.stderr[:500] if result.stderr else result.stdout[:500])
            return False
    except Exception as e:
        print(f"   [ERROR] {e}")
        return False


def sync_to_package(dir_name: str, config: dict, target_version: str = "v4") -> bool:
    """Copy PDF to WHITE-PAPER package directory."""
    viz_dir = VIZ_PICS / dir_name
    pdf_path = viz_dir / config["pdf_name"]

    if not pdf_path.exists():
        print(f"   [WARN] PDF not found: {pdf_path}")
        return False

    target_dir = PACKAGES / target_version / "visualization_pdfs"
    target_dir.mkdir(parents=True, exist_ok=True)
    target_path = target_dir / config["pdf_name"]

    try:
        shutil.copy2(pdf_path, target_path)
        print(f"   [OK] Copied to {target_version}/visualization_pdfs/")
        return True
    except Exception as e:
        print(f"   [ERROR] Copy failed: {e}")
        return False


# =============================================================================
# INTERACTIVE MODE - Ask questions when uncertain
# =============================================================================

def interactive_sync():
    """
    Interactive sync mode - walks through each visualization and asks
    what to do when there's uncertainty.
    """
    print("\n" + "=" * 70)
    print("INTERACTIVE VISUALIZATION SYNC")
    print("=" * 70)
    print("\nI'll check each visualization and ask you what to do.\n")

    status = check_sync_status()

    for dir_name, info in sorted(status.items()):
        if not info.get("exists"):
            continue

        print(f"\n{'='*50}")
        print(f"📁 {dir_name}")
        print(f"{'='*50}")

        config = info.get("config", {})

        # Show current status
        print(f"\nStatus: {info['status']}")
        if info["pdf_mtime"]:
            print(f"PDF last modified: {info['pdf_mtime'].strftime('%Y-%m-%d %H:%M')}")
        if info["png_mtime"]:
            print(f"PNGs last modified: {info['png_mtime'].strftime('%Y-%m-%d %H:%M')}")
        if info["data_mtime"]:
            print(f"Data last modified: {info['data_mtime'].strftime('%Y-%m-%d %H:%M')}")

        # Check if discovered (not in known list)
        if config.get("_discovered"):
            print("\n⚠️  This was auto-discovered. I'm not sure about:")
            print("   - What data sources it uses")
            print("   - Whether the generators are correct")
            response = input("\nShould I include this in the sync? (y/n/skip): ").strip().lower()
            if response != 'y':
                print("Skipping...")
                continue

        # Determine what actions might be needed
        actions_needed = []

        if info["status"] == "data_updated":
            print("\n🔄 The underlying data has been updated since the PNGs were generated.")
            response = input("Regenerate PNGs from fresh data? (y/n): ").strip().lower()
            if response == 'y':
                actions_needed.append("regenerate_pngs")
                actions_needed.append("regenerate_pdf")

        if info["status"] == "pdf_stale" or "regenerate_pngs" in actions_needed:
            if "regenerate_pdf" not in actions_needed:
                print("\n⚠️  PNGs are newer than PDF.")
                response = input("Regenerate PDF to include latest PNGs? (y/n): ").strip().lower()
                if response == 'y':
                    actions_needed.append("regenerate_pdf")

        # Check package sync
        outdated_packages = [v for v, s in info.get("packages", {}).items() if s == "outdated"]
        missing_packages = [v for v, s in info.get("packages", {}).items() if s == "missing"]

        if outdated_packages:
            print(f"\n📦 These packages have older versions: {', '.join(outdated_packages)}")
            response = input(f"Sync to packages? (y/n/specify version): ").strip().lower()
            if response == 'y':
                actions_needed.append(("sync", outdated_packages))
            elif response and response not in ['n', 'no']:
                actions_needed.append(("sync", [response]))

        if missing_packages and not outdated_packages:
            print(f"\n📦 PDF missing from: {', '.join(missing_packages)}")
            response = input(f"Copy to these packages? (y/n): ").strip().lower()
            if response == 'y':
                actions_needed.append(("sync", missing_packages))

        # Execute actions
        if actions_needed:
            print(f"\n▶️  Executing actions...")
            for action in actions_needed:
                if action == "regenerate_pngs":
                    regenerate_pngs(dir_name, config)
                elif action == "regenerate_pdf":
                    regenerate_pdf(dir_name, config)
                elif isinstance(action, tuple) and action[0] == "sync":
                    for version in action[1]:
                        sync_to_package(dir_name, config, version)
        else:
            print("\n✅ No actions needed for this visualization.")

    print("\n" + "=" * 70)
    print("INTERACTIVE SYNC COMPLETE")
    print("=" * 70)


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Sync visualization PDFs and PNGs to WHITE-PAPER packages",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python 0_sync_viz.py --check          # See what needs syncing
  python 0_sync_viz.py --status         # Detailed status report
  python 0_sync_viz.py --interactive    # Walk through interactively
  python 0_sync_viz.py --sync           # Auto-sync all outdated PDFs
  python 0_sync_viz.py --sync run018    # Sync specific viz
  python 0_sync_viz.py --regenerate --sync  # Regenerate then sync

PNG Sync (from visual_index.md to figures/publication/):
  python 0_sync_viz.py --sync-pngs              # Sync identified PNGs
  python 0_sync_viz.py --sync-pngs --dry-run    # Preview what would sync
  python 0_sync_viz.py --sync-pngs --include-requests  # Include approved reviewer requests

Reviewer Feedback Loop:
  python 0_sync_viz.py --requests               # Show pending visual requests
  python 0_sync_viz.py --request "name.png" "source_dir" "Reviewer Name"  # Add request
  python 0_sync_viz.py --approve "name.png"     # Approve a request
  python 0_sync_viz.py --update-index           # Add approved to visual_index.md
        """
    )

    parser.add_argument("--check", action="store_true",
                       help="Check sync status (quick overview)")
    parser.add_argument("--status", action="store_true",
                       help="Show detailed status report")
    parser.add_argument("--interactive", "-i", action="store_true",
                       help="Interactive mode - asks questions")
    parser.add_argument("--sync", nargs="*", metavar="VIZ",
                       help="Sync PDFs to packages (optionally specify which)")
    parser.add_argument("--regenerate", action="store_true",
                       help="Regenerate PNGs and PDFs before syncing")
    parser.add_argument("--target", default=None,
                       help="Target package version (default: read from CURRENT_VERSION.json)")
    parser.add_argument("--version-info", action="store_true",
                       help="Show current version info and triggers")
    parser.add_argument("--bump-check", metavar="REASON",
                       help="Check if a reason warrants a version bump")
    parser.add_argument("--dry-run", action="store_true",
                       help="Show what would be done without doing it")

    # PNG sync arguments
    parser.add_argument("--sync-pngs", action="store_true",
                       help="Sync PNGs from visual_index.md to figures/publication/")
    parser.add_argument("--include-requests", action="store_true",
                       help="Include approved reviewer requests when syncing PNGs")

    # Reviewer request arguments
    parser.add_argument("--requests", action="store_true",
                       help="Show pending visual requests from reviewers")
    parser.add_argument("--request", nargs=3, metavar=("PNG", "SOURCE", "REVIEWER"),
                       help="Add a visual request: --request name.png source_dir reviewer")
    parser.add_argument("--approve", metavar="PNG",
                       help="Approve a pending visual request")
    parser.add_argument("--update-index", action="store_true",
                       help="Add approved requests to visual_index.md")
    parser.add_argument("--process-feedback", action="store_true",
                       help="Import feedback from packages/v4/feedback/ into CURRENT_VERSION.json")

    args = parser.parse_args()

    # Default to --check if no args
    if len(sys.argv) == 1:
        args.check = True

    # Handle version info
    if args.version_info:
        print_version_info()
        return

    # Handle bump check
    if args.bump_check:
        should_bump, explanation = should_bump_version(args.bump_check)
        print(f"\nReason: {args.bump_check}")
        print(f"Should bump version: {'YES' if should_bump else 'NO'}")
        print(f"Explanation: {explanation}")
        if should_bump:
            current = get_current_version()
            next_num = int(current[1:]) + 1
            print(f"Suggested: {current} → v{next_num}")
        return

    # Determine target version
    if args.target is None:
        args.target = get_current_version()
        print(f"(Using version from CURRENT_VERSION.json: {args.target})")

    if args.interactive:
        interactive_sync()
        return

    if args.check or args.status:
        status = check_sync_status()
        print_status(status, verbose=args.status)
        return

    # Handle reviewer request operations
    if args.requests:
        check_reviewer_requests()
        return

    if args.request:
        png_name, source, reviewer = args.request
        add_visual_request(png_name, source, reviewer)
        return

    if args.approve:
        approve_visual_request(args.approve)
        return

    if args.update_index:
        count = update_visual_index_with_approved()
        if count:
            print(f"\n✅ Added {count} visuals to visual_index.md")
        return

    if args.process_feedback:
        process_feedback()
        return

    # Handle PNG sync
    if args.sync_pngs:
        sync_pngs_to_figures(dry_run=args.dry_run, include_requests=args.include_requests)
        return

    if args.sync is not None:
        status = check_sync_status()

        # Determine which visualizations to sync
        if args.sync:  # Specific ones specified
            viz_list = args.sync
        else:  # All that need it
            viz_list = [name for name, info in status.items()
                       if info.get("status") in ["pdf_stale", "data_updated"]
                       or any(s == "outdated" for s in info.get("packages", {}).values())]

        if not viz_list:
            print("✅ Nothing needs syncing!")
            return

        print(f"\nSyncing: {', '.join(viz_list)}")
        if args.dry_run:
            print("(dry run - no changes will be made)")
            return

        for dir_name in viz_list:
            if dir_name not in status:
                print(f"\n❌ Unknown visualization: {dir_name}")
                continue

            info = status[dir_name]
            config = info.get("config", {})

            print(f"\n📁 {dir_name}")

            if args.regenerate:
                regenerate_pngs(dir_name, config)
                regenerate_pdf(dir_name, config)

            sync_to_package(dir_name, config, args.target)

        print("\n✅ Sync complete!")


if __name__ == "__main__":
    main()
