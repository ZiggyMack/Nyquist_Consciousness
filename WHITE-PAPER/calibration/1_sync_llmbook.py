#!/usr/bin/env python3
"""
1_sync_llmbook.py - LLM_BOOK → REVIEWER PACKAGES SYNC
=====================================================
Synchronizes NotebookLM synthesis content to reviewer packages for feedback.

NOTE: This syncs to reviewers/packages/, NOT submissions/. The submissions/
directory contains only curated *_FINAL.md papers. NotebookLM outputs go to
reviewer packages so AI reviewers can evaluate how to incorporate them.

USAGE:
------
py 1_sync_llmbook.py                     # Report mode (default)
py 1_sync_llmbook.py --sync              # Actually sync all files
py 1_sync_llmbook.py --sync --dry-run    # Preview changes without applying
py 1_sync_llmbook.py --category popular_science  # Only sync specific category
py 1_sync_llmbook.py --sync --include-visuals   # Also sync 3_VISUALS/*.png

CATEGORIES:
-----------
- academic: 2_PUBLICATIONS/academic/ → reviewers/packages/{version}/llmbook/academic/
- popular_science: 2_PUBLICATIONS/popular_science/ → reviewers/packages/{version}/llmbook/popular_science/
- education: 2_PUBLICATIONS/education/ → reviewers/packages/{version}/llmbook/education/
- policy: 2_PUBLICATIONS/policy/ → reviewers/packages/{version}/llmbook/policy/
- funding: 2_PUBLICATIONS/funding/ → reviewers/packages/{version}/llmbook/funding/
- media: 2_PUBLICATIONS/media/ → reviewers/packages/{version}/llmbook/media/
- validation: 1_VALIDATION/REVIEW_NOTES_*.md → reviewers/packages/{version}/llmbook/validation/

ANALYSIS SUBDIRECTORIES (--full mode outputs):
----------------------------------------------
- deep_dives: 1_VALIDATION/1_DEEP_DIVES/*.md → reviewers/packages/{version}/llmbook/analysis/deep_dives/
- future: 1_VALIDATION/2_FUTURE/*.md → reviewers/packages/{version}/llmbook/analysis/future/
- experiments: 1_VALIDATION/3_EXPERIMENTS/*.md → reviewers/packages/{version}/llmbook/analysis/experiments/

VERSION:
--------
Target version is read from reviewers/packages/CURRENT_VERSION.json (source of truth)

Author: WHITE-PAPER Calibration
Version: 2.3 (2025-12-29) - Add analysis subdirectory sync for --full mode outputs
"""

import argparse
import hashlib
import json
import shutil
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional

# === PATH CONSTANTS ===
REPO_ROOT = Path(__file__).parent.parent.parent  # d:\Documents\Nyquist_Consciousness
WHITE_PAPER_DIR = Path(__file__).parent.parent   # WHITE-PAPER/
LLM_BOOK_DIR = REPO_ROOT / "REPO-SYNC" / "LLM_BOOK"
VALIDATION_DIR = LLM_BOOK_DIR / "1_VALIDATION"  # Contains REVIEW_NOTES_*.md
PUBLICATIONS_DIR = LLM_BOOK_DIR / "2_PUBLICATIONS"
VISUALS_DIR = LLM_BOOK_DIR / "3_VISUALS"
VERSION_FILE = WHITE_PAPER_DIR / "reviewers" / "packages" / "CURRENT_VERSION.json"
FIGURES_GENERATED_DIR = WHITE_PAPER_DIR / "figures" / "generated" / "llmbook"
MANIFEST_PATH = WHITE_PAPER_DIR / "reviewers" / "LLMBOOK_SYNC_MANIFEST.json"
SYNC_STATUS_PATH = WHITE_PAPER_DIR / "reviewers" / "SYNC_STATUS.md"

# Analysis subdirectories (--full mode outputs from ingest.py)
DEEP_DIVES_DIR = VALIDATION_DIR / "1_DEEP_DIVES"
FUTURE_DIR = VALIDATION_DIR / "2_FUTURE"
EXPERIMENTS_DIR = VALIDATION_DIR / "3_EXPERIMENTS"


def get_current_version() -> str:
    """Read current version from CURRENT_VERSION.json (source of truth)."""
    if VERSION_FILE.exists():
        with open(VERSION_FILE, "r", encoding="utf-8") as f:
            return json.load(f)["current_version"]
    return "v4"  # Fallback if file doesn't exist


def get_llmbook_target_dir() -> Path:
    """Get target directory based on current version from CURRENT_VERSION.json."""
    return WHITE_PAPER_DIR / "reviewers" / "packages" / get_current_version() / "llmbook"

# === CATEGORY MAPPINGS ===
# Source (LLM_BOOK/2_PUBLICATIONS/) → Target (WHITE-PAPER/reviewers/packages/{version}/llmbook/)
# NOTE: NotebookLM outputs go to reviewer packages for feedback, NOT submissions/
# Target paths are computed dynamically via get_category_mappings() to use current version


def get_category_mappings() -> Dict:
    """Build category mappings with current version from CURRENT_VERSION.json."""
    target_dir = get_llmbook_target_dir()
    return {
        "academic": {
            "source": PUBLICATIONS_DIR / "academic",
            "target": target_dir / "academic",
            "description": "Academic papers (NotebookLM synthesis)",
            "extensions": [".md", ".pdf"]
        },
        "popular_science": {
            "source": PUBLICATIONS_DIR / "popular_science",
            "target": target_dir / "popular_science",
            "description": "Popular science articles (Atlantic/Wired style)",
            "extensions": [".md"]
        },
        "education": {
            "source": PUBLICATIONS_DIR / "education",
            "target": target_dir / "education",
            "description": "Educational materials (OER/Coursera)",
            "extensions": [".md"]
        },
        "policy": {
            "source": PUBLICATIONS_DIR / "policy",
            "target": target_dir / "policy",
            "description": "Policy briefings (Think tanks)",
            "extensions": [".md"]
        },
        "funding": {
            "source": PUBLICATIONS_DIR / "funding",
            "target": target_dir / "funding",
            "description": "Funding proposals (NSF/DARPA)",
            "extensions": [".md"]
        },
        "media": {
            "source": PUBLICATIONS_DIR / "media",
            "target": target_dir / "media",
            "description": "Media content (Press/TED)",
            "extensions": [".md"]
        }
    }

# Visual sync mapping
VISUAL_MAPPING = {
    "source": VISUALS_DIR,
    "target": FIGURES_GENERATED_DIR,
    "extensions": [".png", ".jpg", ".jpeg", ".gif"],
    "description": "NotebookLM generated visuals"
}


def get_validation_mapping() -> Dict:
    """Build validation mapping for REVIEW_NOTES_*.md files."""
    target_dir = get_llmbook_target_dir()
    return {
        "source": VALIDATION_DIR,
        "target": target_dir / "validation",
        "pattern": "REVIEW_NOTES_*.md",
        "description": "Reviewer notes (accumulative model)"
    }


def get_analysis_mappings() -> Dict:
    """Build analysis mappings for --full mode subdirectories."""
    target_dir = get_llmbook_target_dir()
    return {
        "deep_dives": {
            "source": DEEP_DIVES_DIR,
            "target": target_dir / "analysis" / "deep_dives",
            "extensions": [".md"],
            "description": "Deep dive distillations (--full mode)"
        },
        "future": {
            "source": FUTURE_DIR,
            "target": target_dir / "analysis" / "future",
            "extensions": [".md"],
            "description": "Future research directions (--full mode)"
        },
        "experiments": {
            "source": EXPERIMENTS_DIR,
            "target": target_dir / "analysis" / "experiments",
            "extensions": [".md"],
            "description": "Experiment ideas (--full mode)"
        }
    }


def get_file_hash(path: Path) -> str:
    """Calculate MD5 hash of file for change detection."""
    if not path.exists() or path.is_dir():
        return ""
    hasher = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def load_manifest() -> Dict:
    """Load sync manifest from LLMBOOK_SYNC_MANIFEST.json."""
    if MANIFEST_PATH.exists():
        with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    return create_empty_manifest()


def save_manifest(manifest: Dict) -> None:
    """Save updated manifest to LLMBOOK_SYNC_MANIFEST.json."""
    # Ensure directory exists
    MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(MANIFEST_PATH, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)


def create_empty_manifest() -> Dict:
    """Create initial manifest structure."""
    return {
        "manifest_version": "1.0",
        "last_updated": datetime.now().isoformat(),
        "repo_root": str(REPO_ROOT),
        "categories": {},
        "visuals": {"files": []},
        "sync_history": [],
        "summary": {
            "total_files": 0,
            "total_synced": 0,
            "total_pending": 0,
            "total_size_mb": 0.0
        }
    }


def discover_source_files(category: Optional[str] = None) -> Dict[str, List[Path]]:
    """
    Discover all source files in LLM_BOOK/2_PUBLICATIONS/.

    Returns dict like:
    {
        "academic": [Path(...), Path(...)],
        "popular_science": [Path(...)],
        ...
    }
    """
    sources = {}

    category_mappings = get_category_mappings()
    categories_to_scan = [category] if category else category_mappings.keys()

    for cat_name in categories_to_scan:
        if cat_name not in category_mappings:
            continue
        mapping = category_mappings[cat_name]
        source_dir = mapping["source"]
        extensions = mapping["extensions"]

        sources[cat_name] = []
        if source_dir.exists():
            for ext in extensions:
                sources[cat_name].extend(source_dir.glob(f"*{ext}"))

    return sources


def discover_visual_files() -> List[Path]:
    """Discover all visual files in LLM_BOOK/3_VISUALS/."""
    visuals = []
    source_dir = VISUAL_MAPPING["source"]
    extensions = VISUAL_MAPPING["extensions"]

    if source_dir.exists():
        for ext in extensions:
            visuals.extend(source_dir.glob(f"*{ext}"))

    return visuals


def discover_validation_files() -> List[Path]:
    """Discover all REVIEW_NOTES_*.md files in LLM_BOOK/1_VALIDATION/."""
    mapping = get_validation_mapping()
    source_dir = mapping["source"]
    pattern = mapping["pattern"]

    if source_dir.exists():
        return sorted(source_dir.glob(pattern))

    return []


def discover_analysis_files(analysis_type: Optional[str] = None) -> Dict[str, List[Path]]:
    """
    Discover all files in analysis subdirectories (--full mode outputs).

    Args:
        analysis_type: Optional - only discover for specific type (deep_dives, future, experiments)

    Returns dict like:
    {
        "deep_dives": [Path(...), Path(...)],
        "future": [Path(...)],
        "experiments": [Path(...)]
    }
    """
    sources = {}
    analysis_mappings = get_analysis_mappings()
    types_to_scan = [analysis_type] if analysis_type else analysis_mappings.keys()

    for atype in types_to_scan:
        if atype not in analysis_mappings:
            continue
        mapping = analysis_mappings[atype]
        source_dir = mapping["source"]
        extensions = mapping["extensions"]

        sources[atype] = []
        if source_dir.exists():
            for ext in extensions:
                sources[atype].extend(sorted(source_dir.glob(f"*{ext}")))

    return sources


def file_needs_sync(source: Path, target: Path, manifest: Dict) -> Tuple[bool, str]:
    """
    Determine if a source file needs to be synced to target.

    Args:
        source: Source file path
        target: Target directory (or file path)
        manifest: Sync manifest for hash comparison

    Returns:
    (True, "new") - target doesn't exist
    (True, "modified") - source hash differs from manifest
    (False, "synced") - file is up to date
    """
    # Construct actual target file path with LLM_ prefix
    if target.is_dir():
        target_file = target / f"LLM_{source.name}"
    else:
        target_file = target.parent / f"LLM_{source.name}"

    if not target_file.exists():
        return (True, "new")

    current_hash = get_file_hash(source)

    # Check manifest for previous hash
    for cat_data in manifest.get("categories", {}).values():
        for file_entry in cat_data.get("files", []):
            if file_entry.get("source_path") == str(source.relative_to(REPO_ROOT)):
                if file_entry.get("source_hash") != current_hash:
                    return (True, "modified")
                return (False, "synced")

    # Check visuals
    for file_entry in manifest.get("visuals", {}).get("files", []):
        if file_entry.get("filename") == source.name:
            if file_entry.get("source_hash") != current_hash:
                return (True, "modified")
            return (False, "synced")

    # Not in manifest but target exists - check hash
    if get_file_hash(target_file) == current_hash:
        return (False, "synced")

    return (True, "modified")


def sync_file(source: Path, target: Path, dry_run: bool = True) -> Dict:
    """
    Copy source file to target location with LLM_ prefix.

    If dry_run=True, only report what would happen.
    Returns dict with operation details.
    """
    # Add LLM_ prefix to distinguish from hand-authored content
    target_name = f"LLM_{source.name}"
    target_path = target.parent / target_name if target.is_file() else target / target_name

    result = {
        "source": str(source),
        "target": str(target_path),
        "source_hash": get_file_hash(source),
        "size_bytes": source.stat().st_size if source.exists() else 0,
        "synced": False,
        "dry_run": dry_run
    }

    if not dry_run:
        # Ensure target directory exists
        target_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target_path)
        result["synced"] = True
        result["synced_at"] = datetime.now().isoformat()

    return result


def sync_category(category: str, dry_run: bool = True, manifest: Dict = None) -> List[Dict]:
    """
    Sync all files in a specific category.
    Returns list of sync operation results.
    """
    if manifest is None:
        manifest = load_manifest()

    results = []

    category_mappings = get_category_mappings()
    if category not in category_mappings:
        return [{"error": f"Unknown category: {category}"}]

    mapping = category_mappings[category]
    sources = discover_source_files(category)

    for source_file in sources.get(category, []):
        needs_sync, reason = file_needs_sync(source_file, mapping["target"], manifest)

        if needs_sync:
            result = sync_file(source_file, mapping["target"], dry_run)
            result["reason"] = reason
            result["category"] = category
            results.append(result)
        else:
            results.append({
                "source": str(source_file),
                "status": "already_synced",
                "category": category
            })

    return results


def sync_visuals(dry_run: bool = True, manifest: Dict = None) -> List[Dict]:
    """Sync visual files from 3_VISUALS/ to figures/generated/llmbook/."""
    if manifest is None:
        manifest = load_manifest()

    results = []
    target_dir = VISUAL_MAPPING["target"]

    for source_file in discover_visual_files():
        needs_sync, reason = file_needs_sync(source_file, target_dir, manifest)

        if needs_sync:
            result = sync_file(source_file, target_dir, dry_run)
            result["reason"] = reason
            result["category"] = "visuals"
            results.append(result)
        else:
            results.append({
                "source": str(source_file),
                "status": "already_synced",
                "category": "visuals"
            })

    return results


def sync_validation(dry_run: bool = True, manifest: Dict = None) -> List[Dict]:
    """Sync REVIEW_NOTES_*.md files from 1_VALIDATION/ to llmbook/validation/."""
    if manifest is None:
        manifest = load_manifest()

    results = []
    mapping = get_validation_mapping()
    target_dir = mapping["target"]

    for source_file in discover_validation_files():
        needs_sync, reason = file_needs_sync(source_file, target_dir, manifest)

        if needs_sync:
            result = sync_file(source_file, target_dir, dry_run)
            result["reason"] = reason
            result["category"] = "validation"
            results.append(result)
        else:
            results.append({
                "source": str(source_file),
                "status": "already_synced",
                "category": "validation"
            })

    return results


def sync_analysis(dry_run: bool = True, manifest: Dict = None) -> Dict[str, List[Dict]]:
    """
    Sync analysis files from --full mode subdirectories.

    Syncs:
    - 1_VALIDATION/1_DEEP_DIVES/*.md → llmbook/analysis/deep_dives/
    - 1_VALIDATION/2_FUTURE/*.md → llmbook/analysis/future/
    - 1_VALIDATION/3_EXPERIMENTS/*.md → llmbook/analysis/experiments/

    Returns dict with results per analysis type.
    """
    if manifest is None:
        manifest = load_manifest()

    results = {}
    analysis_mappings = get_analysis_mappings()
    analysis_files = discover_analysis_files()

    for atype, mapping in analysis_mappings.items():
        results[atype] = []
        target_dir = mapping["target"]

        for source_file in analysis_files.get(atype, []):
            needs_sync, reason = file_needs_sync(source_file, target_dir, manifest)

            if needs_sync:
                result = sync_file(source_file, target_dir, dry_run)
                result["reason"] = reason
                result["category"] = f"analysis_{atype}"
                results[atype].append(result)
            else:
                results[atype].append({
                    "source": str(source_file),
                    "status": "already_synced",
                    "category": f"analysis_{atype}"
                })

    return results


def sync_all(dry_run: bool = True, include_visuals: bool = False,
             include_validation: bool = True, include_analysis: bool = True,
             category: Optional[str] = None) -> Dict:
    """
    Sync all categories, validation notes, analysis subdirs, and optionally visuals.
    Returns comprehensive sync report.

    Args:
        dry_run: If True, only preview changes
        include_visuals: Also sync 3_VISUALS/ to figures/generated/llmbook/
        include_validation: Sync REVIEW_NOTES_*.md from 1_VALIDATION/ (default True)
        include_analysis: Sync analysis subdirs (deep_dives, future, experiments) (default True)
        category: If specified, only sync that publication category
    """
    manifest = load_manifest()
    results = {
        "timestamp": datetime.now().isoformat(),
        "dry_run": dry_run,
        "categories": {},
        "validation": [],
        "analysis": {},
        "visuals": [],
        "summary": {
            "total_processed": 0,
            "synced": 0,
            "already_synced": 0,
            "errors": 0
        }
    }

    category_mappings = get_category_mappings()
    categories_to_sync = [category] if category else category_mappings.keys()

    for cat_name in categories_to_sync:
        cat_results = sync_category(cat_name, dry_run, manifest)
        results["categories"][cat_name] = cat_results

        for r in cat_results:
            results["summary"]["total_processed"] += 1
            if r.get("synced") or (r.get("reason") and not dry_run):
                results["summary"]["synced"] += 1
            elif r.get("status") == "already_synced":
                results["summary"]["already_synced"] += 1
            elif r.get("error"):
                results["summary"]["errors"] += 1

    # Sync validation (REVIEW_NOTES_*.md) - enabled by default
    if include_validation:
        validation_results = sync_validation(dry_run, manifest)
        results["validation"] = validation_results

        for r in validation_results:
            results["summary"]["total_processed"] += 1
            if r.get("synced") or (r.get("reason") and not dry_run):
                results["summary"]["synced"] += 1
            elif r.get("status") == "already_synced":
                results["summary"]["already_synced"] += 1

    # Sync analysis subdirectories (--full mode outputs) - enabled by default
    if include_analysis:
        analysis_results = sync_analysis(dry_run, manifest)
        results["analysis"] = analysis_results

        for atype, atype_results in analysis_results.items():
            for r in atype_results:
                results["summary"]["total_processed"] += 1
                if r.get("synced") or (r.get("reason") and not dry_run):
                    results["summary"]["synced"] += 1
                elif r.get("status") == "already_synced":
                    results["summary"]["already_synced"] += 1

    if include_visuals:
        visual_results = sync_visuals(dry_run, manifest)
        results["visuals"] = visual_results

        for r in visual_results:
            results["summary"]["total_processed"] += 1
            if r.get("synced") or (r.get("reason") and not dry_run):
                results["summary"]["synced"] += 1
            elif r.get("status") == "already_synced":
                results["summary"]["already_synced"] += 1

    # Update manifest if not dry run
    if not dry_run:
        update_manifest(manifest, results)
        save_manifest(manifest)

    return results


def update_manifest(manifest: Dict, results: Dict) -> None:
    """Update manifest with sync results."""
    manifest["last_updated"] = datetime.now().isoformat()

    for cat_name, cat_results in results.get("categories", {}).items():
        if cat_name not in manifest["categories"]:
            mapping = get_category_mappings()[cat_name]
            manifest["categories"][cat_name] = {
                "source_dir": str(mapping["source"].relative_to(REPO_ROOT)),
                "target_dir": str(mapping["target"].relative_to(REPO_ROOT)),
                "files": []
            }

        for result in cat_results:
            if result.get("synced"):
                source_path = Path(result["source"])
                file_entry = {
                    "filename": source_path.name,
                    "source_path": str(source_path.relative_to(REPO_ROOT)),
                    "target_path": result["target"],
                    "source_hash": result["source_hash"],
                    "last_synced": result.get("synced_at", datetime.now().isoformat()),
                    "sync_status": "synced",
                    "file_size_bytes": result.get("size_bytes", 0)
                }

                # Update or append
                existing_idx = None
                for idx, f in enumerate(manifest["categories"][cat_name]["files"]):
                    if f["filename"] == file_entry["filename"]:
                        existing_idx = idx
                        break

                if existing_idx is not None:
                    manifest["categories"][cat_name]["files"][existing_idx] = file_entry
                else:
                    manifest["categories"][cat_name]["files"].append(file_entry)

    # Update visuals
    for result in results.get("visuals", []):
        if result.get("synced"):
            source_path = Path(result["source"])
            file_entry = {
                "filename": source_path.name,
                "source_hash": result["source_hash"],
                "last_synced": result.get("synced_at", datetime.now().isoformat()),
                "sync_status": "synced",
                "file_size_bytes": result.get("size_bytes", 0)
            }

            existing_idx = None
            for idx, f in enumerate(manifest["visuals"]["files"]):
                if f["filename"] == file_entry["filename"]:
                    existing_idx = idx
                    break

            if existing_idx is not None:
                manifest["visuals"]["files"][existing_idx] = file_entry
            else:
                manifest["visuals"]["files"].append(file_entry)

    # Update validation (REVIEW_NOTES_*.md)
    if "validation" not in manifest:
        manifest["validation"] = {"files": []}

    for result in results.get("validation", []):
        if result.get("synced"):
            source_path = Path(result["source"])
            file_entry = {
                "filename": source_path.name,
                "source_hash": result["source_hash"],
                "last_synced": result.get("synced_at", datetime.now().isoformat()),
                "sync_status": "synced",
                "file_size_bytes": result.get("size_bytes", 0)
            }

            existing_idx = None
            for idx, f in enumerate(manifest["validation"]["files"]):
                if f["filename"] == file_entry["filename"]:
                    existing_idx = idx
                    break

            if existing_idx is not None:
                manifest["validation"]["files"][existing_idx] = file_entry
            else:
                manifest["validation"]["files"].append(file_entry)

    # Update analysis (--full mode subdirectories)
    if "analysis" not in manifest:
        manifest["analysis"] = {"deep_dives": [], "future": [], "experiments": []}

    for atype, atype_results in results.get("analysis", {}).items():
        if atype not in manifest["analysis"]:
            manifest["analysis"][atype] = []

        for result in atype_results:
            if result.get("synced"):
                source_path = Path(result["source"])
                file_entry = {
                    "filename": source_path.name,
                    "source_hash": result["source_hash"],
                    "last_synced": result.get("synced_at", datetime.now().isoformat()),
                    "sync_status": "synced",
                    "file_size_bytes": result.get("size_bytes", 0)
                }

                existing_idx = None
                for idx, f in enumerate(manifest["analysis"][atype]):
                    if f["filename"] == file_entry["filename"]:
                        existing_idx = idx
                        break

                if existing_idx is not None:
                    manifest["analysis"][atype][existing_idx] = file_entry
                else:
                    manifest["analysis"][atype].append(file_entry)

    # Add to history
    manifest["sync_history"].append({
        "timestamp": results["timestamp"],
        "operation": "sync",
        "files_synced": results["summary"]["synced"],
        "files_skipped": results["summary"]["already_synced"],
        "dry_run": results["dry_run"]
    })

    # Keep only last 20 history entries
    manifest["sync_history"] = manifest["sync_history"][-20:]

    # Update summary
    total_files = sum(len(cat.get("files", [])) for cat in manifest["categories"].values())
    total_files += len(manifest["visuals"].get("files", []))
    total_files += len(manifest.get("validation", {}).get("files", []))
    # Add analysis files
    for atype_files in manifest.get("analysis", {}).values():
        total_files += len(atype_files) if isinstance(atype_files, list) else 0
    total_size = sum(
        f.get("file_size_bytes", 0)
        for cat in manifest["categories"].values()
        for f in cat.get("files", [])
    )
    total_size += sum(f.get("file_size_bytes", 0) for f in manifest["visuals"].get("files", []))
    total_size += sum(f.get("file_size_bytes", 0) for f in manifest.get("validation", {}).get("files", []))
    # Add analysis file sizes
    for atype_files in manifest.get("analysis", {}).values():
        if isinstance(atype_files, list):
            total_size += sum(f.get("file_size_bytes", 0) for f in atype_files)

    manifest["summary"] = {
        "total_files": total_files,
        "total_synced": total_files,
        "total_pending": 0,
        "total_size_mb": round(total_size / (1024 * 1024), 2)
    }


def generate_status_report(category: Optional[str] = None) -> str:
    """
    Generate comprehensive status report showing:
    - Files by category
    - Sync status (pending vs synced)
    - Last sync timestamps
    - Source/target paths
    """
    manifest = load_manifest()
    lines = [
        "=" * 60,
        "LLM_BOOK -> WHITE-PAPER SYNC STATUS",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        f"Source: {LLM_BOOK_DIR.relative_to(REPO_ROOT)}",
        f"Target: {WHITE_PAPER_DIR.relative_to(REPO_ROOT)}/submissions/",
        "",
        "## Category Status",
    ]

    category_mappings = get_category_mappings()
    categories_to_report = [category] if category else category_mappings.keys()
    total_files = 0
    total_synced = 0
    total_pending = 0
    total_size = 0

    for cat_name in categories_to_report:
        if cat_name not in category_mappings:
            continue

        mapping = category_mappings[cat_name]
        sources = discover_source_files(cat_name)
        source_files = sources.get(cat_name, [])

        lines.append(f"\n### {cat_name} -> {mapping['target'].relative_to(WHITE_PAPER_DIR)}/")
        lines.append(f"  Source files found: {len(source_files)}")

        for source_file in source_files:
            needs_sync, reason = file_needs_sync(source_file, mapping["target"], manifest)
            size_kb = source_file.stat().st_size / 1024
            total_size += source_file.stat().st_size
            total_files += 1

            if needs_sync:
                total_pending += 1
                lines.append(f"    [!] {source_file.name} ({size_kb:.0f} KB) - PENDING ({reason})")
            else:
                total_synced += 1
                lines.append(f"    [*] {source_file.name} ({size_kb:.0f} KB) - SYNCED")

    # Validation (REVIEW_NOTES_*.md)
    validation_files = discover_validation_files()
    if validation_files:
        validation_mapping = get_validation_mapping()
        lines.append(f"\n### validation -> {validation_mapping['target'].relative_to(WHITE_PAPER_DIR)}/")
        lines.append(f"  Source files found: {len(validation_files)}")

        for source_file in validation_files:
            needs_sync, reason = file_needs_sync(source_file, validation_mapping["target"], manifest)
            size_kb = source_file.stat().st_size / 1024
            total_size += source_file.stat().st_size
            total_files += 1

            if needs_sync:
                total_pending += 1
                lines.append(f"    [!] {source_file.name} ({size_kb:.0f} KB) - PENDING ({reason})")
            else:
                total_synced += 1
                lines.append(f"    [*] {source_file.name} ({size_kb:.0f} KB) - SYNCED")

    # Analysis (--full mode subdirectories)
    analysis_files = discover_analysis_files()
    analysis_mappings = get_analysis_mappings()
    for atype, atype_files in analysis_files.items():
        if atype_files:
            mapping = analysis_mappings[atype]
            lines.append(f"\n### analysis/{atype} -> {mapping['target'].relative_to(WHITE_PAPER_DIR)}/")
            lines.append(f"  Source files found: {len(atype_files)}")

            for source_file in atype_files:
                needs_sync, reason = file_needs_sync(source_file, mapping["target"], manifest)
                size_kb = source_file.stat().st_size / 1024
                total_size += source_file.stat().st_size
                total_files += 1

                if needs_sync:
                    total_pending += 1
                    lines.append(f"    [!] {source_file.name} ({size_kb:.0f} KB) - PENDING ({reason})")
                else:
                    total_synced += 1
                    lines.append(f"    [*] {source_file.name} ({size_kb:.0f} KB) - SYNCED")

    # Visuals
    visual_files = discover_visual_files()
    if visual_files:
        lines.append(f"\n### visuals -> {VISUAL_MAPPING['target'].relative_to(WHITE_PAPER_DIR)}/")
        lines.append(f"  Source files found: {len(visual_files)}")

        for source_file in visual_files:
            needs_sync, reason = file_needs_sync(source_file, VISUAL_MAPPING["target"], manifest)
            size_mb = source_file.stat().st_size / (1024 * 1024)
            total_size += source_file.stat().st_size
            total_files += 1

            if needs_sync:
                total_pending += 1
                lines.append(f"    [!] {source_file.name} ({size_mb:.1f} MB) - PENDING ({reason})")
            else:
                total_synced += 1
                lines.append(f"    [*] {source_file.name} ({size_mb:.1f} MB) - SYNCED")

    # Summary
    lines.extend([
        "",
        "## Summary",
        f"  Total files:     {total_files}",
        f"  Synced:          {total_synced}",
        f"  Pending:         {total_pending}",
        f"  Total size:      {total_size / (1024*1024):.1f} MB",
    ])

    if manifest.get("sync_history"):
        last_sync = manifest["sync_history"][-1]
        lines.append(f"  Last sync:       {last_sync.get('timestamp', 'never')}")

    lines.extend([
        "",
        "=" * 60,
        "To sync pending files: py 1_sync_llmbook.py --sync",
        "To preview changes:    py 1_sync_llmbook.py --sync --dry-run",
        "=" * 60,
    ])

    return "\n".join(lines)


def generate_sync_report(results: Dict) -> str:
    """Generate report of sync operation results."""
    lines = [
        "=" * 60,
        "LLM_BOOK -> WHITE-PAPER SYNC REPORT",
        f"Timestamp: {results['timestamp']}",
        f"Mode: {'DRY RUN' if results['dry_run'] else 'APPLIED'}",
        "=" * 60,
    ]

    for cat_name, cat_results in results.get("categories", {}).items():
        lines.append(f"\n## {cat_name}")
        for r in cat_results:
            if r.get("synced") or r.get("reason"):
                status = "[*] SYNCED" if r.get("synced") else f"[!] WOULD SYNC ({r.get('reason')})"
                source = Path(r.get("source", "")).name
                lines.append(f"  {status}: {source}")
            elif r.get("status") == "already_synced":
                source = Path(r.get("source", "")).name
                lines.append(f"  - Already synced: {source}")

    if results.get("validation"):
        lines.append("\n## Validation (REVIEW_NOTES_*.md)")
        for r in results["validation"]:
            if r.get("synced") or r.get("reason"):
                status = "[*] SYNCED" if r.get("synced") else f"[!] WOULD SYNC ({r.get('reason')})"
                source = Path(r.get("source", "")).name
                lines.append(f"  {status}: {source}")
            elif r.get("status") == "already_synced":
                source = Path(r.get("source", "")).name
                lines.append(f"  - Already synced: {source}")

    if results.get("analysis"):
        for atype, atype_results in results["analysis"].items():
            if atype_results:
                lines.append(f"\n## Analysis/{atype}")
                for r in atype_results:
                    if r.get("synced") or r.get("reason"):
                        status = "[*] SYNCED" if r.get("synced") else f"[!] WOULD SYNC ({r.get('reason')})"
                        source = Path(r.get("source", "")).name
                        lines.append(f"  {status}: {source}")
                    elif r.get("status") == "already_synced":
                        source = Path(r.get("source", "")).name
                        lines.append(f"  - Already synced: {source}")

    if results.get("visuals"):
        lines.append("\n## Visuals")
        for r in results["visuals"]:
            if r.get("synced") or r.get("reason"):
                status = "[*] SYNCED" if r.get("synced") else f"[!] WOULD SYNC ({r.get('reason')})"
                source = Path(r.get("source", "")).name
                lines.append(f"  {status}: {source}")
            elif r.get("status") == "already_synced":
                source = Path(r.get("source", "")).name
                lines.append(f"  - Already synced: {source}")

    lines.extend([
        "",
        "## Summary",
        f"  Total processed: {results['summary']['total_processed']}",
        f"  Synced:          {results['summary']['synced']}",
        f"  Already synced:  {results['summary']['already_synced']}",
        f"  Errors:          {results['summary']['errors']}",
    ])

    if results["dry_run"]:
        lines.append("\nDry run complete. Use --sync without --dry-run to apply.")
    else:
        lines.append("\nSync complete. Manifest updated.")

    return "\n".join(lines)


def update_sync_status_md(results: Dict) -> None:
    """Optionally append sync results to reviewers/SYNC_STATUS.md."""
    if not SYNC_STATUS_PATH.exists():
        return

    # Read existing content
    content = SYNC_STATUS_PATH.read_text(encoding="utf-8")

    # Find Communication Log section and append
    timestamp = datetime.now().strftime("%Y-%m-%d")
    sync_count = results["summary"]["synced"]

    log_entry = f"| {timestamp} | SYNC | LLM_BOOK -> WHITE-PAPER | Full sync ({sync_count} files) | LLMBOOK_SYNC_MANIFEST.json |"

    # Append to Communication Log if it exists
    if "## Communication Log" in content:
        # Find the table in that section and append
        # This is a simplified implementation
        pass

    # For now, just note that we would update it
    print(f"  Would append to SYNC_STATUS.md: {log_entry}")


def main():
    parser = argparse.ArgumentParser(
        description="LLM_BOOK -> WHITE-PAPER Sync Framework",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py 1_sync_llmbook.py                          # Show status report
  py 1_sync_llmbook.py --sync                   # Sync all categories
  py 1_sync_llmbook.py --sync --dry-run         # Preview sync changes
  py 1_sync_llmbook.py --category popular_science  # Status for one category
  py 1_sync_llmbook.py --sync --include-visuals # Sync content + visuals
  py 1_sync_llmbook.py --sync --category media  # Sync only media category
        """
    )

    # Action modes
    parser.add_argument("--sync", action="store_true",
                        help="Perform sync (default: report only)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")

    # Scope controls
    parser.add_argument("--category",
                        choices=["academic", "popular_science", "education", "policy", "funding", "media", "all"],
                        default=None,
                        help="Category to sync/report on")
    parser.add_argument("--include-visuals", action="store_true",
                        help="Also sync 3_VISUALS/ to figures/generated/llmbook/")

    # Output controls
    parser.add_argument("--json", action="store_true",
                        help="Output report as JSON instead of text")
    parser.add_argument("--update-status", action="store_true",
                        help="Update reviewers/SYNC_STATUS.md after sync")

    args = parser.parse_args()

    # Handle "all" category
    category = None if args.category == "all" else args.category

    if not args.sync:
        # Report mode
        if args.json:
            manifest = load_manifest()
            print(json.dumps(manifest, indent=2))
        else:
            print(generate_status_report(category))
    else:
        # Sync mode
        results = sync_all(
            dry_run=args.dry_run,
            include_visuals=args.include_visuals,
            category=category
        )

        if args.json:
            print(json.dumps(results, indent=2))
        else:
            print(generate_sync_report(results))

        if args.update_status and not args.dry_run:
            update_sync_status_md(results)


if __name__ == "__main__":
    main()
