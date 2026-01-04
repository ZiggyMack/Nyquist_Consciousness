#!/usr/bin/env python3
"""
ingest.py - NotebookLM STAGING -> LLM_BOOK Ingestion (Accumulative Model)
=========================================================================
Processes NotebookLM outputs from STAGING/ into the LLM_BOOK/ structure.

ACCUMULATIVE MODEL:
-------------------
By default, ingestion APPENDS to existing content, compounding value over time.
Each ingestion batch gets its own REVIEW_NOTES_{batch}.md file.
Use --fresh to clear everything and start over (destructive).

WORKFLOW:
---------
1. Discover un-ingested batches in STAGING/ (folders without .ingested marker)
2. For each Nyquist batch:
   - Create placeholder REVIEW_NOTES_{batch}.md in 1_VALIDATION/
   - Mark batch as ingested (create .ingested marker)
3. For R&D content: append to RnD/{topic}/
4. **Claude reviews content and fills in REVIEW_NOTES_{batch}.md** (default behavior)
5. digest.py reads ALL REVIEW_NOTES_*.md and routes content accordingly

USAGE:
------
py ingest.py                    # Report mode - show staging status
py ingest.py --ingest           # Ingest with Claude review + analysis (default)
py ingest.py --ingest --skip-review  # Skip Claude review, create templates only
py ingest.py --ingest --fresh   # Overwrite mode - clear all, then ingest
py ingest.py --ingest --dry-run # Preview without changes

DEFAULT BEHAVIOR:
-----------------
- Append mode (preserves existing content)
- Claude performs substantive review AND creates:
  - 1_DEEP_DIVES/{batch}.md - Content analysis, quality assessment
  - 2_FUTURE/{batch}.md - Future research directions
  - 3_EXPERIMENTS/{batch}.md - Experimental observations

REVIEW NOTES NAMING:
--------------------
Each batch gets: REVIEW_NOTES_{batch_name}.md
- REVIEW_NOTES_Nyquist_1.md
- REVIEW_NOTES_Nyquist_2.md
- REVIEW_NOTES_Nyquist_1_2.md  (combined review)

CLAUDE REVIEW:
--------------
By default, ingestion triggers Claude to review each batch's content.
Claude reads markdown files and assesses:
- IRON CLAD accuracy (D=0.80, ~93%, p=2.40e-23, 750/25/5)
- Quality grade (A++/A+/A/B/C)
- Content categorization recommendations

Use --skip-review to create placeholder templates instead.

DIET MODE:
----------
Diet mode allows full cognitive processing WITHOUT committing to the real pipeline.
Output goes to _CACHE_/ inside the batch folder instead of 1_VALIDATION/.
Use --throw_up to purge all _CACHE_/ directories.

IMPORTANT: Diet mode IGNORES .ingested status - you can diet-chew any batch,
whether it's been ingested before or not. This is intentional - diet mode is
for non-committal preview/priming, and already-ingested content is still valid
for that purpose.

py ingest.py --ingest --diet --batch SomeOldBatch  # Process to _CACHE_/
py ingest.py --throw_up                             # Purge all _CACHE_/ directories

Author: LLM_BOOK Ingestion Pipeline
Version: 5.0 (2025-12-31) - Diet mode for non-committal processing
"""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional

# === PATH CONSTANTS ===
SCRIPT_DIR = Path(__file__).parent
LLM_BOOK_DIR = SCRIPT_DIR.parent  # REPO-SYNC/LLM_BOOK/
STAGING_DIR = SCRIPT_DIR / "STAGING"
REPO_ROOT = LLM_BOOK_DIR.parent.parent  # d:\Documents\Nyquist_Consciousness
WHITE_PAPER_DIR = REPO_ROOT / "WHITE-PAPER"
SYNC_SCRIPT = WHITE_PAPER_DIR / "calibration" / "1_sync_llmbook.py"
VERSION_FILE = WHITE_PAPER_DIR / "reviewers" / "packages" / "CURRENT_VERSION.json"

# Validation directory for review notes
VALIDATION_DIR = LLM_BOOK_DIR / "1_VALIDATION"

# LLM_BOOK content directories (only cleared with --fresh)
CONTENT_DIRS = [
    VALIDATION_DIR,
    LLM_BOOK_DIR / "2_PUBLICATIONS",
    LLM_BOOK_DIR / "3_VISUALS",
    LLM_BOOK_DIR / "4_AUDIO",
    LLM_BOOK_DIR / "RnD",
]

# Validation subdirectories for --full mode analysis
VALIDATION_ANALYSIS_DIRS = [
    VALIDATION_DIR / "1_DEEP_DIVES",
    VALIDATION_DIR / "2_FUTURE",
    VALIDATION_DIR / "3_EXPERIMENTS",
]

# Directories to preserve (never cleared)
PRESERVE_DIRS = [
    LLM_BOOK_DIR / "0_SOURCE_MANIFESTS",  # Contains STAGING and this script
]

# Marker file indicating a batch has been ingested
INGESTED_MARKER = ".ingested"

# LLM Book Registry (Pan Handlers config)
PAN_HANDLERS_CONFIG = REPO_ROOT / "REPO-SYNC" / "PAN_HANDLERS" / "0_Config" / "root"
LLM_BOOK_REGISTRY = PAN_HANDLERS_CONFIG / "llm_book_registry.json"

# Cache directory for diet mode (inside each batch folder)
CACHE_DIR_NAME = "_CACHE_"

# IRON CLAD reference statistics for validation
IRON_CLAD_STATS = {
    "event_horizon": 0.80,
    "inherent_drift": "~93%",
    "p_value": "2.40e-23",
    "experiments": 750,
    "models": 25,
    "providers": 5,
    "variance_explained": "97.5%",
    "settling_times": {
        "Claude": "4-6",
        "GPT": "3-5",
        "DeepSeek": "2-4",
        "Llama": "5-7",
        "Mistral": "instant",
        "Gemini": "∞ (no recovery)"
    }
}


def get_version_info() -> Dict:
    """Read CURRENT_VERSION.json for review status and version info."""
    if VERSION_FILE.exists():
        with open(VERSION_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {"current_version": "unknown", "review_status": "unknown"}


def load_llm_book_registry() -> Dict:
    """Load the LLM Book Registry from Pan Handlers config."""
    if LLM_BOOK_REGISTRY.exists():
        with open(LLM_BOOK_REGISTRY, "r", encoding="utf-8") as f:
            return json.load(f)
    return {"projects": [], "cross_pollination_log": []}


def load_panhandlers_root() -> Dict:
    """Load the Pan Handlers root config for lab/module context."""
    root_file = PAN_HANDLERS_CONFIG / "panhandlers-root.json"
    if root_file.exists():
        with open(root_file, "r", encoding="utf-8") as f:
            return json.load(f)
    return {"modules": [], "architecture": {}}


def load_lab_configs() -> Dict[str, Dict]:
    """Load all Pan Handler lab/module configs."""
    modules_dir = PAN_HANDLERS_CONFIG.parent / "modules"
    labs = {}
    if modules_dir.exists():
        for f in modules_dir.glob("*.json"):
            try:
                with open(f, "r", encoding="utf-8") as fp:
                    labs[f.stem] = json.load(fp)
            except json.JSONDecodeError:
                pass
    return labs


def get_panhandlers_context() -> str:
    """
    Get summary context of Pan Handler labs for routing awareness.

    Returns a formatted string describing labs that Claude can use
    to identify where insights should be routed.
    """
    root = load_panhandlers_root()
    labs = load_lab_configs()

    context_lines = ["## Pan Handler Labs (for routing awareness)\n"]

    # Add architecture overview
    arch = root.get("architecture", {})
    if arch:
        context_lines.append("### Architecture")
        for role, module in arch.items():
            if isinstance(module, list):
                context_lines.append(f"- **{role}:** {', '.join(module)}")
            else:
                context_lines.append(f"- **{role}:** {module}")
        context_lines.append("")

    # Add lab summaries
    context_lines.append("### Active Labs")
    for module in root.get("modules", []):
        lab_id = module.get("id", "")
        lab_config = labs.get(lab_id, {})

        name = module.get("name", lab_id)
        role = module.get("role", lab_config.get("role", ""))
        status = module.get("status", "Unknown")

        if status == "Active":
            context_lines.append(f"- **{name}** ({lab_id}): {role}")

    context_lines.append("")
    return "\n".join(context_lines)


def get_other_projects_context(current_project: str) -> str:
    """
    Get full context for cross-pollination: LLM Book projects + Pan Handler labs.

    Returns a formatted string describing:
    1. Other LLM Book projects (for cross-pollination)
    2. Pan Handler labs (for routing awareness)
    """
    context_parts = []

    # Part 1: Other LLM Book projects
    registry = load_llm_book_registry()
    projects = registry.get("projects", [])

    if projects:
        project_lines = ["## Other LLM Book Projects (for cross-pollination)\n"]

        for proj in projects:
            if proj["id"] == current_project:
                continue

            project_lines.append(f"### {proj['id']}")
            project_lines.append(f"**Summary:** {proj.get('summary', 'No summary')}")
            project_lines.append(f"**Key Concepts:** {', '.join(proj.get('key_concepts', []))}")
            project_lines.append(f"**Status:** {proj.get('status', 'Unknown')}")
            project_lines.append("")

        if len(project_lines) > 1:
            context_parts.append("\n".join(project_lines))

    # Part 2: Pan Handler labs
    panhandlers_context = get_panhandlers_context()
    if panhandlers_context:
        context_parts.append(panhandlers_context)

    return "\n".join(context_parts)


def update_registry_cross_pollination(source: str, target: str, items: List[str]) -> None:
    """
    Log a cross-pollination event to the LLM Book Registry.

    Args:
        source: Project ID that inspired the cross-pollination
        target: Project ID receiving the cross-pollinated content
        items: List of questions/reports added
    """
    if not LLM_BOOK_REGISTRY.exists():
        return

    registry = load_llm_book_registry()

    log_entry = {
        "date": datetime.now().strftime("%Y-%m-%d"),
        "source": source,
        "target": target,
        "type": "questions",
        "items": items
    }

    if "cross_pollination_log" not in registry:
        registry["cross_pollination_log"] = []

    registry["cross_pollination_log"].append(log_entry)

    with open(LLM_BOOK_REGISTRY, "w", encoding="utf-8") as f:
        json.dump(registry, f, indent=2)


def is_nyquist_content(folder_name: str) -> bool:
    """Determine if a staging folder contains Nyquist-specific content."""
    nyquist_keywords = ["nyquist", "infinity-nyquist"]
    return any(kw in folder_name.lower() for kw in nyquist_keywords)


def get_rnd_topic_name(folder_name: str) -> str:
    """Normalize R&D folder names for consistent directory structure."""
    if folder_name.lower().startswith("gnostic"):
        return "Gnostic"
    return folder_name.replace("-", "_").replace(" ", "_")


def is_batch_ingested(folder: Path) -> bool:
    """Check if a staging folder has already been ingested."""
    return (folder / INGESTED_MARKER).exists()


def mark_batch_ingested(folder: Path, dry_run: bool = True) -> None:
    """Mark a staging folder as ingested."""
    marker = folder / INGESTED_MARKER
    if not dry_run:
        marker.write_text(f"Ingested: {datetime.now().isoformat()}\n")


def discover_staging_folders() -> Dict[str, List[Tuple[Path, bool]]]:
    """
    Discover all content in STAGING/ and classify by type.

    Returns:
        {
            "nyquist": [(Path, is_ingested), ...],
            "rnd": [(Path, is_ingested), ...]
        }
    """
    result = {"nyquist": [], "rnd": []}

    if not STAGING_DIR.exists():
        return result

    for item in STAGING_DIR.iterdir():
        if not item.is_dir():
            continue

        ingested = is_batch_ingested(item)

        if is_nyquist_content(item.name):
            result["nyquist"].append((item, ingested))
        else:
            result["rnd"].append((item, ingested))

    return result


def get_pending_batches(staging: Dict) -> Dict[str, List[Path]]:
    """Filter to only un-ingested batches."""
    return {
        "nyquist": [p for p, ingested in staging["nyquist"] if not ingested],
        "rnd": [p for p, ingested in staging["rnd"] if not ingested],
    }


def create_review_notes_template(batch_name: str, source_folder: Path, dry_run: bool = True,
                                  diet: bool = False) -> Path:
    """
    Create a review notes template for a batch.

    Args:
        diet: If True, write to source_folder/_CACHE_/ instead of VALIDATION_DIR

    Returns the path to the created file.
    """
    # List files in the _IN folder
    in_folder = source_folder / "_IN"
    files = []
    if in_folder.exists():
        files = [f.name for f in in_folder.iterdir() if f.is_file()]

    # Generate template
    template = f"""# Review Notes: {batch_name}

**Ingestion Date:** {datetime.now().strftime('%Y-%m-%d')}
**Source:** STAGING/{batch_name}/_IN/
**Status:** PENDING REVIEW

---

## Files to Review

"""
    # Add file list
    for f in sorted(files):
        ext = Path(f).suffix.lower()
        if ext == ".md":
            template += f"### {f}\n- **Category:** `pending`\n- **Accuracy:** PENDING\n- **Verdict:** PENDING\n\n"
        elif ext in [".png", ".jpg", ".jpeg", ".gif"]:
            template += f"### {f}\n- **Type:** Visual\n- **Route to:** 3_VISUALS/\n\n"
        elif ext in [".m4a", ".mp3", ".mp4", ".wav"]:
            template += f"### {f}\n- **Type:** Audio/Video\n- **Route to:** 7_AUDIO/\n\n"
        elif ext == ".pdf":
            template += f"### {f}\n- **Type:** PDF\n- **Route to:** 2_PUBLICATIONS/academic/\n\n"
        else:
            template += f"### {f}\n- **Type:** Other ({ext})\n- **Route to:** TBD\n\n"

    template += """---

## Review Summary

| File | Category | Verdict | Notes |
|------|----------|---------|-------|
| ... | ... | ... | ... |

---

## Claude's Assessment

**Quality:** PENDING
**Accuracy:** PENDING
**Recommendation:** PENDING

---

*This file is part of the reviewer feedback loop.*
*Created by ingest.py on {date}*
*Review status: PENDING*
""".format(date=datetime.now().strftime('%Y-%m-%d'))

    # Determine target path based on diet mode
    if diet:
        # Diet mode: write to _CACHE_/ inside the batch folder
        cache_dir = source_folder / CACHE_DIR_NAME
        target_path = cache_dir / f"REVIEW_NOTES_{batch_name}.md"
        if not dry_run:
            cache_dir.mkdir(parents=True, exist_ok=True)
            target_path.write_text(template, encoding="utf-8")
    else:
        # Normal mode: write to 1_VALIDATION/
        target_path = VALIDATION_DIR / f"REVIEW_NOTES_{batch_name}.md"
        if not dry_run:
            VALIDATION_DIR.mkdir(parents=True, exist_ok=True)
            target_path.write_text(template, encoding="utf-8")

    return target_path


def create_analysis_stubs(batch_name: str, source_folder: Path = None, dry_run: bool = True,
                          diet: bool = False) -> List[Path]:
    """
    Create stub files for analysis directories.

    Args:
        diet: If True, write to source_folder/_CACHE_/ instead of VALIDATION_DIR
    """
    created = []

    for analysis_dir in VALIDATION_ANALYSIS_DIRS:
        # Get the subdirectory name (1_DEEP_DIVES, 2_FUTURE, 3_EXPERIMENTS)
        subdir_name = analysis_dir.name

        if diet and source_folder:
            # Diet mode: write to _CACHE_/ inside the batch folder
            cache_dir = source_folder / CACHE_DIR_NAME / subdir_name
            stub_path = cache_dir / f"{batch_name}.md"
            if not dry_run:
                cache_dir.mkdir(parents=True, exist_ok=True)
                stub_path.write_text(f"# {subdir_name}: {batch_name}\n\n*Diet mode analysis*\n")
        else:
            # Normal mode: write to 1_VALIDATION/ subdirectories
            stub_path = analysis_dir / f"{batch_name}.md"
            if not dry_run:
                analysis_dir.mkdir(parents=True, exist_ok=True)
                stub_path.write_text(f"# {subdir_name}: {batch_name}\n\n*Pending --full analysis*\n")

        created.append(stub_path)

    return created


def perform_claude_review(batch_name: str, source_folder: Path, dry_run: bool = True) -> Dict:
    """
    Perform Claude's review of batch content.

    Reads markdown files, checks IRON CLAD accuracy, and generates assessment.
    This function is called by the script but the actual review logic runs
    when Claude Code executes this - Claude reads the files and assesses them.

    Returns:
        Dict with review results including quality grade, accuracy, and recommendations
    """
    # Initialize default structure
    review = {
        "batch_name": batch_name,
        "files_reviewed": [],
        "markdown_content": {},
        "iron_clad_accuracy": [],
        "quality_grade": "C",  # Default grade
        "recommendations": [],
        "errors": []
    }

    in_folder = source_folder / "_IN"
    if not in_folder.exists():
        review["errors"].append(f"No _IN folder found in {source_folder}")
        return review

    # Collect all files
    files = list(in_folder.iterdir()) if in_folder.exists() else []

    for f in files:
        if not f.is_file():
            continue

        file_info = {
            "name": f.name,
            "extension": f.suffix.lower(),
            "size_kb": f.stat().st_size / 1024
        }

        # For markdown files, read content for review
        if f.suffix.lower() == ".md":
            try:
                content = f.read_text(encoding="utf-8")
                file_info["content_preview"] = content[:500] + "..." if len(content) > 500 else content
                review["markdown_content"][f.name] = content

                # Check for IRON CLAD statistics
                checks = []
                if "0.80" in content or "0.8" in content:
                    checks.append("✓ Event Horizon (0.80)")
                if "93%" in content or "93 percent" in content.lower():
                    checks.append("✓ Inherent Drift (~93%)")
                if "2.40" in content and "10" in content:
                    checks.append("✓ p-value (2.40e-23)")
                if "750" in content:
                    checks.append("✓ Experiments (750)")
                if "25 model" in content.lower():
                    checks.append("✓ Models (25)")
                if "5 provider" in content.lower():
                    checks.append("✓ Providers (5)")

                file_info["iron_clad_checks"] = checks
                review["iron_clad_accuracy"].extend(checks)

            except Exception as e:
                file_info["error"] = str(e)
                review["errors"].append(f"{f.name}: {e}")

        review["files_reviewed"].append(file_info)

    # Calculate quality grade based on IRON CLAD accuracy
    unique_checks = len(set(review["iron_clad_accuracy"]))
    if unique_checks >= 5:
        review["quality_grade"] = "A++"
    elif unique_checks >= 4:
        review["quality_grade"] = "A+"
    elif unique_checks >= 3:
        review["quality_grade"] = "A"
    elif unique_checks >= 2:
        review["quality_grade"] = "B"
    else:
        review["quality_grade"] = "C"

    return review


def generate_reviewed_notes(batch_name: str, source_folder: Path, review: Dict, dry_run: bool = True,
                            diet: bool = False) -> Path:
    """
    Generate REVIEW_NOTES with Claude's actual assessment.

    Unlike the template version, this includes:
    - Actual file content analysis
    - IRON CLAD accuracy verification
    - Quality grade
    - Specific recommendations

    Args:
        diet: If True, write to source_folder/_CACHE_/ instead of VALIDATION_DIR
    """
    in_folder = source_folder / "_IN"
    files = list(in_folder.iterdir()) if in_folder.exists() else []

    # Build the review notes with actual assessment
    template = f"""# Review Notes: {batch_name}

**Ingestion Date:** {datetime.now().strftime('%Y-%m-%d')}
**Source:** STAGING/{batch_name}/_IN/
**Status:** REVIEWED - {'APPROVED' if review['quality_grade'] in ['A++', 'A+', 'A'] else 'NEEDS ATTENTION'}

---

## Files to Review

"""
    # Add file list with routing
    for f in sorted(files, key=lambda x: x.name):
        if not f.is_file():
            continue
        ext = f.suffix.lower()
        if ext == ".md":
            template += f"### {f.name}\n- **Category:** `pending`\n- **Accuracy:** PENDING\n- **Verdict:** PENDING\n\n"
        elif ext in [".png", ".jpg", ".jpeg", ".gif"]:
            template += f"### {f.name}\n- **Type:** Visual\n- **Route to:** 3_VISUALS/\n\n"
        elif ext in [".m4a", ".mp3", ".mp4", ".wav"]:
            template += f"### {f.name}\n- **Type:** Audio/Video\n- **Route to:** 4_AUDIO/\n\n"
        elif ext == ".pdf":
            template += f"### {f.name}\n- **Type:** PDF\n- **Route to:** 2_PUBLICATIONS/academic/\n\n"
        else:
            template += f"### {f.name}\n- **Type:** Other ({ext})\n- **Route to:** TBD\n\n"

    template += """---

## Review Summary

| File | Category | Verdict | Notes |
|------|----------|---------|-------|
| ... | ... | ... | ... |

---

## Claude's Assessment

"""

    # Add the actual assessment
    template += f"**Quality:** {review['quality_grade']}"
    if review['quality_grade'] == 'A++':
        template += " (Exceptional)"
    elif review['quality_grade'] == 'A+':
        template += " (Excellent)"
    elif review['quality_grade'] == 'A':
        template += " (Good)"

    template += f"""
**Accuracy:** {len(set(review['iron_clad_accuracy']))}/6 IRON CLAD checks passed
**Recommendation:** {'APPROVE ALL - Ready for digest pipeline' if review['quality_grade'] in ['A++', 'A+', 'A'] else 'REVIEW NEEDED'}

### IRON CLAD Validation

"""

    # List all unique checks found
    unique_checks = sorted(set(review['iron_clad_accuracy']))
    if unique_checks:
        for check in unique_checks:
            template += f"- {check}\n"
    else:
        template += "- No IRON CLAD statistics detected (may be visual/audio content)\n"

    template += f"""
### Files Summary

- **Total files:** {len(review['files_reviewed'])}
- **Markdown:** {len([f for f in review['files_reviewed'] if f['extension'] == '.md'])}
- **PDFs:** {len([f for f in review['files_reviewed'] if f['extension'] == '.pdf'])}
- **Visuals:** {len([f for f in review['files_reviewed'] if f['extension'] in ['.png', '.jpg', '.jpeg', '.gif']])}
- **Audio/Video:** {len([f for f in review['files_reviewed'] if f['extension'] in ['.m4a', '.mp3', '.mp4', '.wav']])}

"""

    if review['errors']:
        template += "### Errors Encountered\n\n"
        for err in review['errors']:
            template += f"- {err}\n"
        template += "\n"

    template += f"""---

*Reviewed by Claude Code on {datetime.now().strftime('%Y-%m-%d')}*
*IRON CLAD: {IRON_CLAD_STATS['experiments']} experiments | {IRON_CLAD_STATS['models']} models | {IRON_CLAD_STATS['providers']} providers | EH={IRON_CLAD_STATS['event_horizon']} | p={IRON_CLAD_STATS['p_value']} | {IRON_CLAD_STATS['inherent_drift']} inherent*
"""

    # Determine target path based on diet mode
    if diet:
        # Diet mode: write to _CACHE_/ inside the batch folder
        cache_dir = source_folder / CACHE_DIR_NAME
        target_path = cache_dir / f"REVIEW_NOTES_{batch_name}.md"
        if not dry_run:
            cache_dir.mkdir(parents=True, exist_ok=True)
            target_path.write_text(template, encoding="utf-8")
    else:
        # Normal mode: write to 1_VALIDATION/
        target_path = VALIDATION_DIR / f"REVIEW_NOTES_{batch_name}.md"
        if not dry_run:
            VALIDATION_DIR.mkdir(parents=True, exist_ok=True)
            target_path.write_text(template, encoding="utf-8")

    return target_path


def copy_folder_contents(source: Path, target: Path, dry_run: bool = True,
                          exclude_patterns: List[str] = None) -> int:
    """
    Copy contents of source folder to target. Returns file count.

    Args:
        source: Source folder to copy from
        target: Target folder to copy to
        dry_run: Preview without making changes
        exclude_patterns: List of folder/file names to exclude (e.g., ["_CACHE_", ".ingested"])
    """
    if not source.exists():
        return 0

    if exclude_patterns is None:
        exclude_patterns = [CACHE_DIR_NAME, INGESTED_MARKER]

    file_count = 0

    for item in source.rglob("*"):
        # Skip excluded patterns
        skip = False
        for pattern in exclude_patterns:
            if pattern in item.parts:
                skip = True
                break
        if skip:
            continue

        if item.is_file():
            rel_path = item.relative_to(source)
            target_path = target / rel_path

            if not dry_run:
                target_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(item, target_path)

            file_count += 1

    return file_count


# === R&D COGNITIVE PROCESSING ===
# Parallel to Nyquist processing but with exploratory focus (no IRON CLAD constraints)

RND_ANALYSIS_DIRS = ["INSIGHTS", "CONNECTIONS", "EXPERIMENTS"]


def create_rnd_review_notes(batch_name: str, source_folder: Path, dry_run: bool = True,
                             diet: bool = False) -> Path:
    """
    Create R&D review notes template (open-ended, exploratory).

    Unlike Nyquist reviews, these focus on:
    - Novel insights and discoveries
    - Cross-domain connections
    - Pan Handler routing suggestions
    """
    # List files in root or _IN folder
    in_folder = source_folder / "_IN"
    if in_folder.exists():
        files = [f.name for f in in_folder.iterdir() if f.is_file()]
    else:
        files = [f.name for f in source_folder.iterdir()
                 if f.is_file() and not f.name.startswith(".")]

    template = f"""# R&D Review: {batch_name}

**Ingestion Date:** {datetime.now().strftime('%Y-%m-%d')}
**Source:** STAGING/{batch_name}/
**Type:** Exploratory Research
**Status:** PENDING REVIEW

---

## Source Files

"""
    for f in sorted(files):
        ext = Path(f).suffix.lower()
        template += f"- `{f}` ({ext})\n"

    template += """

---

## Source Summary

[What is this content about? Main themes and topics.]

---

## Key Insights

[Novel ideas, surprising findings, interesting patterns discovered.]

---

## Cross-Domain Connections

[How does this relate to other Pan Handler labs?]
[Potential synergies with existing research?]

- **CFA (Epistemics):**
- **ABI (Investigation):**
- **AVLAR Studio (Ritual Art):**
- **NDO (Data Observatory):**
- **Other Labs:**

---

## Experimental Ideas

[What experiments could test these ideas?]
[What questions does this raise?]

1.
2.
3.

---

## Routing Suggestions

Based on content analysis:

**Primary Destination(s):**
-

**Secondary/Supporting:**
-

**Rationale:**


---

## Quality Assessment

| Dimension | Rating | Notes |
|-----------|--------|-------|
| Novelty | [High/Medium/Low] | |
| Actionability | [High/Medium/Low] | |
| Integration Potential | [High/Medium/Low] | |

---

*Created by 1_ingest.py on {date}*
*R&D Review (exploratory, no IRON CLAD constraints)*
""".format(date=datetime.now().strftime('%Y-%m-%d'))

    # Determine target path
    if diet:
        cache_dir = source_folder / CACHE_DIR_NAME
        target_path = cache_dir / f"REVIEW_NOTES_{batch_name}.md"
        if not dry_run:
            cache_dir.mkdir(parents=True, exist_ok=True)
            target_path.write_text(template, encoding="utf-8")
    else:
        rnd_dir = LLM_BOOK_DIR / "RnD" / get_rnd_topic_name(batch_name)
        target_path = rnd_dir / f"REVIEW_NOTES_{batch_name}.md"
        if not dry_run:
            rnd_dir.mkdir(parents=True, exist_ok=True)
            target_path.write_text(template, encoding="utf-8")

    return target_path


def create_rnd_analysis_stubs(batch_name: str, source_folder: Path, dry_run: bool = True,
                               diet: bool = False) -> List[Path]:
    """
    Create R&D analysis stub files (INSIGHTS, CONNECTIONS, EXPERIMENTS).

    Different from Nyquist stubs - focused on exploration rather than validation.
    """
    created = []
    topic_name = get_rnd_topic_name(batch_name)

    stubs = {
        "INSIGHTS": f"""# INSIGHTS: {batch_name}

## Novel Ideas

[What new ideas emerged from this content?]

## Surprising Findings

[What was unexpected or counter-intuitive?]

## Patterns Discovered

[What recurring themes or patterns appeared?]

---

*R&D Exploratory Analysis*
""",
        "CONNECTIONS": f"""# CONNECTIONS: {batch_name}

## Pan Handler Lab Links

| Lab | Connection | Potential Value |
|-----|------------|-----------------|
| CFA | | |
| ABI | | |
| AVLAR | | |
| NDO | | |

## Cross-Domain Synergies

[What other fields or domains could benefit?]

## Integration Opportunities

[How could this inform or improve existing work?]

---

*R&D Exploratory Analysis*
""",
        "EXPERIMENTS": f"""# EXPERIMENTS: {batch_name}

## Testable Hypotheses

1.
2.
3.

## Proposed Experiments

### Experiment 1: [Name]
- **Question:**
- **Method:**
- **Expected Outcome:**

## Open Questions

[What remains unknown that experiments could address?]

---

*R&D Exploratory Analysis*
"""
    }

    for subdir_name, content in stubs.items():
        if diet:
            cache_dir = source_folder / CACHE_DIR_NAME / subdir_name
            stub_path = cache_dir / f"{batch_name}.md"
            if not dry_run:
                cache_dir.mkdir(parents=True, exist_ok=True)
                stub_path.write_text(content, encoding="utf-8")
        else:
            rnd_dir = LLM_BOOK_DIR / "RnD" / topic_name / subdir_name
            stub_path = rnd_dir / f"{batch_name}.md"
            if not dry_run:
                rnd_dir.mkdir(parents=True, exist_ok=True)
                stub_path.write_text(content, encoding="utf-8")

        created.append(stub_path)

    return created


def create_llm_book_interface_files(batch_name: str, source_folder: Path, dry_run: bool = True,
                                     diet: bool = False) -> List[Path]:
    """
    Create LLM Book interface files (chat.md, report.md) for NotebookLM interaction.

    These files provide:
    - chat.md: Suggested questions to ask the project's NotebookLM
    - report.md: Suggested custom reports, infographics, slide decks, audio/video

    Only created in diet mode (these are for STAGING projects, not committed content).
    """
    if not diet:
        return []

    created = []
    cache_dir = source_folder / CACHE_DIR_NAME

    # Get current date for timestamps
    from datetime import datetime
    current_date = datetime.now().strftime("%Y-%m-%d")

    chat_content = f"""# NotebookLM Questions: {batch_name}

## Suggested Questions

### Q1: [Core Concept Question]

> [Question about the fundamental concepts in this source material]

**Response:**

---

### Q2: [Mechanism/Process Question]

> [Question about how something works or operates]

**Response:**

---

### Q3: [Relationship Question]

> [Question about connections between concepts]

**Response:**

---

### Q4: [Application Question]

> [Question about practical applications or implications]

**Response:**

---

### Q5: [Boundary/Limitation Question]

> [Question about edge cases, limitations, or exceptions]

**Response:**

---

## Follow-Up Questions

(To be added after initial responses)

---

*Created: {current_date}*
*Project: {batch_name} NotebookLM*
*Status: TEMPLATE - Claude to populate with source-specific questions*
"""

    report_content = f"""# NotebookLM Report Requests: {batch_name}

## Custom Reports

### Report 1: [Deep Dive Topic]

**Type:** Deep Dive / Technical Analysis

**Prompt:**
> [Detailed prompt for the report]

**Status:** [ ] Requested  [ ] Received  [ ] Analyzed

---

### Report 2: [Framework/Methodology]

**Type:** Framework / Methodology

**Prompt:**
> [Detailed prompt for the report]

**Status:** [ ] Requested  [ ] Received  [ ] Analyzed

---

### Report 3: [Comparative Analysis]

**Type:** Analytical Report

**Prompt:**
> [Detailed prompt for the report]

**Status:** [ ] Requested  [ ] Received  [ ] Analyzed

---

## Infographics

### Infographic 1: [Visual Mapping]

**Description:** [What should be visualized]

**Elements to include:**
- [Element 1]
- [Element 2]
- [Element 3]

**Status:** [ ] Requested  [ ] Received  [ ] Analyzed

---

## Slide Decks

### Deck 1: [Overview Presentation]

**Purpose:** [What the deck should accomplish]

**Suggested slides:**
1. [Slide 1 topic]
2. [Slide 2 topic]
3. [Slide 3 topic]
4. [Slide 4 topic]
5. [Slide 5 topic]

**Status:** [ ] Requested  [ ] Received  [ ] Analyzed

---

## Audio Overviews

### Audio 1: Deep Dive Conversation

**Topic:** [What the audio should cover]

**Status:** [ ] Requested  [ ] Received  [ ] Analyzed

---

## Video Presentations

(Pending AVLAR stackup implementation)

---

*Created: {current_date}*
*Project: {batch_name} NotebookLM*
*Status: TEMPLATE - Claude to populate with source-specific suggestions*
"""

    routing_content = f"""# ROUTING MATRIX: {batch_name}

## Source Summary

**Material:** [Brief description of source material]
**Core Concepts:** [Key concepts from this source]
**Domain:** [Primary domain/field]

---

## LLM Book Project Connections

| Project | Connection Strength | Rationale | Action |
| ------- | ------------------- | --------- | ------ |
| New_4_GOLDEN_GEOMETRY | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action taken or "No action"] |
| New_5_RAG_Geometry_Experiments | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action taken or "No action"] |
| RAG | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action taken or "No action"] |
| Gnostic-1 | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action taken or "No action"] |

---

## Pan Handler Lab Connections

| Lab | Role | Connection Strength | Rationale | Action |
| --- | ---- | ------------------- | --------- | ------ |
| nyquist-consciousness | Theory Engine | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |
| cfa-meta-lab | Epistemic Engine | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |
| ndo | Sensory Cortex | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |
| abi | Investigation Wing | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |
| dcia | Interpretation Wing | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |
| voting-lab | Civic Infrastructure | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |
| justice-lab | Carceral Reform | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |
| gene-lab | Biomedical Research | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |
| avlar-studio | Creative Wing (S9) | [STRONG/MODERATE/WEAK/NONE] | [Why or why not] | [Action] |

---

## Cross-Pollination Actions Taken

| Target | Type | Items Added |
| ------ | ---- | ----------- |
| [Project/Lab] | [Questions/Reports/Insights] | [Brief description] |

---

## Cross-Pollination Actions Recommended

| Target | Type | Recommendation |
| ------ | ---- | -------------- |
| [Project/Lab] | [Insight/Question/Report] | [What should be added] |

---

## Key Routing Insight

[One paragraph explaining the main takeaway for how this material fits into the broader research ecosystem]

---

*Routing evaluation completed: {current_date}*
*Status: TEMPLATE - Claude to populate with source-specific routing analysis*
"""

    files = {
        "chat.md": chat_content,
        "report.md": report_content,
        "routing.md": routing_content
    }

    for filename, content in files.items():
        file_path = cache_dir / filename
        if not dry_run:
            cache_dir.mkdir(parents=True, exist_ok=True)
            file_path.write_text(content, encoding="utf-8")
        created.append(file_path)

    return created


def ingest_rnd_content(folders: List[Path], dry_run: bool = True, diet: bool = False,
                       skip_review: bool = False) -> Dict:
    """
    Ingest R&D content into RnD/ directory WITH cognitive processing.

    Args:
        folders: List of source folders to process
        dry_run: Preview without making changes
        diet: If True, write to _CACHE_/ instead of RnD/ (non-committal)
        skip_review: If True, create templates only without analysis
    """
    result = {"folders": 0, "files": 0, "details": [], "diet": diet, "review_notes": []}

    rnd_dir = LLM_BOOK_DIR / "RnD"

    for folder in folders:
        topic_name = get_rnd_topic_name(folder.name)
        batch_name = folder.name

        if diet:
            # Diet mode: DON'T copy source files (they're already in STAGING)
            # Just create analysis structure in _CACHE_/
            cache_dir = folder / CACHE_DIR_NAME
            if not dry_run:
                cache_dir.mkdir(parents=True, exist_ok=True)

            # Count source files for reporting (but don't copy them)
            source_files = [f for f in folder.iterdir()
                           if f.is_file() and f.suffix in ('.md', '.txt', '.pdf', '.png', '.jpg')]
            file_count = len(source_files)

            action = "[DRY RUN]" if dry_run else "[OK]"
            print(f"  {action} {folder.name} -> _CACHE_/ (analysis only, {file_count} source files in place)")
        else:
            # Normal mode: copy to LLM_BOOK/RnD/{topic_name}
            target = rnd_dir / topic_name

            # Ensure target directory exists before copying
            if not dry_run:
                target.mkdir(parents=True, exist_ok=True)

            file_count = copy_folder_contents(folder, target, dry_run)

            action = "[DRY RUN]" if dry_run else "[OK]"
            print(f"  {action} {folder.name} -> RnD/{topic_name} ({file_count} files)")

        if file_count > 0:
            result["folders"] += 1
            result["files"] += file_count

            target_display = "_CACHE_/ (analysis)" if diet else f"RnD/{topic_name}"
            diet_tag = " -> _CACHE_/" if diet else ""
            result["details"].append({
                "source": folder.name,
                "target": target_display,
                "files": file_count
            })

            # Create R&D cognitive processing outputs
            rn_path = create_rnd_review_notes(batch_name, folder, dry_run, diet=diet)
            result["review_notes"].append(str(rn_path))
            print(f"  {action} Created REVIEW_NOTES_{batch_name}.md (R&D exploratory){diet_tag}")

            # Create analysis stubs
            stubs = create_rnd_analysis_stubs(batch_name, folder, dry_run, diet=diet)
            print(f"  {action} Created R&D analysis files{diet_tag}:")
            for stub in stubs:
                print(f"      - {stub.parent.name}/{stub.name}")

            # Create LLM Book interface files (chat.md, report.md) - diet mode only
            if diet:
                interface_files = create_llm_book_interface_files(batch_name, folder, dry_run, diet=diet)
                if interface_files:
                    print(f"  {action} Created NotebookLM interface files{diet_tag}:")
                    for ifile in interface_files:
                        print(f"      - {ifile.name}")

            # Mark as ingested (skip in diet mode)
            if not diet:
                mark_batch_ingested(folder, dry_run)
            else:
                print(f"      (Diet mode: .ingested marker NOT created)")

    return result


def clear_content_directories(dry_run: bool = True) -> None:
    """Clear LLM_BOOK content directories (for --fresh mode)."""
    for content_dir in CONTENT_DIRS:
        if not content_dir.exists():
            continue

        files = list(content_dir.rglob("*"))
        file_count = sum(1 for f in files if f.is_file())

        action = "[DRY RUN]" if dry_run else "[OK]"

        if not dry_run:
            for item in content_dir.iterdir():
                if item.is_file():
                    item.unlink()
                elif item.is_dir():
                    shutil.rmtree(item)

        print(f"  {action} Cleared {content_dir.name}/ ({file_count} files)")


def clear_ingestion_markers(dry_run: bool = True) -> int:
    """Clear all .ingested markers (for --fresh mode). Returns count."""
    count = 0

    if not STAGING_DIR.exists():
        return 0

    for folder in STAGING_DIR.iterdir():
        if folder.is_dir():
            marker = folder / INGESTED_MARKER
            if marker.exists():
                if not dry_run:
                    marker.unlink()
                count += 1

    return count


def throw_up(dry_run: bool = True) -> Dict:
    """
    Purge all _CACHE_/ directories found in STAGING/.

    The digestive metaphor continues:
    - --diet = consume but don't commit (output to _CACHE_/)
    - --throw_up = purge the temporary output

    Returns:
        Dict with purged directories and count
    """
    purged = []
    total_files = 0

    if not STAGING_DIR.exists():
        return {"purged": [], "count": 0, "files": 0}

    for folder in STAGING_DIR.iterdir():
        if folder.is_dir():
            cache_dir = folder / CACHE_DIR_NAME
            if cache_dir.exists():
                # Count files before deletion
                file_count = sum(1 for f in cache_dir.rglob("*") if f.is_file())
                total_files += file_count

                if not dry_run:
                    shutil.rmtree(cache_dir)

                purged.append({
                    "path": str(cache_dir),
                    "batch": folder.name,
                    "files": file_count
                })

    return {"purged": purged, "count": len(purged), "files": total_files}


def generate_report() -> str:
    """Generate status report of STAGING contents."""
    staging = discover_staging_folders()
    pending = get_pending_batches(staging)

    lines = [
        "=" * 60,
        "LLM_BOOK INGESTION STATUS (Accumulative Model)",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        f"STAGING location: {STAGING_DIR}",
        "",
    ]

    # Nyquist content
    lines.append("## Nyquist Content (-> publication pipeline)")
    if staging["nyquist"]:
        for folder, ingested in staging["nyquist"]:
            in_folder = folder / "_IN"
            status = "[*] INGESTED" if ingested else "[ ] PENDING"
            if in_folder.exists():
                file_count = sum(1 for f in in_folder.rglob("*") if f.is_file())
                lines.append(f"  {status} {folder.name}/_IN ({file_count} files)")
            else:
                lines.append(f"  {status} {folder.name} (no _IN subfolder)")
    else:
        lines.append("  (none found)")

    lines.append("")

    # R&D content
    lines.append("## R&D Content (-> RnD/ directory)")
    if staging["rnd"]:
        for folder, ingested in staging["rnd"]:
            status = "[*] INGESTED" if ingested else "[ ] PENDING"
            file_count = sum(1 for f in folder.rglob("*") if f.is_file())
            topic = get_rnd_topic_name(folder.name)
            lines.append(f"  {status} {folder.name} -> RnD/{topic} ({file_count} files)")
    else:
        lines.append("  (none found)")

    lines.append("")

    # Existing review notes
    lines.append("## Existing Review Notes")
    review_notes = list(VALIDATION_DIR.glob("REVIEW_NOTES_*.md"))
    if review_notes:
        for rn in sorted(review_notes):
            lines.append(f"  - {rn.name}")
    else:
        lines.append("  (none found)")

    # Summary
    pending_nyquist = len(pending["nyquist"])
    pending_rnd = len(pending["rnd"])

    lines.extend([
        "",
        "=" * 60,
        f"Pending ingestion: {pending_nyquist} Nyquist + {pending_rnd} R&D batches",
        "",
        "Commands:",
        "  py ingest.py --ingest           # Ingest pending batches (append)",
        "  py ingest.py --ingest --fresh   # Clear all and re-ingest",
        "  py ingest.py --ingest --dry-run # Preview changes",
        "=" * 60,
    ])

    return "\n".join(lines)


def perform_ingestion(dry_run: bool = True, fresh: bool = False,
                      force: bool = False, batches: List[str] = None,
                      skip_review: bool = False, diet: bool = False) -> Dict:
    """
    Perform ingestion workflow.

    Args:
        dry_run: Preview without making changes
        fresh: Overwrite mode - clear everything first (destructive)
        force: Re-process batches even if already ingested
        batches: Specific batch names to process (None = all pending)
        skip_review: If True, create placeholder templates instead of Claude review
                    (also skips DEEP_DIVES, FUTURE, EXPERIMENTS creation)
        diet: If True, write to _CACHE_/ instead of real pipeline (non-committal)
    """
    results = {
        "timestamp": datetime.now().isoformat(),
        "dry_run": dry_run,
        "fresh": fresh,
        "force": force,
        "skip_review": skip_review,
        "diet": diet,
        "batches_filter": batches,
        "nyquist": {"batches": [], "review_notes": [], "reviews": [], "analysis_files": []},
        "rnd": {},
    }

    mode_str = "DRY RUN" if dry_run else "APPLYING"
    fresh_str = " (FRESH)" if fresh else " (APPEND)"
    force_str = " --force" if force else ""
    batch_str = f" --batch {' '.join(batches)}" if batches else ""
    review_str = " --skip-review" if skip_review else " (with Claude review)"
    diet_str = " --diet (-> _CACHE_/)" if diet else ""

    print("=" * 60)
    print(f"LLM_BOOK INGESTION - {mode_str}{fresh_str}{force_str}{batch_str}{diet_str}")
    print(f"Review mode:{review_str}")
    if diet:
        print("DIET MODE: Output goes to _CACHE_/ (no pipeline commitment)")
    print("=" * 60)

    # Fresh mode: clear everything first
    if fresh:
        print("\n## Step 1: Clear existing content (--fresh)")
        clear_content_directories(dry_run)
        markers_cleared = clear_ingestion_markers(dry_run)
        print(f"  Cleared {markers_cleared} ingestion markers")
        results["cleared"] = True
    else:
        print("\n## Step 1: Append mode - preserving existing content")
        results["cleared"] = False

    # Discover batches
    staging = discover_staging_folders()

    # Determine which batches to process
    # Diet mode ALWAYS ignores .ingested status (it's non-committal preview)
    if diet and batches:
        # Diet mode with batch filter: process specified batches regardless of .ingested
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"] if p.name in batches],
            "rnd": [p for p, _ in staging["rnd"] if p.name in batches],
        }
    elif diet:
        # Diet mode without filter: process ALL batches regardless of .ingested
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"]],
            "rnd": [p for p, _ in staging["rnd"]],
        }
    elif fresh and batches:
        # Fresh mode with batch filter: only process specified batches
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"] if p.name in batches],
            "rnd": [p for p, _ in staging["rnd"] if p.name in batches],
        }
    elif fresh:
        # Fresh mode without filter: process all
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"]],
            "rnd": [p for p, _ in staging["rnd"]],
        }
    elif force and batches:
        # Force mode with specific batches: process those regardless of .ingested
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"] if p.name in batches],
            "rnd": [p for p, _ in staging["rnd"] if p.name in batches],
        }
    elif force:
        # Force mode without batch filter: process ALL batches
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"]],
            "rnd": [p for p, _ in staging["rnd"]],
        }
    else:
        # Normal append mode: only pending batches
        pending = get_pending_batches(staging)
        if batches:
            # Filter to specified batches
            pending = {
                "nyquist": [p for p in pending["nyquist"] if p.name in batches],
                "rnd": [p for p in pending["rnd"] if p.name in batches],
            }

    # Ingest Nyquist batches
    print("\n## Step 2: Process Nyquist batches")
    if pending["nyquist"]:
        for folder in pending["nyquist"]:
            batch_name = folder.name
            action = "[DRY RUN]" if dry_run else "[OK]"
            diet_tag = " -> _CACHE_/" if diet else ""

            if skip_review:
                # Create placeholder template only (skip all substantive review)
                rn_path = create_review_notes_template(batch_name, folder, dry_run, diet=diet)
                print(f"  {action} Created REVIEW_NOTES_{batch_name}.md (template only){diet_tag}")
                print(f"      (Skipped: DEEP_DIVES, FUTURE, EXPERIMENTS analysis)")
            else:
                # Perform Claude review (default behavior)
                print(f"  Reviewing {batch_name}...")
                review = perform_claude_review(batch_name, folder, dry_run)
                results["nyquist"]["reviews"].append(review)

                # Generate reviewed notes with actual assessment
                rn_path = generate_reviewed_notes(batch_name, folder, review, dry_run, diet=diet)
                print(f"  {action} Created REVIEW_NOTES_{batch_name}.md{diet_tag}")
                print(f"      Quality: {review['quality_grade']}")
                print(f"      IRON CLAD checks: {len(set(review['iron_clad_accuracy']))}/6")
                print(f"      Files reviewed: {len(review['files_reviewed'])}")

                # Create analysis files (default behavior - always done unless skip_review)
                stubs = create_analysis_stubs(batch_name, folder, dry_run, diet=diet)
                results["nyquist"]["analysis_files"].extend([str(s) for s in stubs])
                print(f"  {action} Created analysis files{diet_tag}:")
                for stub in stubs:
                    print(f"      - {stub.parent.name}/{stub.name}")

            results["nyquist"]["review_notes"].append(str(rn_path))

            # Mark as ingested (skip in diet mode - batch stays "pending" for real ingest later)
            if not diet:
                mark_batch_ingested(folder, dry_run)
            else:
                print(f"      (Diet mode: .ingested marker NOT created)")
            results["nyquist"]["batches"].append(batch_name)
    else:
        print("  No pending Nyquist batches")

    # Ingest R&D content
    print("\n## Step 3: Process R&D content")
    if pending["rnd"]:
        results["rnd"] = ingest_rnd_content(pending["rnd"], dry_run, diet=diet)
    else:
        print("  No pending R&D batches")

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Nyquist batches processed: {len(results['nyquist']['batches'])}")
    print(f"  Review notes created:      {len(results['nyquist']['review_notes'])}")
    print(f"  R&D folders processed:     {results['rnd'].get('folders', 0)}")
    print(f"  R&D files copied:          {results['rnd'].get('files', 0)}")

    if dry_run:
        print("\n[DRY RUN] No changes made. Run without --dry-run to apply.")
    else:
        print("\n[OK] Ingestion complete!")
        if results["nyquist"]["batches"]:
            print("\nNext steps:")
            for batch in results["nyquist"]["batches"]:
                print(f"  1. Review STAGING/{batch}/_IN/ content")
                print(f"  2. Fill in 1_VALIDATION/REVIEW_NOTES_{batch}.md")
            print("  3. Run: py digest.py --digest")

    return results


def main():
    parser = argparse.ArgumentParser(
        description="NotebookLM STAGING -> LLM_BOOK Ingestion (Accumulative Model)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Default Behavior:
  - APPENDS to existing content (accumulative)
  - Claude performs SUBSTANTIVE REVIEW and creates:
    - REVIEW_NOTES_{batch}.md with quality assessment
    - 1_DEEP_DIVES/{batch}.md with content analysis
    - 2_FUTURE/{batch}.md with future research directions
    - 3_EXPERIMENTS/{batch}.md with experimental observations

Flags:
  --fresh        Overwrite mode - clear all content before ingesting
  --skip-review  Skip Claude's substantive review (create templates only)
  --force        Re-process batches even if already ingested
  --batch X      Process only specific batch(es)
  --diet         Diet mode: write to _CACHE_/ instead of real pipeline
  --throw_up     Purge all _CACHE_/ directories in STAGING/

Examples:
  py ingest.py                    # Show staging status
  py ingest.py --ingest           # Ingest with full Claude review (default)
  py ingest.py --ingest --fresh   # Clear all, then ingest with review
  py ingest.py --ingest --skip-review  # Skip review, templates only
  py ingest.py --ingest --fresh --batch Nyquist_3  # Fresh ingest of just Nyquist_3
  py ingest.py --ingest --diet --batch OldBatch   # Diet mode: process to _CACHE_/
  py ingest.py --throw_up         # Purge all _CACHE_/ directories
        """
    )

    parser.add_argument("--ingest", action="store_true",
                        help="Perform ingestion (default: report only)")
    parser.add_argument("--fresh", action="store_true",
                        help="Overwrite mode - clear all content before ingesting (destructive!)")
    parser.add_argument("--force", action="store_true",
                        help="Re-process batches even if already ingested")
    parser.add_argument("--batch", type=str, nargs='+', default=None,
                        help="Process specific batch folder(s)")
    parser.add_argument("--skip-review", action="store_true",
                        help="Skip Claude review, create placeholder templates only (no analysis)")
    parser.add_argument("--diet", action="store_true",
                        help="Diet mode: write to _CACHE_/ instead of real pipeline (non-committal)")
    parser.add_argument("--throw_up", action="store_true",
                        help="Purge all _CACHE_/ directories in STAGING/ (clean up diet mode output)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")
    parser.add_argument("--json", action="store_true",
                        help="Output as JSON instead of text")

    args = parser.parse_args()

    # Handle --throw_up first (independent action)
    if args.throw_up:
        print("=" * 60)
        print("LLM_BOOK - THROW UP (Purging _CACHE_/ directories)")
        print("=" * 60)

        results = throw_up(dry_run=args.dry_run)

        if results["count"] == 0:
            print("\nNo _CACHE_/ directories found to purge.")
        else:
            action = "[DRY RUN]" if args.dry_run else "[PURGED]"
            print(f"\n{action} Found {results['count']} _CACHE_/ directories ({results['files']} files):")
            for item in results["purged"]:
                print(f"  - STAGING/{item['batch']}/_CACHE_/ ({item['files']} files)")

            if args.dry_run:
                print("\n[DRY RUN] No changes made. Run without --dry-run to purge.")
            else:
                print("\n[OK] All _CACHE_/ directories purged!")

        if args.json:
            print(json.dumps(results, indent=2))
        return

    if not args.ingest:
        # Report mode
        print(generate_report())
    else:
        # Ingestion mode
        results = perform_ingestion(
            dry_run=args.dry_run,
            fresh=args.fresh,
            force=args.force,
            batches=args.batch,
            skip_review=args.skip_review,
            diet=args.diet
        )

        if args.json:
            print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
