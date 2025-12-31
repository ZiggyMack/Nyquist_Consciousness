#!/usr/bin/env python3
"""
explore.py - LLM Book Research Exploration Manager
===================================================

Primary function: Create research project directories for LLM Book exploration.
Secondary function: Promote validated content to Consciousness/ (requires explicit flag).

USAGE:
------
py explore.py "EEG Analog Study"           # Create New_X project (DEFAULT)
py explore.py --create "EEG Analog Study"  # Explicit create (same as above)
py explore.py --status                     # Show status of all projects
py explore.py --promote --batch Nyquist_3  # Promote to Consciousness/ (explicit only)

MULTI-STAGING SUPPORT:
----------------------
py explore.py "Project Name" --staging STAGING STAGING2  # Create in multiple locations

RESEARCH PROJECT STRUCTURE:
---------------------------
New_X_ProjectName/
    _IN/           # Content FROM NotebookLM (their responses)
    _OUT/          # Content TO NotebookLM (our questions/materials)
    README.md      # Project overview and status

Author: LLM_BOOK Research Pipeline
Version: 1.1 (2025-12-31) - Creation as default, multi-staging support
"""

import argparse
import shutil
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional


# === PATH CONSTANTS ===
SCRIPT_DIR = Path(__file__).parent
DEFAULT_STAGING_DIR = SCRIPT_DIR / "STAGING"
LLM_BOOK_DIR = SCRIPT_DIR.parent  # REPO-SYNC/LLM_BOOK/
REPO_ROOT = LLM_BOOK_DIR.parent.parent  # d:\Documents\Nyquist_Consciousness
CONSCIOUSNESS_DIR = REPO_ROOT / "Consciousness"
LLM_BOOK_DISTILL = CONSCIOUSNESS_DIR / "RIGHT" / "distillations" / "llm_book"

# Publication categories in LLM_BOOK
PUBLICATIONS_DIR = LLM_BOOK_DIR / "2_PUBLICATIONS"


def resolve_staging_dirs(staging_names: Optional[List[str]] = None) -> List[Path]:
    """
    Resolve staging directory names to paths.

    Args:
        staging_names: List of staging directory names (relative to SCRIPT_DIR)
                      If None, returns [DEFAULT_STAGING_DIR]

    Returns:
        List of resolved Path objects
    """
    if not staging_names:
        return [DEFAULT_STAGING_DIR]

    resolved = []
    for name in staging_names:
        # Try as relative to SCRIPT_DIR first
        candidate = SCRIPT_DIR / name
        if candidate.exists() or not Path(name).is_absolute():
            resolved.append(candidate)
        else:
            # Try as absolute path
            resolved.append(Path(name))

    return resolved


def get_next_project_number(staging_dirs: Optional[List[Path]] = None) -> int:
    """Find the next available New_X number across all staging directories."""
    if staging_dirs is None:
        staging_dirs = [DEFAULT_STAGING_DIR]

    numbers = []
    for staging_dir in staging_dirs:
        if not staging_dir.exists():
            continue

        for d in staging_dir.iterdir():
            if d.is_dir() and d.name.startswith("New_"):
                parts = d.name.split("_")
                if len(parts) >= 2 and parts[1].isdigit():
                    numbers.append(int(parts[1]))

    return max(numbers) + 1 if numbers else 1


def get_all_projects(staging_dirs: Optional[List[Path]] = None) -> List[Dict]:
    """Get information about all research projects across staging directories."""
    if staging_dirs is None:
        staging_dirs = [DEFAULT_STAGING_DIR]

    projects = []

    for staging_dir in staging_dirs:
        if not staging_dir.exists():
            continue

        for folder in sorted(staging_dir.iterdir()):
            if not folder.is_dir():
                continue

            if folder.name.startswith("New_"):
                # Research project
                in_folder = folder / "_IN"
                out_folder = folder / "_OUT"
                readme = folder / "README.md"

                in_count = len(list(in_folder.glob("*"))) if in_folder.exists() else 0
                out_count = len(list(out_folder.glob("*"))) if out_folder.exists() else 0

                # Extract project name from folder name
                parts = folder.name.split("_", 2)
                name = parts[2] if len(parts) > 2 else folder.name

                projects.append({
                    "type": "research",
                    "folder": folder.name,
                    "name": name.replace("_", " "),
                    "number": int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 0,
                    "in_count": in_count,
                    "out_count": out_count,
                    "has_readme": readme.exists(),
                    "staging_dir": staging_dir.name,
                    "path": folder
                })

            elif folder.name.startswith("Nyquist_"):
                # Standard batch
                in_folder = folder / "_IN"
                ingested = (folder / ".ingested").exists()

                file_count = len(list(in_folder.glob("*"))) if in_folder.exists() else 0

                projects.append({
                    "type": "batch",
                    "folder": folder.name,
                    "name": folder.name,
                    "file_count": file_count,
                    "ingested": ingested,
                    "staging_dir": staging_dir.name,
                    "path": folder
                })

    return projects


def create_research_project(name: str, staging_dirs: Optional[List[Path]] = None,
                             dry_run: bool = True) -> List[Path]:
    """
    Create a new research project directory structure.

    Args:
        name: Project name
        staging_dirs: List of staging directories to create in (default: [DEFAULT_STAGING_DIR])
        dry_run: Preview without creating

    Returns:
        List of created project directory paths
    """
    if staging_dirs is None:
        staging_dirs = [DEFAULT_STAGING_DIR]

    num = get_next_project_number(staging_dirs)
    safe_name = name.replace(" ", "_").replace("-", "_")
    folder_name = f"New_{num}_{safe_name}"

    action = "[DRY RUN]" if dry_run else "[OK]"
    created_dirs = []

    for staging_dir in staging_dirs:
        project_dir = staging_dir / folder_name

        print(f"\n{action} Creating research project: {folder_name}")
        print(f"  Location: {staging_dir}")

        if not dry_run:
            # Create directories
            (project_dir / "_IN").mkdir(parents=True, exist_ok=True)
            (project_dir / "_OUT").mkdir(parents=True, exist_ok=True)

            # Create README.md
            readme_content = f"""# Research Project: {name}

**Created:** {datetime.now().strftime('%Y-%m-%d')}
**Status:** ACTIVE
**Project ID:** New_{num}

---

## Research Question

[TO BE FILLED - What hypothesis are we testing?]

---

## _OUT/ Contents (Feed to NotebookLM)

Materials prepared FOR NotebookLM:

- [ ] `RESEARCH_QUESTION.md` - Core hypothesis and specific questions
- [ ] `EXISTING_EVIDENCE.md` - What we already know from prior experiments
- [ ] `CONSTRAINTS.md` - Resources, access, limitations

---

## _IN/ Contents (From NotebookLM)

Responses received FROM NotebookLM:

(Save responses here with format: YYYY-MM-DD_topic_response.md)

---

## Progress Log

| Date | Action | Notes |
|------|--------|-------|
| {datetime.now().strftime('%Y-%m-%d')} | Project created | Initial setup |

---

## Related Phase 2 Thrust

[Link to funding proposal section if applicable]

---

*Created by explore.py on {datetime.now().strftime('%Y-%m-%d')}*
"""
            (project_dir / "README.md").write_text(readme_content, encoding="utf-8")

            # Create template files in _OUT/
            research_q = f"""# Research Question: {name}

## Core Hypothesis

[What are we trying to prove or disprove?]

## Specific Questions for NotebookLM

1. **Methodology Design**
   - [What experimental approach should we use?]
   - [How do we operationalize the key variables?]

2. **Success Criteria**
   - [What would confirm the hypothesis?]
   - [What would disconfirm it?]

3. **Analysis Approach**
   - [Which statistical tests?]
   - [What confounds to control?]

---

## Questions to Ask NotebookLM

1.
2.
3.

---

*Template created by explore.py*
"""
            (project_dir / "_OUT" / "RESEARCH_QUESTION.md").write_text(research_q, encoding="utf-8")

            existing_evidence = """# Existing Evidence

## From Nyquist Framework (IRON CLAD)

### Key Statistics
- Event Horizon: D=0.80 (cosine distance)
- Inherent Drift: ~93% (not probing-induced)
- p-value: 2.40e-23
- Experiments: 750 | Models: 25 | Providers: 5

### Relevant Findings

[Reference specific findings from prior experiments that inform this research]

---

## Provider Fingerprints

| Provider | Recovery Mechanism | Relevant to This Study? |
|----------|-------------------|------------------------|
| Anthropic | Over-Authenticity | |
| OpenAI | Meta-Analyst | |
| Google | Hard Threshold (no recovery) | |
| DeepSeek | Axiological Anchoring | |
| Mistral | Epistemic Humility | |

---

## Gaps in Current Understanding

[What don't we know that this research aims to address?]

---

*Template created by explore.py*
"""
            (project_dir / "_OUT" / "EXISTING_EVIDENCE.md").write_text(existing_evidence, encoding="utf-8")

            constraints = """# Project Constraints

## Resources Available

- [ ] API access to models
- [ ] Embedding infrastructure
- [ ] Visualization tools
- [ ] Human subjects (if applicable)

## Limitations

-
-

## Timeline

| Phase | Target |
|-------|--------|
| Design | |
| Data Collection | |
| Analysis | |
| Write-up | |

## Budget Considerations

[If applicable]

---

*Template created by explore.py*
"""
            (project_dir / "_OUT" / "CONSTRAINTS.md").write_text(constraints, encoding="utf-8")

            print(f"  Created: {project_dir}")
            print(f"  Created: {project_dir / '_IN'}")
            print(f"  Created: {project_dir / '_OUT'}")
            print(f"  Created: {project_dir / 'README.md'}")
            print(f"  Created: {project_dir / '_OUT' / 'RESEARCH_QUESTION.md'}")
            print(f"  Created: {project_dir / '_OUT' / 'EXISTING_EVIDENCE.md'}")
            print(f"  Created: {project_dir / '_OUT' / 'CONSTRAINTS.md'}")

        created_dirs.append(project_dir)

    return created_dirs


def promote_to_consciousness(batch_name: str, dry_run: bool = True,
                             category: Optional[str] = None) -> Dict:
    """
    Promote validated content from LLM_BOOK to Consciousness/.

    Only content that passes HOLY_GRAIL criteria should be promoted.
    """
    result = {
        "batch": batch_name,
        "promoted": [],
        "skipped": [],
        "errors": []
    }

    action = "[DRY RUN]" if dry_run else "[OK]"

    print(f"\n{action} Promoting content from batch: {batch_name}")

    # Check if publications exist for this batch
    if not PUBLICATIONS_DIR.exists():
        result["errors"].append(f"Publications directory not found: {PUBLICATIONS_DIR}")
        print(f"  ERROR: {PUBLICATIONS_DIR} does not exist")
        return result

    # Find content to promote
    categories = ["academic", "education", "policy", "funding", "navigation"]

    for cat in categories:
        if category and cat != category:
            continue

        cat_dir = PUBLICATIONS_DIR / cat
        if not cat_dir.exists():
            continue

        # Look for files that might be from this batch
        for file in cat_dir.iterdir():
            if not file.is_file():
                continue

            # Determine target location in Consciousness/
            target_subdir = {
                "academic": "technical_reports",
                "education": "study_guides",
                "policy": "briefings",
                "funding": "proposals",
                "navigation": "meta"
            }.get(cat, "other")

            target_dir = LLM_BOOK_DISTILL / target_subdir
            target_file = target_dir / file.name

            if target_file.exists():
                result["skipped"].append({
                    "file": file.name,
                    "reason": "Already exists in Consciousness/"
                })
                print(f"  SKIP: {file.name} (already exists)")
                continue

            if not dry_run:
                target_dir.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, target_file)

            result["promoted"].append({
                "source": str(file),
                "target": str(target_file)
            })
            print(f"  {action} {file.name} -> {target_subdir}/")

    print(f"\n  Promoted: {len(result['promoted'])} files")
    print(f"  Skipped: {len(result['skipped'])} files")

    return result


def show_status(staging_dirs: Optional[List[Path]] = None):
    """Display status of all projects and batches."""
    projects = get_all_projects(staging_dirs)

    print("=" * 60)
    print("LLM_BOOK EXPLORATION STATUS")
    print(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 60)

    # Research projects
    research = [p for p in projects if p["type"] == "research"]
    if research:
        print("\n## Research Projects (New_X)")
        print("-" * 40)
        for p in sorted(research, key=lambda x: x["number"]):
            status = "ACTIVE" if p["out_count"] > 0 else "EMPTY"
            print(f"  [{p['number']}] {p['name']}")
            print(f"      _OUT/: {p['out_count']} files (to NotebookLM)")
            print(f"      _IN/:  {p['in_count']} files (from NotebookLM)")
            print(f"      Status: {status}")
            print()
    else:
        print("\n## Research Projects (New_X)")
        print("  (none found)")

    # Standard batches
    batches = [p for p in projects if p["type"] == "batch"]
    if batches:
        print("\n## Standard Batches (Nyquist_X)")
        print("-" * 40)
        for p in batches:
            status = "[*] INGESTED" if p["ingested"] else "[ ] PENDING"
            print(f"  {status} {p['name']} ({p['file_count']} files)")
    else:
        print("\n## Standard Batches (Nyquist_X)")
        print("  (none found)")

    # Summary
    print("\n" + "=" * 60)
    print("COMMANDS")
    print("=" * 60)
    print("  py explore.py --create \"Project Name\"   # Create new research project")
    print("  py explore.py --promote --batch X        # Promote to Consciousness/")
    print("  py explore.py --status                   # This view")


def main():
    parser = argparse.ArgumentParser(
        description="LLM Book Research Exploration Manager",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py explore.py "EEG Analog Study"           # Create new project (DEFAULT)
  py explore.py --create "EEG Analog Study"  # Explicit create (same)
  py explore.py --status                     # Show all projects
  py explore.py --promote --batch Nyquist_3  # Promote to Consciousness/ (explicit)
  py explore.py "Project" --staging STAGING STAGING2  # Multi-staging
        """
    )

    # Positional argument for project name (default action: create)
    parser.add_argument("name", nargs="?", type=str,
                        help="Project name to create (default action)")
    parser.add_argument("--create", type=str, metavar="NAME",
                        help="Create new research project (explicit)")
    parser.add_argument("--staging", type=str, nargs="+", metavar="DIR",
                        help="Staging directories to use (default: STAGING)")
    parser.add_argument("--promote", action="store_true",
                        help="Promote content to Consciousness/ (explicit only)")
    parser.add_argument("--batch", type=str,
                        help="Batch name for promotion")
    parser.add_argument("--category", type=str,
                        help="Category to promote (academic, education, policy, etc.)")
    parser.add_argument("--status", action="store_true",
                        help="Show detailed project status")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")

    args = parser.parse_args()

    # Resolve staging directories
    staging_dirs = resolve_staging_dirs(args.staging)

    # Determine project name (positional or --create)
    project_name = args.name or args.create

    if args.status:
        # Show status
        show_status(staging_dirs)

    elif args.promote:
        # Explicit promotion required
        if not args.batch:
            print("ERROR: --batch required for promotion")
            print("Usage: py explore.py --promote --batch Nyquist_3")
            return
        promote_to_consciousness(args.batch, dry_run=args.dry_run, category=args.category)
        if args.dry_run:
            print("\n[DRY RUN] No changes made. Run without --dry-run to apply.")

    elif project_name:
        # DEFAULT: Create research project
        create_research_project(project_name, staging_dirs=staging_dirs, dry_run=args.dry_run)
        if args.dry_run:
            print("\n[DRY RUN] No changes made. Run without --dry-run to apply.")

    else:
        # No action specified, show status
        show_status(staging_dirs)


if __name__ == "__main__":
    main()
