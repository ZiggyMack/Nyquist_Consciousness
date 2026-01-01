#!/usr/bin/env python3
"""
0_chew.py - Unified LLM Book Pipeline Entry Point
==================================================

The "mastication" stage - everything starts with chewing.
Orchestrates the full digestive pipeline:
  0_chew.py -> 1_ingest.py -> 2_digest.py

USAGE:
------
py 0_chew.py BATCH                    # Default: ingest + digest (append)
py 0_chew.py BATCH --new              # Fresh: clear + ingest + digest
py 0_chew.py BATCH --diet             # Diet: process to _CACHE_/ only
py 0_chew.py --baka "Project Name"    # Create research project
py 0_chew.py --promote BATCH          # Promote to Consciousness/
py 0_chew.py --reset                  # Purge _CACHE_/ directories
py 0_chew.py --status                 # Show pipeline status
py 0_chew.py --route TOPIC            # Show routing info
py 0_chew.py --labs                   # List Pan Handler labs

Author: LLM_BOOK Pipeline
Version: 3.0 (2025-12-31) - Unified entry point architecture
"""

import argparse
import json
import re
import shutil
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional

# === PATH CONSTANTS ===
SCRIPT_DIR = Path(__file__).parent
DEFAULT_STAGING_DIR = SCRIPT_DIR / "STAGING"
LLM_BOOK_DIR = SCRIPT_DIR.parent  # REPO-SYNC/LLM_BOOK/
REPO_SYNC_DIR = LLM_BOOK_DIR.parent  # REPO-SYNC/
REPO_ROOT = REPO_SYNC_DIR.parent  # d:\Documents\Nyquist_Consciousness
CONSCIOUSNESS_DIR = REPO_ROOT / "Consciousness"
LLM_BOOK_DISTILL = CONSCIOUSNESS_DIR / "RIGHT" / "distillations" / "llm_book"

# Pan Handlers paths
PAN_HANDLERS_DIR = REPO_SYNC_DIR / "PAN_HANDLERS"
MODULES_DIR = PAN_HANDLERS_DIR / "0_Config" / "modules"
MAPS_DIR = PAN_HANDLERS_DIR / "1_Maps"

# Publication categories in LLM_BOOK
PUBLICATIONS_DIR = LLM_BOOK_DIR / "2_PUBLICATIONS"


# =============================================================================
# PIPELINE ORCHESTRATION
# =============================================================================

def is_nyquist_content(folder_name: str) -> bool:
    """Determine if a staging folder contains Nyquist-specific content."""
    nyquist_keywords = ["nyquist", "infinity-nyquist", "white-paper"]
    return any(kw in folder_name.lower() for kw in nyquist_keywords)


def run_pipeline(batch_name: str, mode: str = "default", dry_run: bool = False) -> Dict:
    """
    Execute the full pipeline for a batch.

    Args:
        batch_name: Name of batch folder in STAGING/
        mode: "default" (append), "new" (fresh), or "diet" (_CACHE_/)
        dry_run: Preview without making changes

    Returns:
        Dict with ingest and digest results
    """
    # Import here to avoid circular imports
    try:
        # Try importing as module (when called from same directory)
        import importlib.util
        ingest_spec = importlib.util.spec_from_file_location("ingest", SCRIPT_DIR / "1_ingest.py")
        ingest_module = importlib.util.module_from_spec(ingest_spec)
        ingest_spec.loader.exec_module(ingest_module)

        digest_spec = importlib.util.spec_from_file_location("digest", SCRIPT_DIR / "2_digest.py")
        digest_module = importlib.util.module_from_spec(digest_spec)
        digest_spec.loader.exec_module(digest_module)
    except Exception as e:
        print(f"ERROR: Could not import pipeline modules: {e}")
        return {"error": str(e)}

    content_type = "NYQUIST" if is_nyquist_content(batch_name) else "R&D"

    print("=" * 60)
    print(f"CHEWING: {batch_name}")
    print(f"Content Type: {content_type}")
    print(f"Mode: {mode.upper()}")
    print("=" * 60)

    result = {"batch": batch_name, "mode": mode, "content_type": content_type}

    # Step 1: Ingest
    print("\n## Step 1: INGEST")
    print("-" * 40)

    fresh = (mode == "new")
    diet = (mode == "diet")

    ingest_result = ingest_module.perform_ingestion(
        dry_run=dry_run,
        fresh=fresh,
        force=False,
        batches=[batch_name],
        skip_review=False,
        diet=diet
    )
    result["ingest"] = ingest_result

    # Step 2: Digest (skip in diet mode)
    if mode != "diet":
        print("\n## Step 2: DIGEST")
        print("-" * 40)

        digest_result = digest_module.perform_digestion(
            dry_run=dry_run,
            batch_name=batch_name
        )
        result["digest"] = digest_result
    else:
        print("\n## Step 2: DIGEST (SKIPPED - diet mode)")
        print("  Content remains in _CACHE_/ for review")
        result["digest"] = None

        # Step 3: Trigger Claude analysis for diet mode
        print("\n## Step 3: CLAUDE ANALYSIS")
        print("-" * 40)

        # Build the analysis prompt
        staging_path = DEFAULT_STAGING_DIR / batch_name
        cache_path = staging_path / "_CACHE_"

        if cache_path.exists():
            # Find source files to analyze
            source_files = []
            for ext in ["*.md", "*.txt", "*.pdf"]:
                source_files.extend(staging_path.glob(ext))
            # Also check _IN folder
            in_folder = staging_path / "_IN"
            if in_folder.exists():
                for ext in ["*.md", "*.txt", "*.pdf"]:
                    source_files.extend(in_folder.glob(ext))

            # Find analysis files to populate
            analysis_files = list(cache_path.rglob("*.md"))

            print(f"\n  Source files to analyze: {len(source_files)}")
            for f in source_files[:5]:  # Show first 5
                print(f"    - {f.name}")
            if len(source_files) > 5:
                print(f"    ... and {len(source_files) - 5} more")

            print(f"\n  Analysis files to populate: {len(analysis_files)}")
            for f in analysis_files:
                print(f"    - {f.relative_to(cache_path)}")

            # Output the Claude instruction block
            print("\n" + "=" * 60)
            print("CLAUDE: ANALYZE AND POPULATE")
            print("=" * 60)
            print(f"""
<CLAUDE_ANALYSIS_REQUEST>
BATCH: {batch_name}
CACHE: {cache_path}

INSTRUCTIONS:
1. Read all source files in STAGING/{batch_name}/
2. For each analysis file in _CACHE_/, replace placeholder text with actual insights
3. Focus on:
   - INSIGHTS: Novel ideas, surprising findings, patterns
   - CONNECTIONS: Links to other research, Pan Handler labs
   - EXPERIMENTS: Testable hypotheses, proposed experiments
   - REVIEW_NOTES: Quality assessment, key themes, routing suggestions

SOURCE FILES:
{chr(10).join(f'  - {f}' for f in source_files)}

ANALYSIS FILES TO POPULATE:
{chr(10).join(f'  - {f}' for f in analysis_files)}

After analysis, the user can:
  - Review _CACHE_/ contents
  - Run normal chew to commit: py 0_chew.py {batch_name}
  - Or discard: py 0_chew.py --reset
</CLAUDE_ANALYSIS_REQUEST>
""")
            result["claude_analysis_triggered"] = True
            result["source_files"] = [str(f) for f in source_files]
            result["analysis_files"] = [str(f) for f in analysis_files]

    # Summary
    print("\n" + "=" * 60)
    print("CHEWING COMPLETE")
    print("=" * 60)
    if dry_run:
        print("[DRY RUN] No changes made. Run without --dry-run to apply.")

    return result


def reset_caches(dry_run: bool = False) -> Dict:
    """Purge all _CACHE_/ directories (throw_up wrapper)."""
    try:
        import importlib.util
        ingest_spec = importlib.util.spec_from_file_location("ingest", SCRIPT_DIR / "1_ingest.py")
        ingest_module = importlib.util.module_from_spec(ingest_spec)
        ingest_spec.loader.exec_module(ingest_module)

        return ingest_module.throw_up(dry_run=dry_run)
    except Exception as e:
        print(f"ERROR: Could not import ingest module: {e}")
        return {"error": str(e)}


# =============================================================================
# PROJECT MANAGEMENT (--baka)
# =============================================================================

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


def create_research_project(name: str, dry_run: bool = False) -> List[Path]:
    """
    Create a new research project directory structure.
    Always uses R&D exploratory structure (not IRON CLAD constrained).
    """
    staging_dir = DEFAULT_STAGING_DIR
    num = get_next_project_number([staging_dir])
    safe_name = name.replace(" ", "_").replace("-", "_")
    folder_name = f"New_{num}_{safe_name}"

    action = "[DRY RUN]" if dry_run else "[OK]"
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
**Type:** R&D Exploration (open-ended)

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

## Pan Handler Routing

Use `py 0_chew.py --route {safe_name}` to see where insights should go.

---

*Created by 0_chew.py --baka on {datetime.now().strftime('%Y-%m-%d')}*
"""
        (project_dir / "README.md").write_text(readme_content, encoding="utf-8")

        # Create template files in _OUT/
        research_q = f"""# Research Question: {name}

## Core Hypothesis

[What are we trying to prove or disprove?]

## Specific Questions for NotebookLM

1. **Exploration**
   - [What are we trying to understand?]
   - [What connections might exist?]

2. **Novel Directions**
   - [What hasn't been tried before?]
   - [What adjacent fields might inform this?]

3. **Integration Potential**
   - [How might this connect to existing Pan Handler labs?]
   - [What synergies could emerge?]

---

## Questions to Ask NotebookLM

1.
2.
3.

---

*Template created by 0_chew.py --baka*
"""
        (project_dir / "_OUT" / "RESEARCH_QUESTION.md").write_text(research_q, encoding="utf-8")

        existing_evidence = """# Existing Evidence

## From Nyquist Framework (Context)

### Key Statistics (For Reference)
- Event Horizon: D=0.80 (cosine distance)
- Inherent Drift: ~93% (not probing-induced)
- p-value: 2.40e-23
- Experiments: 750 | Models: 25 | Providers: 5

### Relevant Prior Work

[Reference any existing research that informs this exploration]

---

## Cross-Domain Connections

[What other fields or Pan Handler labs might inform this research?]

---

## Gaps and Opportunities

[What don't we know that this research aims to explore?]

---

*Template created by 0_chew.py --baka*
"""
        (project_dir / "_OUT" / "EXISTING_EVIDENCE.md").write_text(existing_evidence, encoding="utf-8")

        constraints = """# Project Constraints

## Resources Available

- [ ] API access to models
- [ ] Embedding infrastructure
- [ ] Visualization tools
- [ ] Human subjects (if applicable)

## Open Questions

- What scope is realistic?
- What would success look like?
- How does this connect to Pan Handlers?

## Pan Handler Lab Connections

[Which labs might benefit from this research?]

---

*Template created by 0_chew.py --baka*
"""
        (project_dir / "_OUT" / "CONSTRAINTS.md").write_text(constraints, encoding="utf-8")

        print(f"  Created: {project_dir}")
        print(f"  Created: {project_dir / '_IN'}")
        print(f"  Created: {project_dir / '_OUT'}")
        print(f"  Created: README.md + templates")

    return [project_dir]


# =============================================================================
# PROMOTION (--promote)
# =============================================================================

def promote_to_consciousness(batch_name: str, dry_run: bool = False,
                             category: Optional[str] = None) -> Dict:
    """Promote validated content from LLM_BOOK to Consciousness/."""
    result = {
        "batch": batch_name,
        "promoted": [],
        "skipped": [],
        "errors": []
    }

    action = "[DRY RUN]" if dry_run else "[OK]"

    print(f"\n{action} Promoting content from batch: {batch_name}")

    if not PUBLICATIONS_DIR.exists():
        result["errors"].append(f"Publications directory not found: {PUBLICATIONS_DIR}")
        print(f"  ERROR: {PUBLICATIONS_DIR} does not exist")
        return result

    categories = ["academic", "education", "policy", "funding", "navigation"]

    for cat in categories:
        if category and cat != category:
            continue

        cat_dir = PUBLICATIONS_DIR / cat
        if not cat_dir.exists():
            continue

        for file in cat_dir.iterdir():
            if not file.is_file():
                continue

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
                result["skipped"].append({"file": file.name, "reason": "Already exists"})
                print(f"  SKIP: {file.name} (already exists)")
                continue

            if not dry_run:
                target_dir.mkdir(parents=True, exist_ok=True)
                shutil.copy2(file, target_file)

            result["promoted"].append({"source": str(file), "target": str(target_file)})
            print(f"  {action} {file.name} -> {target_subdir}/")

    print(f"\n  Promoted: {len(result['promoted'])} files")
    print(f"  Skipped: {len(result['skipped'])} files")

    return result


# =============================================================================
# ROUTING INTELLIGENCE (--route, --labs, --lab)
# =============================================================================

def load_routing_maps() -> Dict:
    """Load routing configuration from 1_Maps/."""
    result = {"research_to_labs": {}, "routing_rules": []}

    research_map = MAPS_DIR / "research_to_labs.json"
    routing_rules = MAPS_DIR / "llm_book_routing.json"

    if research_map.exists():
        with open(research_map, "r", encoding="utf-8") as f:
            data = json.load(f)
            result["research_to_labs"] = data.get("mappings", {})

    if routing_rules.exists():
        with open(routing_rules, "r", encoding="utf-8") as f:
            data = json.load(f)
            result["routing_rules"] = data.get("routing_rules", [])

    return result


def load_lab_config(lab_id: str) -> Optional[Dict]:
    """Load configuration for a specific lab."""
    lab_file = MODULES_DIR / f"{lab_id}.json"
    if lab_file.exists():
        with open(lab_file, "r", encoding="utf-8") as f:
            return json.load(f)
    return None


def get_all_labs() -> List[Dict]:
    """Get summary info for all Pan Handler labs."""
    labs = []
    if MODULES_DIR.exists():
        for f in sorted(MODULES_DIR.glob("*.json")):
            try:
                with open(f, "r", encoding="utf-8") as fp:
                    data = json.load(fp)
                    labs.append({
                        "id": f.stem,
                        "name": data.get("display_name", f.stem),
                        "status": data.get("status", "Unknown"),
                        "role": data.get("role", "")[:60] + "..." if len(data.get("role", "")) > 60 else data.get("role", "")
                    })
            except json.JSONDecodeError:
                pass
    return labs


def show_routing(batch_name: Optional[str] = None, show_all: bool = False):
    """Display routing information for a batch or all mappings."""
    maps = load_routing_maps()

    print("=" * 60)
    print("LLM BOOK ROUTING MAP")
    print("=" * 60)

    if batch_name:
        mapping = maps["research_to_labs"].get(batch_name)
        if mapping:
            print(f"\n## Routing for: {batch_name}")
            print("-" * 40)
            print(f"  Primary destinations: {', '.join(mapping['primary'])}")
            if mapping.get('secondary'):
                print(f"  Secondary: {', '.join(mapping['secondary'])}")
            print(f"  Rationale: {mapping['rationale']}")
        else:
            print(f"\n  No explicit routing for '{batch_name}'")
            print("  Checking pattern-based rules...")

            matches = []
            for rule in maps["routing_rules"]:
                pattern = rule.get("pattern", "")
                if re.search(pattern, batch_name, re.IGNORECASE):
                    matches.append(rule)

            if matches:
                print("\n  Pattern matches:")
                for m in matches:
                    print(f"    [{m['priority']}] {m['id']}: -> {', '.join(m['destinations'])}")
            else:
                print("  No pattern matches found.")

    elif show_all:
        print("\n## Explicit Topic -> Lab Mappings")
        print("-" * 40)
        for topic, mapping in sorted(maps["research_to_labs"].items()):
            primary = ', '.join(mapping['primary'])
            print(f"  {topic:25} -> {primary}")

        print("\n## Pattern-Based Routing Rules")
        print("-" * 40)
        for rule in maps["routing_rules"]:
            dests = ', '.join(rule['destinations'])
            print(f"  [{rule['priority']:6}] {rule['id']:20} -> {dests}")

    else:
        print("\nUsage:")
        print("  py 0_chew.py --route BATCH_NAME    # Show routing for specific batch")
        print("  py 0_chew.py --route --all         # Show all routing mappings")


def show_labs(lab_id: Optional[str] = None):
    """Display Pan Handler labs information."""
    print("=" * 60)
    print("PAN HANDLERS CIVILIZATION ENGINE")
    print("=" * 60)

    if lab_id:
        config = load_lab_config(lab_id)
        if config:
            print(f"\n## {config.get('display_name', lab_id)}")
            print("-" * 40)
            print(f"  Status: {config.get('status', 'Unknown')}")
            print(f"  Role: {config.get('role', 'N/A')}")

            if config.get('tags'):
                print(f"  Tags: {', '.join(config['tags'][:5])}")

            if config.get('projects'):
                print(f"\n  Projects ({len(config['projects'])}):")
                for p in config['projects'][:5]:
                    print(f"    - [{p.get('status', '?')}] {p.get('title', 'Untitled')}")

            maps = load_routing_maps()
            feeds = []
            for topic, mapping in maps["research_to_labs"].items():
                if lab_id in mapping.get('primary', []) or lab_id in mapping.get('secondary', []):
                    feeds.append(topic)
            if feeds:
                print(f"\n  Fed by R&D topics: {', '.join(feeds)}")
        else:
            print(f"\n  Lab '{lab_id}' not found.")
            print("  Available labs:")
            for lab in get_all_labs():
                print(f"    - {lab['id']}")
    else:
        labs = get_all_labs()
        print(f"\n## Active Labs ({len(labs)})")
        print("-" * 40)

        for lab in labs:
            status_icon = "[*]" if lab['status'] == "Active" else "[ ]"
            print(f"  {status_icon} {lab['id']:25} {lab['status']:12} {lab['name']}")

        print("\n  Use --lab <id> to see details for a specific lab")


# =============================================================================
# STATUS (--status)
# =============================================================================

def get_all_projects() -> List[Dict]:
    """Get information about all research projects and batches."""
    staging_dir = DEFAULT_STAGING_DIR
    projects = []

    if not staging_dir.exists():
        return projects

    for folder in sorted(staging_dir.iterdir()):
        if not folder.is_dir():
            continue

        if folder.name.startswith("New_"):
            # Research project
            in_folder = folder / "_IN"
            out_folder = folder / "_OUT"
            cache_folder = folder / "_CACHE_"

            in_count = len(list(in_folder.glob("*"))) if in_folder.exists() else 0
            out_count = len(list(out_folder.glob("*"))) if out_folder.exists() else 0
            has_cache = cache_folder.exists()

            parts = folder.name.split("_", 2)
            name = parts[2] if len(parts) > 2 else folder.name

            projects.append({
                "type": "research",
                "folder": folder.name,
                "name": name.replace("_", " "),
                "number": int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 0,
                "in_count": in_count,
                "out_count": out_count,
                "has_cache": has_cache,
                "path": folder
            })

        else:
            # Standard batch (Nyquist or R&D)
            in_folder = folder / "_IN"
            cache_folder = folder / "_CACHE_"
            ingested = (folder / ".ingested").exists()

            # Check for files in root or _IN
            if in_folder.exists():
                file_count = len(list(in_folder.glob("*")))
            else:
                file_count = len([f for f in folder.iterdir() if f.is_file() and not f.name.startswith(".")])

            has_cache = cache_folder.exists()
            is_nyquist = is_nyquist_content(folder.name)

            projects.append({
                "type": "nyquist" if is_nyquist else "rnd",
                "folder": folder.name,
                "name": folder.name,
                "file_count": file_count,
                "ingested": ingested,
                "has_cache": has_cache,
                "path": folder
            })

    return projects


def show_status():
    """Display comprehensive pipeline status."""
    projects = get_all_projects()

    print("=" * 60)
    print("LLM BOOK PIPELINE STATUS")
    print(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 60)

    # Research projects
    research = [p for p in projects if p["type"] == "research"]
    if research:
        print("\n## Research Projects (--baka)")
        print("-" * 40)
        for p in sorted(research, key=lambda x: x["number"]):
            cache_tag = " [CACHE]" if p.get("has_cache") else ""
            print(f"  [{p['number']}] {p['name']}{cache_tag}")
            print(f"      _OUT/: {p['out_count']} files (to NotebookLM)")
            print(f"      _IN/:  {p['in_count']} files (from NotebookLM)")
            print()
    else:
        print("\n## Research Projects (--baka)")
        print("  (none found)")

    # Nyquist batches
    nyquist = [p for p in projects if p["type"] == "nyquist"]
    if nyquist:
        print("\n## Nyquist Batches (IRON CLAD pipeline)")
        print("-" * 40)
        for p in nyquist:
            status = "[*] INGESTED" if p["ingested"] else "[ ] PENDING"
            cache_tag = " [CACHE]" if p.get("has_cache") else ""
            print(f"  {status} {p['name']} ({p['file_count']} files){cache_tag}")

    # R&D batches
    rnd = [p for p in projects if p["type"] == "rnd"]
    if rnd:
        print("\n## R&D Batches (Exploratory)")
        print("-" * 40)
        for p in rnd:
            status = "[*] INGESTED" if p["ingested"] else "[ ] PENDING"
            cache_tag = " [CACHE]" if p.get("has_cache") else ""
            print(f"  {status} {p['name']} ({p['file_count']} files){cache_tag}")

    # Commands
    print("\n" + "=" * 60)
    print("COMMANDS")
    print("=" * 60)
    print("  py 0_chew.py BATCH              # Ingest + digest (default)")
    print("  py 0_chew.py BATCH --new        # Fresh: clear + process")
    print("  py 0_chew.py BATCH --diet       # Diet: to _CACHE_/ only")
    print("  py 0_chew.py --baka \"Name\"      # Create research project")
    print("  py 0_chew.py --promote BATCH    # Promote to Consciousness/")
    print("  py 0_chew.py --reset            # Purge _CACHE_/ directories")
    print("  py 0_chew.py --route TOPIC      # Show routing for topic")
    print("  py 0_chew.py --labs             # List Pan Handler labs")


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Unified LLM Book Pipeline Entry Point",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py 0_chew.py Nyquist_3               # Ingest + digest Nyquist batch
  py 0_chew.py HOFFMAN                  # Ingest + digest R&D batch
  py 0_chew.py Nyquist_4 --new          # Fresh: clear + process
  py 0_chew.py HOFFMAN --diet           # Process to _CACHE_/ only

Project Management:
  py 0_chew.py --baka "EEG Study"       # Create research project
  py 0_chew.py --promote Nyquist_3      # Promote to Consciousness/
  py 0_chew.py --reset                  # Purge _CACHE_/ directories
  py 0_chew.py --status                 # Show full pipeline status

Routing Intelligence:
  py 0_chew.py --route HOFFMAN          # Where should HOFFMAN go?
  py 0_chew.py --route --all            # Full routing map
  py 0_chew.py --labs                   # List Pan Handler labs
  py 0_chew.py --lab cfa                # CFA lab details
        """
    )

    # Positional: batch name for pipeline processing
    parser.add_argument("batch", nargs="?", type=str,
                        help="Batch to process (default action: ingest + digest)")

    # Pipeline mode flags (mutually exclusive with each other)
    mode_group = parser.add_mutually_exclusive_group()
    mode_group.add_argument("--new", action="store_true",
                           help="Fresh mode: clear existing + ingest + digest")
    mode_group.add_argument("--diet", action="store_true",
                           help="Diet mode: process to _CACHE_/ only")

    # Project management flags
    parser.add_argument("--baka", type=str, metavar="NAME",
                       help="Create new research project (R&D exploratory)")
    parser.add_argument("--promote", type=str, metavar="BATCH",
                       help="Promote batch to Consciousness/")
    parser.add_argument("--reset", action="store_true",
                       help="Purge all _CACHE_/ directories")
    parser.add_argument("--status", action="store_true",
                       help="Show pipeline status")

    # Routing flags
    parser.add_argument("--route", type=str, nargs="?", const="", metavar="TOPIC",
                       help="Show routing for topic (use --all for full map)")
    parser.add_argument("--all", action="store_true",
                       help="Show all routing mappings (use with --route)")
    parser.add_argument("--labs", action="store_true",
                       help="List all Pan Handler labs")
    parser.add_argument("--lab", type=str, metavar="ID",
                       help="Show details for specific lab")

    # Common flags
    parser.add_argument("--dry-run", action="store_true",
                       help="Preview changes without applying")

    args = parser.parse_args()

    # Determine which action to take
    if args.reset:
        # --reset: Purge caches
        print("=" * 60)
        print("RESETTING: Purging all _CACHE_/ directories")
        print("=" * 60)
        reset_caches(dry_run=args.dry_run)

    elif args.baka:
        # --baka: Create research project
        create_research_project(args.baka, dry_run=args.dry_run)
        if args.dry_run:
            print("\n[DRY RUN] No changes made. Run without --dry-run to apply.")

    elif args.promote:
        # --promote: Promote to Consciousness
        promote_to_consciousness(args.promote, dry_run=args.dry_run)
        if args.dry_run:
            print("\n[DRY RUN] No changes made. Run without --dry-run to apply.")

    elif args.route is not None:
        # --route: Show routing
        batch_name = args.route if args.route else None
        show_routing(batch_name=batch_name, show_all=args.all)

    elif args.labs:
        # --labs: List labs
        show_labs()

    elif args.lab:
        # --lab ID: Show specific lab
        show_labs(lab_id=args.lab)

    elif args.status:
        # --status: Show status
        show_status()

    elif args.batch:
        # BATCH: Run pipeline
        mode = "new" if args.new else ("diet" if args.diet else "default")
        run_pipeline(args.batch, mode=mode, dry_run=args.dry_run)

    else:
        # No action: Show status
        show_status()


if __name__ == "__main__":
    main()
