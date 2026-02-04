#!/usr/bin/env python3
"""
3_burp.py - Cross-Pollination Loop Closure (Synthesis Pass)
============================================================

The "burp" stage - bringing answers back to their origins.
Closes the cross-pollination loop by:
  1. Reading questions asked OUT from each project
  2. Checking if target projects have answers/insights that address them
  3. Generating Answer Reports showing loop closure status
  4. Identifying projects ready to move to BURP/ (action-ready)

DIGESTIVE WORKFLOW:
-------------------
STAGING/           -> Raw material waiting to be processed
    | chew (0_chew.py)
    v
STAGING/CHEWED/    -> Digested, questions asked outward
    | burp (3_burp.py)
    v
STAGING/CHEWED/BURP/  -> Answers received back, loop closed, ready for action

USAGE:
------
py 3_burp.py                    # Status report - show loop closure
py 3_burp.py --report           # Generate full Answer Reports
py 3_burp.py --project NAME     # Check specific project
py 3_burp.py --ready            # List projects ready for BURP/
py 3_burp.py --move NAME        # Move project to BURP/

Author: LLM_BOOK Pipeline
Version: 1.0 (2026-02-03) - Initial synthesis pass implementation
"""

import argparse
import json
import shutil
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple

# === PATH CONSTANTS ===
SCRIPT_DIR = Path(__file__).parent
STAGING_DIR = SCRIPT_DIR / "STAGING"
CHEWED_DIR = STAGING_DIR / "CHEWED"
BURP_DIR = CHEWED_DIR / "BURP"

# Registry path
REPO_SYNC_DIR = SCRIPT_DIR.parent.parent  # REPO-SYNC/
REGISTRY_PATH = REPO_SYNC_DIR / "PAN_HANDLERS" / "0_Config" / "root" / "llm_book_registry.json"

# Files that indicate answers exist
ANSWER_INDICATORS = [
    "INSIGHTS.md",
    "EXPERIMENTS.md",
    "REVIEW_NOTES*.md",
    "*_INSIGHTS.md",
    "*_synthesis.md"
]

# Minimum requirements for BURP readiness
BURP_THRESHOLD = 0.5  # At least 50% of outgoing questions addressed


# =============================================================================
# REGISTRY OPERATIONS
# =============================================================================

def load_registry() -> Dict:
    """Load the LLM Book registry with cross-pollination log."""
    if not REGISTRY_PATH.exists():
        print(f"WARNING: Registry not found at {REGISTRY_PATH}")
        return {"projects": [], "cross_pollination_log": []}

    with open(REGISTRY_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def get_project_by_id(registry: Dict, project_id: str) -> Optional[Dict]:
    """Find a project in the registry by ID."""
    for project in registry.get("projects", []):
        if project.get("id") == project_id:
            return project
    return None


def get_outgoing_questions(registry: Dict, project_id: str) -> List[Dict]:
    """Get all questions asked OUT from a project."""
    questions = []
    for entry in registry.get("cross_pollination_log", []):
        if entry.get("source") == project_id:
            questions.append({
                "date": entry.get("date"),
                "target": entry.get("target"),
                "type": entry.get("type"),
                "items": entry.get("items", [])
            })
    return questions


def get_incoming_questions(registry: Dict, project_id: str) -> List[Dict]:
    """Get all questions asked TO a project (that it needs to answer)."""
    questions = []
    for entry in registry.get("cross_pollination_log", []):
        if entry.get("target") == project_id:
            questions.append({
                "date": entry.get("date"),
                "source": entry.get("source"),
                "type": entry.get("type"),
                "items": entry.get("items", [])
            })
    return questions


# =============================================================================
# PROJECT DISCOVERY
# =============================================================================

def discover_chewed_projects() -> List[Dict]:
    """Find all projects in CHEWED/ directory."""
    projects = []

    if not CHEWED_DIR.exists():
        return projects

    for folder in CHEWED_DIR.iterdir():
        if not folder.is_dir():
            continue
        if folder.name == "BURP":  # Skip BURP subdirectory
            continue
        if folder.name.startswith("."):
            continue

        # Check for answer indicators
        has_insights = (folder / "INSIGHTS.md").exists() or any(folder.glob("*INSIGHTS*.md"))
        has_experiments = (folder / "EXPERIMENTS.md").exists() or any(folder.glob("*EXPERIMENTS*.md"))
        has_synthesis = any(folder.glob("*synthesis*.md"))

        projects.append({
            "id": folder.name,
            "path": folder,
            "has_insights": has_insights,
            "has_experiments": has_experiments,
            "has_synthesis": has_synthesis,
            "files": [f.name for f in folder.iterdir() if f.is_file()]
        })

    return sorted(projects, key=lambda x: x["id"])


def discover_burped_projects() -> List[str]:
    """Find all projects already in BURP/."""
    if not BURP_DIR.exists():
        return []

    return sorted([
        folder.name for folder in BURP_DIR.iterdir()
        if folder.is_dir() and not folder.name.startswith(".")
    ])


# =============================================================================
# LOOP CLOSURE ANALYSIS
# =============================================================================

def analyze_loop_closure(registry: Dict, project_id: str) -> Dict:
    """
    Analyze how well a project's outgoing questions have been answered.

    Returns:
        {
            "project_id": str,
            "outgoing_questions": int,
            "targets_with_answers": int,
            "closure_ratio": float,
            "details": [
                {
                    "target": str,
                    "questions": [...],
                    "target_has_insights": bool,
                    "likely_addressed": bool
                }
            ]
        }
    """
    outgoing = get_outgoing_questions(registry, project_id)

    if not outgoing:
        return {
            "project_id": project_id,
            "outgoing_questions": 0,
            "targets_with_answers": 0,
            "closure_ratio": 1.0,  # No questions = fully closed
            "details": [],
            "ready_for_burp": True
        }

    # Check each target project for answers
    details = []
    targets_with_answers = 0
    total_targets = 0

    # Group questions by target
    targets = {}
    for entry in outgoing:
        target = entry["target"]
        if target not in targets:
            targets[target] = []
        targets[target].extend(entry["items"])

    # Check each target
    chewed_projects = {p["id"]: p for p in discover_chewed_projects()}

    for target, questions in targets.items():
        total_targets += 1

        target_info = chewed_projects.get(target, None)
        target_has_insights = False
        likely_addressed = False

        if target_info:
            target_has_insights = target_info.get("has_insights", False) or target_info.get("has_experiments", False)
            # Consider addressed if target has insights/experiments
            likely_addressed = target_has_insights

        if likely_addressed:
            targets_with_answers += 1

        details.append({
            "target": target,
            "questions": questions,
            "question_count": len(questions),
            "target_has_insights": target_has_insights,
            "likely_addressed": likely_addressed
        })

    closure_ratio = targets_with_answers / total_targets if total_targets > 0 else 1.0

    return {
        "project_id": project_id,
        "outgoing_questions": sum(len(d["questions"]) for d in details),
        "targets_with_answers": targets_with_answers,
        "total_targets": total_targets,
        "closure_ratio": closure_ratio,
        "details": details,
        "ready_for_burp": closure_ratio >= BURP_THRESHOLD
    }


def analyze_incoming_needs(registry: Dict, project_id: str) -> Dict:
    """
    Analyze what questions THIS project needs to answer for others.

    Returns info about incoming questions and whether this project
    has content that addresses them.
    """
    incoming = get_incoming_questions(registry, project_id)

    if not incoming:
        return {
            "project_id": project_id,
            "incoming_questions": 0,
            "sources": [],
            "needs_attention": False
        }

    # Check if this project has answer content
    chewed_projects = {p["id"]: p for p in discover_chewed_projects()}
    this_project = chewed_projects.get(project_id, {})
    has_answer_content = this_project.get("has_insights", False) or this_project.get("has_experiments", False)

    sources = []
    for entry in incoming:
        sources.append({
            "source": entry["source"],
            "questions": entry["items"],
            "question_count": len(entry["items"])
        })

    return {
        "project_id": project_id,
        "incoming_questions": sum(len(s["questions"]) for s in sources),
        "sources": sources,
        "has_answer_content": has_answer_content,
        "needs_attention": not has_answer_content and len(incoming) > 0
    }


# =============================================================================
# REPORTING
# =============================================================================

def generate_status_report() -> str:
    """Generate overall loop closure status report."""
    registry = load_registry()
    chewed = discover_chewed_projects()
    burped = discover_burped_projects()

    lines = [
        "=" * 60,
        "BURP STATUS - Cross-Pollination Loop Closure",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        "## Directory Status",
        f"  CHEWED/: {len(chewed)} projects",
        f"  BURP/:   {len(burped)} projects (action-ready)",
        "",
    ]

    # Analyze each chewed project
    ready_projects = []
    pending_projects = []

    for project in chewed:
        analysis = analyze_loop_closure(registry, project["id"])

        if analysis["ready_for_burp"]:
            ready_projects.append((project, analysis))
        else:
            pending_projects.append((project, analysis))

    # Report ready projects
    lines.append("## Ready for BURP/ (Loop Closed)")
    lines.append("-" * 40)

    if ready_projects:
        for project, analysis in ready_projects:
            ratio = analysis["closure_ratio"]
            icon = "[*]" if ratio >= 0.8 else "[~]"
            lines.append(f"  {icon} {project['id']}")
            if analysis["outgoing_questions"] > 0:
                lines.append(f"      {analysis['targets_with_answers']}/{analysis['total_targets']} targets addressed ({ratio*100:.0f}%)")
            else:
                lines.append(f"      No outgoing questions")
    else:
        lines.append("  (none)")

    lines.append("")

    # Report pending projects
    lines.append("## Pending (Awaiting Answers)")
    lines.append("-" * 40)

    if pending_projects:
        for project, analysis in pending_projects:
            ratio = analysis["closure_ratio"]
            lines.append(f"  [ ] {project['id']}")
            lines.append(f"      {analysis['targets_with_answers']}/{analysis['total_targets']} targets addressed ({ratio*100:.0f}%)")

            # Show which targets need attention
            for detail in analysis["details"]:
                if not detail["likely_addressed"]:
                    lines.append(f"        -> {detail['target']}: {detail['question_count']} questions waiting")
    else:
        lines.append("  (none - all loops closed!)")

    lines.append("")

    # Report projects in BURP/
    if burped:
        lines.append("## In BURP/ (Action-Ready)")
        lines.append("-" * 40)
        for name in burped:
            lines.append(f"  [+] {name}")
        lines.append("")

    # Commands
    lines.extend([
        "=" * 60,
        "COMMANDS",
        "=" * 60,
        "  py 3_burp.py                     # This status report",
        "  py 3_burp.py --report            # Full Answer Reports",
        "  py 3_burp.py --project NAME      # Check specific project",
        "  py 3_burp.py --ready             # List BURP-ready projects",
        "  py 3_burp.py --move NAME         # Move project to BURP/",
    ])

    return "\n".join(lines)


def generate_project_report(project_id: str) -> str:
    """Generate detailed report for a specific project."""
    registry = load_registry()
    project_info = get_project_by_id(registry, project_id)

    lines = [
        "=" * 60,
        f"BURP REPORT: {project_id}",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
    ]

    if project_info:
        lines.append(f"Display Name: {project_info.get('display_name', project_id)}")
        lines.append(f"Status: {project_info.get('status', 'Unknown')}")
        lines.append(f"Phase: {project_info.get('phase', 'Unknown')}")
        lines.append("")

    # Outgoing analysis (questions WE asked)
    out_analysis = analyze_loop_closure(registry, project_id)

    lines.append("## Outgoing Questions (We Asked)")
    lines.append("-" * 40)

    if out_analysis["outgoing_questions"] == 0:
        lines.append("  No outgoing questions logged.")
    else:
        lines.append(f"  Total Questions: {out_analysis['outgoing_questions']}")
        lines.append(f"  Targets: {out_analysis['total_targets']}")
        lines.append(f"  Addressed: {out_analysis['targets_with_answers']} ({out_analysis['closure_ratio']*100:.0f}%)")
        lines.append("")

        for detail in out_analysis["details"]:
            status = "[OK]" if detail["likely_addressed"] else "[??]"
            lines.append(f"  {status} -> {detail['target']}")
            for q in detail["questions"]:
                lines.append(f"        {q}")

    lines.append("")

    # Incoming analysis (questions asked OF us)
    in_analysis = analyze_incoming_needs(registry, project_id)

    lines.append("## Incoming Questions (Asked of Us)")
    lines.append("-" * 40)

    if in_analysis["incoming_questions"] == 0:
        lines.append("  No projects are waiting on answers from us.")
    else:
        lines.append(f"  Total Questions: {in_analysis['incoming_questions']}")
        lines.append(f"  Has Answer Content: {'Yes' if in_analysis['has_answer_content'] else 'No'}")
        lines.append("")

        for source in in_analysis["sources"]:
            lines.append(f"  <- {source['source']}")
            for q in source["questions"]:
                lines.append(f"        {q}")

    lines.append("")

    # BURP readiness
    lines.append("## BURP Readiness")
    lines.append("-" * 40)

    ready = out_analysis["ready_for_burp"]
    if ready:
        lines.append(f"  [READY] This project can be moved to BURP/")
        lines.append(f"          Run: py 3_burp.py --move {project_id}")
    else:
        lines.append(f"  [PENDING] Waiting for more answers to come back")
        lines.append(f"            {out_analysis['targets_with_answers']}/{out_analysis['total_targets']} targets addressed")
        lines.append(f"            Need {BURP_THRESHOLD*100:.0f}% closure to be BURP-ready")

    return "\n".join(lines)


def generate_full_report() -> str:
    """Generate comprehensive Answer Report for all projects."""
    registry = load_registry()
    chewed = discover_chewed_projects()

    lines = [
        "=" * 60,
        "FULL BURP REPORT - All Projects",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
    ]

    for project in chewed:
        lines.append("")
        lines.append("=" * 60)
        lines.append(generate_project_report(project["id"]))

    return "\n".join(lines)


# =============================================================================
# PROJECT MOVEMENT
# =============================================================================

def move_to_burp(project_id: str, dry_run: bool = False) -> Dict:
    """Move a project from CHEWED/ to CHEWED/BURP/."""
    result = {
        "project_id": project_id,
        "success": False,
        "message": ""
    }

    source = CHEWED_DIR / project_id
    target = BURP_DIR / project_id

    if not source.exists():
        result["message"] = f"Project not found: {source}"
        return result

    if target.exists():
        result["message"] = f"Already in BURP/: {project_id}"
        return result

    # Check readiness
    registry = load_registry()
    analysis = analyze_loop_closure(registry, project_id)

    if not analysis["ready_for_burp"]:
        result["message"] = f"Not ready for BURP: {analysis['closure_ratio']*100:.0f}% closure (need {BURP_THRESHOLD*100:.0f}%)"
        return result

    action = "[DRY RUN]" if dry_run else "[OK]"

    if not dry_run:
        # Ensure BURP directory exists
        BURP_DIR.mkdir(parents=True, exist_ok=True)

        # Move the project
        shutil.move(str(source), str(target))

    print(f"{action} Moved {project_id} to BURP/")
    result["success"] = True
    result["message"] = f"Moved to {target}"

    return result


def list_ready_projects() -> List[str]:
    """List all projects ready for BURP/."""
    registry = load_registry()
    chewed = discover_chewed_projects()

    ready = []
    for project in chewed:
        analysis = analyze_loop_closure(registry, project["id"])
        if analysis["ready_for_burp"]:
            ready.append(project["id"])

    return ready


# =============================================================================
# MAIN
# =============================================================================

def safe_print(text: str):
    """Print text safely on Windows, replacing problematic Unicode characters."""
    try:
        print(text)
    except UnicodeEncodeError:
        # Fall back to ASCII-safe version
        print(text.encode('ascii', 'replace').decode('ascii'))


def main():
    parser = argparse.ArgumentParser(
        description="Cross-Pollination Loop Closure (Synthesis Pass)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Digestive Workflow:
  STAGING/            -> Raw material
  STAGING/CHEWED/     -> Digested, questions asked outward
  STAGING/CHEWED/BURP/ -> Answers received, ready for action

Examples:
  py 3_burp.py                      # Status report
  py 3_burp.py --report             # Full Answer Reports
  py 3_burp.py --project Frame_Theory  # Check specific project
  py 3_burp.py --ready              # List BURP-ready projects
  py 3_burp.py --move Frame_Theory  # Move to BURP/
        """
    )

    parser.add_argument("--report", action="store_true",
                        help="Generate full Answer Reports for all projects")
    parser.add_argument("--project", type=str, metavar="NAME",
                        help="Check specific project's loop closure status")
    parser.add_argument("--ready", action="store_true",
                        help="List all projects ready for BURP/")
    parser.add_argument("--move", type=str, metavar="NAME",
                        help="Move project to BURP/")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")

    args = parser.parse_args()

    if args.report:
        safe_print(generate_full_report())

    elif args.project:
        safe_print(generate_project_report(args.project))

    elif args.ready:
        ready = list_ready_projects()
        print("=" * 60)
        print("BURP-Ready Projects")
        print("=" * 60)
        if ready:
            for name in ready:
                print(f"  [*] {name}")
            print("")
            print("To move a project to BURP/:")
            print(f"  py 3_burp.py --move <project_name>")
        else:
            print("  (none ready - awaiting answers)")

    elif args.move:
        result = move_to_burp(args.move, dry_run=args.dry_run)
        if not result["success"]:
            print(f"ERROR: {result['message']}")
        elif args.dry_run:
            print("[DRY RUN] No changes made. Run without --dry-run to apply.")

    else:
        # Default: status report
        safe_print(generate_status_report())


if __name__ == "__main__":
    main()
