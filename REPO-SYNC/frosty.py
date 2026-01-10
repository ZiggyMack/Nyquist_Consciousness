"""
OPERATION FROSTY v2.0 - Cold-Boot Documentation & Navigation Automation
=======================================================================

Automates the process of keeping documentation fresh for cold-started Claude instances.
Now with breadcrumb validation, link checking, and navigation auditing.

USAGE:
    py REPO-SYNC/frosty.py                    # Full scan and report
    py REPO-SYNC/frosty.py --commits 10       # Check against last 10 commits
    py REPO-SYNC/frosty.py --dir S7_ARMADA    # Scan specific directory
    py REPO-SYNC/frosty.py --update-manifests # Refresh manifest timestamps

    # v2.0 NEW MODES:
    py REPO-SYNC/frosty.py --validate-links   # Check all markdown links resolve
    py REPO-SYNC/frosty.py --check-consistency # Verify key terms are consistent
    py REPO-SYNC/frosty.py --audit            # Full navigation audit
    py REPO-SYNC/frosty.py --plan-registry    # Scan and report plan file status
    py REPO-SYNC/frosty.py --session-health   # Check JSONL session files

PHILOSOPHY:
    Phase 0: Status updates (what's done, what's next)
    Phase 1: Context updates (structural changes, new patterns)
    Phase 2: Navigation health (can a fresh Claude find their way?)

    The real value is ensuring fresh Claudes can navigate effectively.

MANIFEST FORMAT (embedded in markdown files):
    <!-- FROSTY_MANIFEST
    last_reviewed: 2025-12-17
    depends_on:
      - ../1_CALIBRATION/lib/triple_dip.py
      - ../0_docs/specs/0_RUN_METHODOLOGY.md
    impacts:
      - ../14_CONSCIOUSNESS/README.md
    keywords:
      - exit_survey
      - triple_dip
    breadcrumbs_to:           # v2.0: Where this file points readers
      - docs/maps/MAP_OF_MAPS.md
    breadcrumbs_from:         # v2.0: What files should point here
      - README.md
    key_terms:                # v2.0: Terms that must be consistent
      - Event Horizon: 0.80
    -->

Author: Claude (Nyquist Framework)
Version: 2.0 (Claude Consolidation Era)
Date: January 10, 2026
"""

import os
import sys
import re
import argparse
import subprocess
import json
from datetime import datetime
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Set, Tuple
from collections import defaultdict

# =============================================================================
# CONFIGURATION
# =============================================================================

REPO_ROOT = Path(__file__).parent.parent

# Claude projects folder (Windows)
CLAUDE_PROJECTS = Path.home() / ".claude" / "projects"
CLAUDE_PLANS = Path.home() / ".claude" / "plans"

COLD_BOOT_PATTERNS = [
    "README.md",
    "START_HERE.md",
    "*_METHODOLOGY.md",
    "*_INTENTIONALITY.md",
    "*_MAP.md",
    "*_MATRIX.md",
    "I_AM_NYQUIST.md",
    "MASTER_GLOSSARY.md",
]

PRIORITY_DIRS = [
    "experiments/temporal_stability/S7_ARMADA",
    "Consciousness",
    "docs/maps",
    "personas/egregores",
]

# Key terms that must be consistent across all docs
KEY_TERMS = {
    "Event Horizon": ["0.80", "0.8"],  # Acceptable values
    "IRON CLAD": ["N=3", "N = 3"],
    "Inherent Drift": ["~93%", "93%", "92%"],  # Allow small variance in reporting
}

# How many commits back to check by default
DEFAULT_COMMIT_DEPTH = 5

# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class FrostyManifest:
    """Embedded manifest parsed from markdown files."""
    last_reviewed: Optional[datetime] = None
    depends_on: List[str] = field(default_factory=list)
    impacts: List[str] = field(default_factory=list)
    keywords: List[str] = field(default_factory=list)
    breadcrumbs_to: List[str] = field(default_factory=list)
    breadcrumbs_from: List[str] = field(default_factory=list)
    key_terms: Dict[str, str] = field(default_factory=dict)

@dataclass
class FlaggedFile:
    """A file flagged for documentation update."""
    path: Path
    priority: str  # HIGH, MEDIUM, LOW, NONE
    reasons: List[str] = field(default_factory=list)
    last_reviewed: Optional[datetime] = None
    commits_since: int = 0
    checklist: List[str] = field(default_factory=list)

@dataclass
class LinkValidation:
    """Result of validating a markdown link."""
    source_file: Path
    link_text: str
    link_target: str
    line_number: int
    valid: bool
    error: str = ""

@dataclass
class TermConsistency:
    """Result of checking term consistency."""
    term: str
    expected: List[str]
    found: Dict[str, List[Tuple[Path, int]]]  # value -> [(file, line), ...]
    consistent: bool

@dataclass
class PlanStatus:
    """Status of a plan file."""
    path: Path
    slug: str
    status: str  # IN PROGRESS, COMPLETE, BLOCKED, READY, UNKNOWN
    claude_session: str
    purpose: str
    last_modified: Optional[datetime] = None

@dataclass
class SessionHealth:
    """Health status of a Claude session JSONL file."""
    session_id: str
    path: Path
    lines: int
    size_mb: float
    has_errors: bool
    status: str  # HEALTHY, LARGE, CRASHED, UNKNOWN
    last_activity: Optional[datetime] = None

# =============================================================================
# GIT OPERATIONS
# =============================================================================

def get_recent_commits(n: int = 5) -> List[Dict]:
    """Get last N commit messages and changed files."""
    commits = []
    try:
        result = subprocess.run(
            ["git", "log", f"-{n}", "--format=%H|%s|%ai"],
            capture_output=True, text=True, cwd=REPO_ROOT
        )
        if result.returncode != 0:
            print(f"[WARNING] Git log failed: {result.stderr}")
            return commits

        for line in result.stdout.strip().split("\n"):
            if not line:
                continue
            parts = line.split("|", 2)
            if len(parts) >= 3:
                commit_hash, message, date_str = parts

                files_result = subprocess.run(
                    ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", commit_hash],
                    capture_output=True, text=True, cwd=REPO_ROOT
                )
                changed_files = files_result.stdout.strip().split("\n") if files_result.returncode == 0 else []

                commits.append({
                    "hash": commit_hash[:7],
                    "message": message,
                    "date": date_str,
                    "files": [f for f in changed_files if f]
                })
    except Exception as e:
        print(f"[ERROR] Failed to get commits: {e}")

    return commits

def get_file_last_modified(path: Path) -> Optional[datetime]:
    """Get last modified time of a file from git or filesystem."""
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%ai", "--", str(path)],
            capture_output=True, text=True, cwd=REPO_ROOT
        )
        if result.returncode == 0 and result.stdout.strip():
            date_str = result.stdout.strip()
            return datetime.strptime(date_str[:19], "%Y-%m-%d %H:%M:%S")
    except:
        pass

    try:
        return datetime.fromtimestamp(path.stat().st_mtime)
    except:
        return None

# =============================================================================
# MANIFEST PARSING
# =============================================================================

def parse_frosty_manifest(file_path: Path) -> Optional[FrostyManifest]:
    """Extract FROSTY_MANIFEST from markdown file."""
    try:
        content = file_path.read_text(encoding='utf-8', errors='replace')
    except:
        return None

    pattern = r'<!--\s*FROSTY_MANIFEST\s*(.*?)\s*-->'
    match = re.search(pattern, content, re.DOTALL | re.IGNORECASE)

    if not match:
        return None

    manifest = FrostyManifest()
    manifest_text = match.group(1)

    current_key = None
    current_list = []

    for line in manifest_text.split('\n'):
        line = line.strip()
        if not line:
            continue

        key_match = re.match(r'^(\w+):\s*(.*)$', line)
        if key_match:
            if current_key and current_list:
                if current_key == 'key_terms':
                    # Parse key_terms as dict
                    terms_dict = {}
                    for item in current_list:
                        if ':' in item:
                            k, v = item.split(':', 1)
                            terms_dict[k.strip()] = v.strip()
                    manifest.key_terms = terms_dict
                else:
                    setattr(manifest, current_key, current_list)
                current_list = []

            key = key_match.group(1)
            value = key_match.group(2).strip()

            if key == 'last_reviewed' and value:
                try:
                    manifest.last_reviewed = datetime.strptime(value, "%Y-%m-%d")
                except:
                    pass
            elif value:
                if key == 'key_terms':
                    current_key = key
                    if ':' in value:
                        k, v = value.split(':', 1)
                        current_list.append(f"{k.strip()}: {v.strip()}")
                else:
                    setattr(manifest, key, [value])
                    current_key = None
            else:
                current_key = key
        elif line.startswith('-'):
            item = line[1:].strip()
            current_list.append(item)

    if current_key and current_list:
        if current_key == 'key_terms':
            terms_dict = {}
            for item in current_list:
                if ':' in item:
                    k, v = item.split(':', 1)
                    terms_dict[k.strip()] = v.strip()
            manifest.key_terms = terms_dict
        else:
            setattr(manifest, current_key, current_list)

    return manifest

# =============================================================================
# FILE SCANNING
# =============================================================================

def scan_cold_boot_docs(root: Path, subdir: Optional[str] = None) -> List[Path]:
    """Find all README.md, START_HERE.md, etc."""
    search_root = root / subdir if subdir else root
    found = []

    for pattern in COLD_BOOT_PATTERNS:
        found.extend(search_root.rglob(pattern))

    exclusions = ['.git', '__pycache__', 'node_modules', 'venv', '.venv']
    filtered = [
        f for f in found
        if not any(ex in str(f) for ex in exclusions)
    ]

    return sorted(set(filtered))

def check_file_staleness(doc_path: Path, commits: List[Dict]) -> FlaggedFile:
    """Determine if a doc file needs updating based on changes."""
    flagged = FlaggedFile(path=doc_path, priority="NONE")

    manifest = parse_frosty_manifest(doc_path)
    if manifest:
        flagged.last_reviewed = manifest.last_reviewed

    doc_rel_path = doc_path.relative_to(REPO_ROOT)
    doc_modified_in_commits = 0

    for commit in commits:
        if str(doc_rel_path) in commit['files']:
            doc_modified_in_commits += 1

    if manifest and manifest.depends_on:
        for dep in manifest.depends_on:
            dep_path = str((doc_path.parent / dep).resolve())
            for commit in commits:
                for changed in commit['files']:
                    if dep in changed or changed.endswith(Path(dep).name):
                        flagged.reasons.append(f"Dependency changed: {Path(dep).name}")
                        flagged.commits_since += 1

    if manifest and manifest.keywords:
        for commit in commits:
            for keyword in manifest.keywords:
                if keyword.lower() in commit['message'].lower():
                    flagged.reasons.append(f"Commit mentions '{keyword}': {commit['hash']}")
                    flagged.commits_since += 1

    doc_dir = doc_path.parent
    for commit in commits:
        for changed in commit['files']:
            changed_path = REPO_ROOT / changed
            if changed_path.parent == doc_dir and changed_path != doc_path:
                if changed.endswith('.py') or changed.endswith('.md'):
                    flagged.reasons.append(f"Sibling changed: {Path(changed).name}")
                    flagged.commits_since += 1

    unique_reasons = list(set(flagged.reasons))
    flagged.reasons = unique_reasons

    if len(unique_reasons) >= 3:
        flagged.priority = "HIGH"
    elif len(unique_reasons) >= 1:
        flagged.priority = "MEDIUM"
    elif not manifest:
        flagged.priority = "LOW"
        flagged.reasons.append("No FROSTY_MANIFEST found")

    flagged.checklist = generate_checklist(doc_path, flagged.reasons)

    return flagged

def generate_checklist(doc_path: Path, reasons: List[str]) -> List[str]:
    """Generate context-aware update checklist for a file."""
    checklist = []
    name = doc_path.name.lower()

    if name == "readme.md":
        checklist = [
            "[ ] Update status section (what's completed, in-progress, planned)",
            "[ ] Verify cross-references to other docs still valid",
            "[ ] Check for outdated patterns or deprecated approaches",
            "[ ] Update 'Last Updated' timestamp in FROSTY_MANIFEST"
        ]
    elif name == "start_here.md":
        checklist = [
            "[ ] Verify operational instructions still accurate",
            "[ ] Check example commands work",
            "[ ] Update prerequisite list",
            "[ ] Update 'Last Updated' timestamp"
        ]
    elif "methodology" in name:
        checklist = [
            "[ ] Verify code examples match current implementation",
            "[ ] Check cross-references to spec files",
            "[ ] Update library locations (agnostic paths)",
            "[ ] Update lessons learned section"
        ]
    elif "map" in name or "matrix" in name:
        checklist = [
            "[ ] Verify counts/statistics still accurate",
            "[ ] Check for new entries needed",
            "[ ] Update cross-references"
        ]
    elif "i_am_nyquist" in name:
        checklist = [
            "[ ] Check VERSION HISTORY is current",
            "[ ] Verify CLAUDE CONSOLIDATION PROTOCOL is accurate",
            "[ ] Update session handoff template if needed",
            "[ ] Update LAST_UPDATE in header"
        ]
    else:
        checklist = [
            "[ ] Review for outdated information",
            "[ ] Update references if needed",
            "[ ] Update timestamp"
        ]

    return checklist

# =============================================================================
# v2.0: LINK VALIDATION
# =============================================================================

def extract_markdown_links(file_path: Path) -> List[Tuple[str, str, int]]:
    """Extract all markdown links from a file. Returns [(text, target, line_num), ...]"""
    links = []
    try:
        content = file_path.read_text(encoding='utf-8', errors='replace')
        lines = content.split('\n')

        # Pattern for [text](target)
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'

        for line_num, line in enumerate(lines, 1):
            for match in re.finditer(link_pattern, line):
                text = match.group(1)
                target = match.group(2)
                # Skip external links and anchors
                if not target.startswith('http') and not target.startswith('#'):
                    links.append((text, target, line_num))
    except:
        pass

    return links

def validate_link(source_file: Path, link_target: str) -> Tuple[bool, str]:
    """Check if a markdown link target exists."""
    # Handle anchor links within file
    if '#' in link_target:
        link_target = link_target.split('#')[0]
        if not link_target:  # Pure anchor link
            return True, ""

    # Resolve relative to source file's directory
    target_path = (source_file.parent / link_target).resolve()

    if target_path.exists():
        return True, ""

    # Try relative to repo root
    target_from_root = (REPO_ROOT / link_target).resolve()
    if target_from_root.exists():
        return True, ""

    return False, f"File not found: {link_target}"

def validate_all_links(root: Path) -> List[LinkValidation]:
    """Validate all markdown links in the repository."""
    results = []
    md_files = list(root.rglob("*.md"))

    exclusions = ['.git', '__pycache__', 'node_modules', 'venv', '.venv']
    md_files = [f for f in md_files if not any(ex in str(f) for ex in exclusions)]

    for md_file in md_files:
        links = extract_markdown_links(md_file)
        for text, target, line_num in links:
            valid, error = validate_link(md_file, target)
            results.append(LinkValidation(
                source_file=md_file,
                link_text=text,
                link_target=target,
                line_number=line_num,
                valid=valid,
                error=error
            ))

    return results

# =============================================================================
# v2.0: TERM CONSISTENCY
# =============================================================================

def check_term_consistency(root: Path) -> List[TermConsistency]:
    """Check that key terms are used consistently across all docs."""
    results = []
    md_files = list(root.rglob("*.md"))

    exclusions = ['.git', '__pycache__', 'node_modules', 'venv', '.venv']
    md_files = [f for f in md_files if not any(ex in str(f) for ex in exclusions)]

    for term, expected_values in KEY_TERMS.items():
        found = defaultdict(list)

        # Create pattern to find term with various values
        pattern = re.compile(
            rf'{re.escape(term)}[:\s=]+([0-9.%~N=\s]+)',
            re.IGNORECASE
        )

        for md_file in md_files:
            try:
                content = md_file.read_text(encoding='utf-8', errors='replace')
                lines = content.split('\n')

                for line_num, line in enumerate(lines, 1):
                    matches = pattern.findall(line)
                    for match in matches:
                        value = match.strip()
                        found[value].append((md_file, line_num))
            except:
                continue

        # Check consistency
        consistent = True
        for value in found.keys():
            if not any(exp in value for exp in expected_values):
                consistent = False
                break

        results.append(TermConsistency(
            term=term,
            expected=expected_values,
            found=dict(found),
            consistent=consistent
        ))

    return results

# =============================================================================
# v2.0: PLAN REGISTRY
# =============================================================================

def scan_plan_files() -> List[PlanStatus]:
    """Scan all plan files and extract their status."""
    plans = []

    if not CLAUDE_PLANS.exists():
        print(f"[WARNING] Plans directory not found: {CLAUDE_PLANS}")
        return plans

    for plan_file in CLAUDE_PLANS.glob("*.md"):
        try:
            content = plan_file.read_text(encoding='utf-8', errors='replace')

            # Extract status
            status_match = re.search(r'\*\*Status:\*\*\s*(\w+(?:\s+\w+)?)', content)
            status = status_match.group(1) if status_match else "UNKNOWN"

            # Extract Claude session
            session_match = re.search(r'\*\*Claude Session:\*\*\s*([^\n]+)', content)
            session = session_match.group(1).strip() if session_match else "Unknown"

            # Extract purpose (first paragraph after ## Purpose)
            purpose_match = re.search(r'##\s*Purpose\s*\n+([^\n#]+)', content)
            purpose = purpose_match.group(1).strip()[:100] if purpose_match else "No purpose found"

            plans.append(PlanStatus(
                path=plan_file,
                slug=plan_file.stem,
                status=status.upper(),
                claude_session=session,
                purpose=purpose,
                last_modified=get_file_last_modified(plan_file)
            ))
        except Exception as e:
            print(f"[WARNING] Could not parse {plan_file.name}: {e}")

    return plans

# =============================================================================
# v2.0: SESSION HEALTH
# =============================================================================

def check_session_health() -> List[SessionHealth]:
    """Check health of Claude session JSONL files."""
    sessions = []

    # Find project folder for this repo
    project_folder = None
    if CLAUDE_PROJECTS.exists():
        # Look for folder matching this repo
        for folder in CLAUDE_PROJECTS.iterdir():
            if folder.is_dir() and "Nyquist" in folder.name:
                project_folder = folder
                break

    if not project_folder:
        print(f"[WARNING] Could not find Claude project folder")
        return sessions

    for jsonl_file in project_folder.glob("*.jsonl"):
        try:
            size_bytes = jsonl_file.stat().st_size
            size_mb = size_bytes / (1024 * 1024)

            # Count lines (fast method)
            with open(jsonl_file, 'rb') as f:
                lines = sum(1 for _ in f)

            # Check for errors in last 50 lines
            has_errors = False
            last_activity = None
            try:
                with open(jsonl_file, 'r', encoding='utf-8', errors='replace') as f:
                    # Read last 50 lines
                    all_lines = f.readlines()
                    check_lines = all_lines[-50:] if len(all_lines) > 50 else all_lines

                    for line in check_lines:
                        if '413' in line or 'request_too_large' in line or 'error' in line.lower():
                            has_errors = True

                        # Try to get timestamp
                        try:
                            data = json.loads(line)
                            if 'timestamp' in data:
                                last_activity = datetime.fromisoformat(data['timestamp'].replace('Z', '+00:00'))
                        except:
                            pass
            except:
                pass

            # Determine status
            if has_errors:
                status = "CRASHED"
            elif size_mb > 300:
                status = "LARGE"
            elif lines < 100:
                status = "SMALL"
            else:
                status = "HEALTHY"

            sessions.append(SessionHealth(
                session_id=jsonl_file.stem,
                path=jsonl_file,
                lines=lines,
                size_mb=size_mb,
                has_errors=has_errors,
                last_activity=last_activity,
                status=status
            ))
        except Exception as e:
            print(f"[WARNING] Could not check {jsonl_file.name}: {e}")

    return sessions

# =============================================================================
# REPORT GENERATION
# =============================================================================

def print_frosty_report(flagged_files: List[FlaggedFile], commits: List[Dict]):
    """Print the Operation Frosty report."""
    print("=" * 80)
    print("              OPERATION FROSTY v2.0 - Documentation Refresh")
    print("=" * 80)
    print()

    print("Last commits analyzed:")
    for commit in commits[:5]:
        print(f"  {commit['hash']} {commit['message'][:60]}")
    print()

    flagged = [f for f in flagged_files if f.priority != "NONE"]

    if not flagged:
        print("No files flagged for update. Documentation appears current.")
        return

    print("=" * 80)
    print("FILES FLAGGED FOR UPDATE (by priority)")
    print("=" * 80)
    print()

    priority_order = {"HIGH": 0, "MEDIUM": 1, "LOW": 2}
    flagged.sort(key=lambda f: priority_order.get(f.priority, 3))

    for f in flagged:
        rel_path = f.path.relative_to(REPO_ROOT)
        print(f"[{f.priority}] {rel_path}")

        if f.last_reviewed:
            print(f"  Last reviewed: {f.last_reviewed.strftime('%Y-%m-%d')}")
        else:
            print("  Last reviewed: NEVER (no manifest)")

        if f.commits_since > 0:
            print(f"  Related commits: {f.commits_since}")

        if f.reasons:
            print("  Reasons:")
            for reason in f.reasons[:5]:
                print(f"    - {reason}")

        print("  Checklist:")
        for item in f.checklist:
            print(f"    {item}")
        print()

    print("=" * 80)
    print("SUGGESTED UPDATE ORDER")
    print("=" * 80)
    print()

    high_priority = [f for f in flagged if f.priority == "HIGH"]
    medium_priority = [f for f in flagged if f.priority == "MEDIUM"]

    order = 1
    for f in high_priority + medium_priority:
        rel_path = f.path.relative_to(REPO_ROOT)
        print(f"{order}. {rel_path}")
        order += 1

    print()
    print(f"Total files flagged: {len(flagged)}")
    print(f"  HIGH: {len(high_priority)}")
    print(f"  MEDIUM: {len(medium_priority)}")
    print(f"  LOW: {len([f for f in flagged if f.priority == 'LOW'])}")

def print_link_validation_report(results: List[LinkValidation]):
    """Print link validation report."""
    print("=" * 80)
    print("              OPERATION FROSTY v2.0 - Link Validation")
    print("=" * 80)
    print()

    broken = [r for r in results if not r.valid]
    valid_count = len(results) - len(broken)

    print(f"Total links checked: {len(results)}")
    print(f"  Valid: {valid_count}")
    print(f"  Broken: {len(broken)}")
    print()

    if broken:
        print("BROKEN LINKS:")
        print("-" * 40)
        for link in broken:
            rel_path = link.source_file.relative_to(REPO_ROOT)
            print(f"  {rel_path}:{link.line_number}")
            print(f"    [{link.link_text}]({link.link_target})")
            print(f"    Error: {link.error}")
            print()
    else:
        print("All links are valid!")

def print_consistency_report(results: List[TermConsistency]):
    """Print term consistency report."""
    print("=" * 80)
    print("              OPERATION FROSTY v2.0 - Term Consistency")
    print("=" * 80)
    print()

    for result in results:
        status = "CONSISTENT" if result.consistent else "INCONSISTENT"
        print(f"[{status}] {result.term}")
        print(f"  Expected: {', '.join(result.expected)}")

        if result.found:
            print(f"  Found values:")
            for value, locations in result.found.items():
                print(f"    '{value}' in {len(locations)} location(s)")
                for path, line in locations[:3]:  # Show first 3
                    rel_path = path.relative_to(REPO_ROOT)
                    print(f"      - {rel_path}:{line}")
                if len(locations) > 3:
                    print(f"      ... and {len(locations) - 3} more")
        else:
            print(f"  Not found in any files")
        print()

def print_plan_registry_report(plans: List[PlanStatus]):
    """Print plan registry report."""
    print("=" * 80)
    print("              OPERATION FROSTY v2.0 - Plan Registry")
    print("=" * 80)
    print()

    # Group by status
    by_status = defaultdict(list)
    for plan in plans:
        by_status[plan.status].append(plan)

    status_order = ["IN PROGRESS", "READY", "BLOCKED", "COMPLETE", "UNKNOWN"]

    for status in status_order:
        if status in by_status:
            print(f"\n[{status}] ({len(by_status[status])} plans)")
            print("-" * 40)
            for plan in by_status[status]:
                modified = plan.last_modified.strftime("%Y-%m-%d") if plan.last_modified else "Unknown"
                print(f"  {plan.slug}")
                print(f"    Claude: {plan.claude_session}")
                print(f"    Modified: {modified}")
                print(f"    Purpose: {plan.purpose[:60]}...")
                print()

    print(f"\nTotal plans: {len(plans)}")

def print_session_health_report(sessions: List[SessionHealth]):
    """Print session health report."""
    print("=" * 80)
    print("              OPERATION FROSTY v2.0 - Session Health")
    print("=" * 80)
    print()

    # Sort by status priority
    status_order = {"CRASHED": 0, "LARGE": 1, "SMALL": 2, "HEALTHY": 3}
    sessions.sort(key=lambda s: status_order.get(s.status, 4))

    for session in sessions:
        status_icon = {
            "HEALTHY": "[OK]",
            "LARGE": "[WARN]",
            "CRASHED": "[ERROR]",
            "SMALL": "[INFO]"
        }.get(session.status, "[?]")

        print(f"{status_icon} {session.session_id[:20]}...")
        print(f"    Lines: {session.lines:,} | Size: {session.size_mb:.1f}MB | Status: {session.status}")
        if session.last_activity:
            print(f"    Last activity: {session.last_activity.strftime('%Y-%m-%d %H:%M')}")
        print()

    # Summary
    crashed = len([s for s in sessions if s.status == "CRASHED"])
    large = len([s for s in sessions if s.status == "LARGE"])
    healthy = len([s for s in sessions if s.status == "HEALTHY"])

    print(f"\nSummary: {len(sessions)} sessions")
    print(f"  Healthy: {healthy}")
    print(f"  Large (>300MB): {large}")
    print(f"  Crashed/Errors: {crashed}")

def print_audit_report(flagged: List[FlaggedFile], links: List[LinkValidation],
                       terms: List[TermConsistency], plans: List[PlanStatus],
                       sessions: List[SessionHealth], commits: List[Dict]):
    """Print comprehensive audit report."""
    print("=" * 80)
    print("        OPERATION FROSTY v2.0 - COMPREHENSIVE NAVIGATION AUDIT")
    print("=" * 80)
    print(f"  Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print(f"  Repository: {REPO_ROOT}")
    print("=" * 80)
    print()

    # Calculate scores
    doc_score = 10 - min(len([f for f in flagged if f.priority == "HIGH"]) * 2, 4)
    link_score = 10 if not any(not l.valid for l in links) else max(0, 10 - len([l for l in links if not l.valid]))
    term_score = 10 if all(t.consistent for t in terms) else 5
    plan_score = 10 - min(len([p for p in plans if p.status == "BLOCKED"]) * 2, 4)
    session_score = 10 - min(len([s for s in sessions if s.status == "CRASHED"]) * 3, 6)

    overall = (doc_score + link_score + term_score + plan_score + session_score) / 5

    print("NAVIGATION HEALTH SCORES")
    print("-" * 40)
    print(f"  Documentation freshness:  {doc_score}/10")
    print(f"  Link validity:            {link_score}/10")
    print(f"  Term consistency:         {term_score}/10")
    print(f"  Plan registry:            {plan_score}/10")
    print(f"  Session health:           {session_score}/10")
    print("-" * 40)
    print(f"  OVERALL SCORE:            {overall:.1f}/10")
    print()

    # Quick summary
    print("QUICK SUMMARY")
    print("-" * 40)
    print(f"  Docs needing update: {len([f for f in flagged if f.priority in ['HIGH', 'MEDIUM']])}")
    print(f"  Broken links: {len([l for l in links if not l.valid])}")
    print(f"  Inconsistent terms: {len([t for t in terms if not t.consistent])}")
    print(f"  Plans in progress: {len([p for p in plans if p.status == 'IN PROGRESS'])}")
    print(f"  Crashed sessions: {len([s for s in sessions if s.status == 'CRASHED'])}")
    print()

    # Recommendations
    print("TOP RECOMMENDATIONS")
    print("-" * 40)

    recommendations = []

    high_priority = [f for f in flagged if f.priority == "HIGH"]
    if high_priority:
        recommendations.append(f"1. Update {len(high_priority)} HIGH priority docs")

    broken_links = [l for l in links if not l.valid]
    if broken_links:
        recommendations.append(f"2. Fix {len(broken_links)} broken links")

    crashed = [s for s in sessions if s.status == "CRASHED"]
    if crashed:
        recommendations.append(f"3. Recover {len(crashed)} crashed sessions")

    blocked = [p for p in plans if p.status == "BLOCKED"]
    if blocked:
        recommendations.append(f"4. Unblock {len(blocked)} plans")

    if not recommendations:
        recommendations.append("All systems healthy! Consider running experiments.")

    for rec in recommendations[:5]:
        print(f"  {rec}")

    print()
    print("=" * 80)
    print("Run with specific flags for detailed reports:")
    print("  --validate-links    Detailed broken link report")
    print("  --check-consistency Detailed term usage report")
    print("  --plan-registry     Detailed plan status report")
    print("  --session-health    Detailed session health report")
    print("=" * 80)

# =============================================================================
# MANIFEST UPDATE
# =============================================================================

def update_manifest_timestamp(file_path: Path) -> bool:
    """Update the last_reviewed timestamp in a file's manifest."""
    try:
        content = file_path.read_text(encoding='utf-8')
    except:
        return False

    today = datetime.now().strftime("%Y-%m-%d")

    pattern = r'(<!--\s*FROSTY_MANIFEST\s*\n)(.*?)(-->)'

    def replace_timestamp(match):
        prefix = match.group(1)
        manifest_content = match.group(2)
        suffix = match.group(3)

        if 'last_reviewed:' in manifest_content:
            manifest_content = re.sub(
                r'last_reviewed:\s*\d{4}-\d{2}-\d{2}',
                f'last_reviewed: {today}',
                manifest_content
            )
        else:
            manifest_content = f'last_reviewed: {today}\n' + manifest_content

        return prefix + manifest_content + suffix

    new_content, count = re.subn(pattern, replace_timestamp, content, flags=re.DOTALL)

    if count > 0:
        file_path.write_text(new_content, encoding='utf-8')
        print(f"  Updated: {file_path.relative_to(REPO_ROOT)}")
        return True
    else:
        print(f"  No manifest found: {file_path.relative_to(REPO_ROOT)}")
        return False

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Operation Frosty v2.0 - Cold-Boot Documentation & Navigation Automation"
    )
    parser.add_argument(
        "--commits", "-c", type=int, default=DEFAULT_COMMIT_DEPTH,
        help=f"Number of commits to analyze (default: {DEFAULT_COMMIT_DEPTH})"
    )
    parser.add_argument(
        "--dir", "-d", type=str, default=None,
        help="Scan specific subdirectory (relative to repo root)"
    )
    parser.add_argument(
        "--update-manifests", "-u", action="store_true",
        help="Update last_reviewed timestamps in all manifests"
    )
    parser.add_argument(
        "--validate-links", "-l", action="store_true",
        help="Validate all markdown links in the repository"
    )
    parser.add_argument(
        "--check-consistency", "-t", action="store_true",
        help="Check key term consistency across all docs"
    )
    parser.add_argument(
        "--audit", "-a", action="store_true",
        help="Run comprehensive navigation audit"
    )
    parser.add_argument(
        "--plan-registry", "-p", action="store_true",
        help="Scan and report on plan file status"
    )
    parser.add_argument(
        "--session-health", "-s", action="store_true",
        help="Check Claude session JSONL file health"
    )

    args = parser.parse_args()

    print(f"\nOperation Frosty v2.0 - Scanning from: {REPO_ROOT}")
    print()

    # Handle specific modes
    if args.validate_links:
        print("Validating all markdown links...")
        results = validate_all_links(REPO_ROOT)
        print_link_validation_report(results)
        return

    if args.check_consistency:
        print("Checking term consistency...")
        results = check_term_consistency(REPO_ROOT)
        print_consistency_report(results)
        return

    if args.plan_registry:
        print("Scanning plan registry...")
        plans = scan_plan_files()
        print_plan_registry_report(plans)
        return

    if args.session_health:
        print("Checking session health...")
        sessions = check_session_health()
        print_session_health_report(sessions)
        return

    if args.audit:
        print("Running comprehensive audit...")
        commits = get_recent_commits(args.commits)
        docs = scan_cold_boot_docs(REPO_ROOT, args.dir)
        flagged = [check_file_staleness(doc, commits) for doc in docs]
        links = validate_all_links(REPO_ROOT)
        terms = check_term_consistency(REPO_ROOT)
        plans = scan_plan_files()
        sessions = check_session_health()
        print_audit_report(flagged, links, terms, plans, sessions, commits)
        return

    # Default mode: staleness check
    print(f"Analyzing last {args.commits} commits...")
    commits = get_recent_commits(args.commits)

    if not commits:
        print("[WARNING] No git commits found or git unavailable")

    docs = scan_cold_boot_docs(REPO_ROOT, args.dir)
    print(f"Found {len(docs)} cold-boot documentation files")
    print()

    if args.update_manifests:
        print("Updating manifest timestamps...")
        for doc in docs:
            update_manifest_timestamp(doc)
        return

    flagged = []
    for doc in docs:
        result = check_file_staleness(doc, commits)
        flagged.append(result)

    print_frosty_report(flagged, commits)

if __name__ == "__main__":
    main()
