#!/usr/bin/env python3
"""
2_package_review.py - REVIEW PACKAGE EXTRACTOR
===============================================
Extracts path-specific review packages from WHITE-PAPER for AI reviewers.

WHITE-PAPER is ~41MB total (figures + PDF dominate). This script extracts
manageable packages (~100KB-700KB each) for different publication paths.

USAGE:
------
py 2_package_review.py workshop          # Extract single path (with figures)
py 2_package_review.py workshop arxiv    # Extract multiple paths
py 2_package_review.py --all             # Extract ALL 8 paths
py 2_package_review.py arxiv --no-figures        # Exclude figure specs
py 2_package_review.py arxiv --include-pdf       # Include 14MB PDF in package
py 2_package_review.py workshop --dry-run        # Preview extraction
py 2_package_review.py workshop --output ./FOR_OPUS_1  # Custom output
py 2_package_review.py --extract-pdfs            # Extract PDFs to packages/pdf/

OUTPUT:
-------
WHITE-PAPER/reviewers/packages/v4/{path}/
├── README.md                    # Instructions for reviewers
├── PACKAGE_MANIFEST.md          # What's included + reading order
├── {PATH}_BLUEPRINT.md          # Blueprint for this path (at root)
├── submissions/                 # Core submission materials (FLAT - no nested path dir)
├── theory/                      # Theory docs (varies by path)
├── guides/                      # Guides (varies by path)
└── figures/                     # Figure specs (included by default)

PDF LAYER (separate):
WHITE-PAPER/reviewers/packages/pdf/
├── README.md                    # PDF layer overview
├── visualization_pdfs/          # S7_ARMADA visualization summaries
└── submission_pdfs/             # Generated submission PDFs

Author: WHITE-PAPER Calibration
Version: 2.0 (2025-12-29) - IRON CLAD Methodology (Cosine D=0.80)
"""

import argparse
import shutil
import hashlib
import json
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Set
from dataclasses import dataclass, field

# Add parent directories to path for converter imports
sys.path.insert(0, str(Path(__file__).parent.parent))
from guides._convert_to_reviewer import convert_content as convert_guides_content
from planning._convert_to_reviewer import convert_content as convert_planning_content
from theory._convert_to_reviewer import convert_content as convert_theory_content

# === PATH CONSTANTS ===
WHITE_PAPER_ROOT = Path(__file__).parent.parent  # WHITE-PAPER/
REPO_ROOT = WHITE_PAPER_ROOT.parent              # Nyquist_Consciousness/
DEFAULT_OUTPUT_DIR = WHITE_PAPER_ROOT / "reviewers" / "packages" / "v4"  # v4 packages (Run 023d IRON CLAD + Oobleck Effect)
PDF_OUTPUT_DIR = WHITE_PAPER_ROOT / "reviewers" / "packages" / "pdf"
# LLM content source: REPO-SYNC/LLM_BOOK/2_PUBLICATIONS/ (organized by publication type)
LLM_PUBLICATIONS_DIR = REPO_ROOT / "REPO-SYNC" / "LLM_BOOK" / "2_PUBLICATIONS"

# === PUBLICATION PATHS (8 total) ===
PUBLICATION_PATHS = [
    "workshop",      # Academic: NeurIPS/AAAI Workshop (4-8 pages)
    "arxiv",         # Academic: cs.AI preprint (25-35 pages)
    "journal",       # Academic: Nature MI (full paper)
    "popular_science",  # Dissemination: Atlantic/Wired
    "education",     # Dissemination: OER/Coursera
    "policy",        # Dissemination: Think tanks
    "funding",       # Dissemination: NSF/DARPA
    "media",         # Dissemination: Press/TED
]

# Path to PACKAGE_INDEX.json template (SSOT for shared content mapping)
PACKAGE_INDEX_TEMPLATE = WHITE_PAPER_ROOT / "planning" / "reviewer_templates" / "PACKAGE_INDEX.json"


def get_shared_content_for_path(path_name: str) -> Dict[str, List[Dict[str, str]]]:
    """
    Read PACKAGE_INDEX.json and return the .shared/ content relevant for a specific path.
    Returns dict organized by category: {category: [{file: description}, ...]}
    """
    if not PACKAGE_INDEX_TEMPLATE.exists():
        return {}

    try:
        with open(PACKAGE_INDEX_TEMPLATE, 'r', encoding='utf-8') as f:
            index = json.load(f)
    except (json.JSONDecodeError, IOError):
        return {}

    shared_content = index.get("shared_content", {})
    result = {}

    for category, files in shared_content.items():
        category_files = []
        for filename, file_info in files.items():
            # Handle both dict format and array format for paths
            if isinstance(file_info, dict):
                paths = file_info.get("paths", [])
                description = file_info.get("description", "")
                if path_name in paths:
                    category_files.append({
                        "file": filename,
                        "description": description
                    })
        if category_files:
            result[category] = category_files

    return result


# === NOTEBOOKLM INTEGRATION ===
# Map publication paths → source subdirectories in LLM_BOOK/2_PUBLICATIONS/
# Format: path_name: [(source_subdir, filename), ...]
#
# Source subdirectories in LLM_BOOK/2_PUBLICATIONS/:
#   academic/    - for arxiv, journal, workshop
#   education/   - for education path
#   funding/     - for funding path
#   media/       - for media path
#   policy/      - for policy path
#   popular_science/ - for popular_science path
#
NOTEBOOKLM_INTEGRATION = {
    "arxiv": [
        ("academic", "Measuring AI Identity as a Dynamical System - An Empirical Framework Based on 750 Experiments Across 25 Models.md"),
        ("academic", "Technical Report - Comparative Analysis of AI Provider Identity Stability.md"),
        ("academic", "The Nyquist Consciousness Framework - An Empirical Analysis of AI Identity Dynamics.md"),
    ],
    "journal": [
        ("academic", "Measuring AI Identity as a Dynamical System - An Empirical Framework Based on 750 Experiments Across 25 Models.md"),
        ("academic", "Technical Report - Comparative Analysis of AI Provider Identity Stability.md"),
        ("academic", "The Nyquist Consciousness Framework - An Empirical Analysis of AI Identity Dynamics.md"),
    ],
    "workshop": [
        ("policy", "Briefing Document - The Nyquist Consciousness Framework for AI Identity Dynamics.md"),
    ],
    "popular_science": [
        ("popular_science", "Measuring an AI's Identity - Charting Personality Drift with an Engineer's Toolkit.md"),
    ],
    "education": [
        ("education", "Decoding AI Identity - A Visual Guide to Model Waveforms.md"),
        ("education", "The Five Discoveries of Nyquist Consciousness - A Student's Guide to AI Identity.md"),
        ("education", "A Learner's Glossary - Key Terms in Nyquist Consciousness Research.md"),
    ],
    "policy": [
        ("policy", "Briefing Document - The Nyquist Consciousness Framework for AI Identity Dynamics.md"),
    ],
    "funding": [
        ("funding", "Project Nyquist Consciousness - A Proposal for the Next Phase of Research into AI Identity Dynamics and Control.md"),
        ("academic", "Technical Report - Comparative Analysis of AI Provider Identity Stability.md"),
    ],
    "media": [
        ("media", "The Nyquist Consciousness Framework - A New Paradigm for Measuring and Engineering AI Identity.md"),
    ],
}


@dataclass
class PathContent:
    """Defines what content belongs to each publication path."""
    name: str
    description: str
    target_venue: str
    submissions: List[str]      # Dirs under submissions/
    blueprints: List[str]       # Files under submissions/blueprints/
    theory: List[str]           # Files/patterns under theory/
    guides: List[str]           # Files/patterns under guides/
    references: List[str]       # Files under references/
    figures: List[str]          # Files/patterns under figures/
    planning: List[str]         # Files under planning/
    reviewers: List[str]        # Files/patterns under reviewers/
    reading_order: List[str] = field(default_factory=list)  # Suggested reading order


# === CONTENT MAPPINGS FOR EACH PATH ===

WORKSHOP_CONTENT = PathContent(
    name="workshop",
    description="Workshop paper package (4-8 pages, focused claims)",
    target_venue="NeurIPS/AAAI Workshop",
    submissions=["workshop/"],
    blueprints=["WORKSHOP_BLUEPRINT.md"],
    # All shared content (theory, guides, figures, references, planning) lives in .shared/
    # Path packages only contain path-specific submissions + blueprint
    theory=[],
    guides=[],
    references=[],
    figures=[],
    planning=[],
    reviewers=[],
    reading_order=[
        "submissions/README.md",
        "WORKSHOP_BLUEPRINT.md",
        # Reviewers should use .shared/ for: theory/, guides/, figures/, references/
    ]
)

ARXIV_CONTENT = PathContent(
    name="arxiv",
    description="arXiv preprint package (25-35 pages, full methodology)",
    target_venue="cs.AI Preprint",
    submissions=["arxiv/"],
    blueprints=["ARXIV_BLUEPRINT.md"],
    # All shared content (theory, guides, figures, references, planning) lives in .shared/
    # Path packages only contain path-specific submissions + blueprint
    theory=[],
    guides=[],
    references=[],
    figures=[],
    planning=[],
    reviewers=[],
    reading_order=[
        "submissions/README.md",
        "ARXIV_BLUEPRINT.md",
        # Reviewers should use .shared/ for: theory/, guides/, figures/, references/
    ]
)

JOURNAL_CONTENT = PathContent(
    name="journal",
    description="Journal paper package (Nature MI, comprehensive)",
    target_venue="Nature Machine Intelligence",
    submissions=["journal/"],  # Just journal content (arxiv has its own package)
    blueprints=["JOURNAL_BLUEPRINT.md"],
    # All shared content (theory, guides, figures, references, planning) lives in .shared/
    # Path packages only contain path-specific submissions + blueprint
    theory=[],
    guides=[],
    references=[],
    figures=[],
    planning=[],
    reviewers=[],
    reading_order=[
        "submissions/README.md",
        "JOURNAL_BLUEPRINT.md",
        # Reviewers should use .shared/ for: theory/, guides/, figures/, references/
    ]
)

POPULAR_SCIENCE_CONTENT = PathContent(
    name="popular_science",
    description="Popular science article package (Atlantic/Wired style)",
    target_venue="The Atlantic / Wired / Scientific American",
    submissions=["popular_science/"],
    blueprints=[],
    # All shared content lives in .shared/
    theory=[],
    guides=[],
    references=[],
    figures=[],
    planning=[],
    reviewers=[],
    reading_order=[
        "submissions/README.md",
        "submissions/POPULAR_SCIENCE_FINAL.md",
    ]
)

EDUCATION_CONTENT = PathContent(
    name="education",
    description="Educational materials package (OER/Coursera)",
    target_venue="Open Educational Resources / Coursera",
    submissions=["education/"],
    blueprints=[],
    # All shared content lives in .shared/
    theory=[],
    guides=[],
    references=[],
    figures=[],
    planning=[],
    reviewers=[],
    reading_order=[
        "submissions/README.md",
        "submissions/EDUCATION_FINAL.md",
    ]
)

POLICY_CONTENT = PathContent(
    name="policy",
    description="Policy briefing package (Think tanks)",
    target_venue="Brookings / Center for AI Safety / EU AI Office",
    submissions=["policy/"],
    blueprints=[],
    # All shared content lives in .shared/
    theory=[],
    guides=[],
    references=[],
    figures=[],
    planning=[],
    reviewers=[],
    reading_order=[
        "submissions/README.md",
        "submissions/POLICY_FINAL.md",
    ]
)

FUNDING_CONTENT = PathContent(
    name="funding",
    description="Funding proposal package (NSF/DARPA)",
    target_venue="NSF / DARPA / Open Philanthropy",
    submissions=["funding/"],
    blueprints=[],
    # All shared content lives in .shared/
    theory=[],
    guides=[],
    references=[],
    figures=[],
    planning=[],
    reviewers=[],
    reading_order=[
        "submissions/README.md",
        "submissions/FUNDING_FINAL.md",
    ]
)

MEDIA_CONTENT = PathContent(
    name="media",
    description="Media/press package (Press releases, podcasts)",
    target_venue="Press / Podcasts / TED",
    submissions=["media/"],  # Just media content (popular_science has its own package)
    blueprints=[],
    # All shared content lives in .shared/
    theory=[],
    guides=[],
    references=[],
    figures=[],
    planning=[],
    reviewers=[],
    reading_order=[
        "submissions/README.md",
        "submissions/MEDIA_FINAL.md",
    ]
)

# Map path names to content definitions
PATH_CONTENT_MAP: Dict[str, PathContent] = {
    "workshop": WORKSHOP_CONTENT,
    "arxiv": ARXIV_CONTENT,
    "journal": JOURNAL_CONTENT,
    "popular_science": POPULAR_SCIENCE_CONTENT,
    "education": EDUCATION_CONTENT,
    "policy": POLICY_CONTENT,
    "funding": FUNDING_CONTENT,
    "media": MEDIA_CONTENT,
}


def get_file_hash(path: Path) -> str:
    """Calculate MD5 hash of file."""
    if not path.exists() or path.is_dir():
        return ""
    hasher = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def resolve_patterns(base_dir: Path, patterns: List[str]) -> List[Path]:
    """
    Resolve glob patterns to actual file paths.

    Args:
        base_dir: Directory to search in (e.g., WHITE_PAPER_ROOT / "theory")
        patterns: List of patterns like ["*.md", "MINIMUM*.md"]

    Returns:
        List of resolved Path objects
    """
    files: Set[Path] = set()

    for pattern in patterns:
        if not pattern:
            continue

        # Handle directory patterns (ending with /)
        if pattern.endswith("/"):
            dir_path = base_dir / pattern.rstrip("/")
            if dir_path.exists() and dir_path.is_dir():
                for f in dir_path.rglob("*"):
                    if f.is_file():
                        files.add(f)
        else:
            # Regular glob pattern
            for f in base_dir.glob(pattern):
                if f.is_file():
                    files.add(f)

    return sorted(files)


def calculate_total_size(files: List[Path]) -> int:
    """Calculate total size in bytes of file list."""
    return sum(f.stat().st_size for f in files if f.exists())


def format_size(size_bytes: int) -> str:
    """Format bytes as human-readable string."""
    if size_bytes < 1024:
        return f"{size_bytes} B"
    elif size_bytes < 1024 * 1024:
        return f"{size_bytes / 1024:.1f} KB"
    else:
        return f"{size_bytes / (1024 * 1024):.1f} MB"


def collect_package_files(
    path_content: PathContent,
    include_figures: bool = False,
    include_pdf: bool = False
) -> Dict[str, List[Path]]:
    """
    Collect all files for a publication path package.

    Returns dict like:
    {
        "submissions": [Path(...)],
        "blueprints": [Path(...)],
        "theory": [Path(...)],
        ...
    }
    """
    collected: Dict[str, List[Path]] = {
        "submissions": [],
        "blueprints": [],
        "theory": [],
        "guides": [],
        "references": [],
        "figures": [],
        "planning": [],
        "reviewers": [],
    }

    # Submissions
    submissions_dir = WHITE_PAPER_ROOT / "submissions"
    for pattern in path_content.submissions:
        collected["submissions"].extend(
            resolve_patterns(submissions_dir, [pattern])
        )

    # Blueprints
    blueprints_dir = WHITE_PAPER_ROOT / "submissions" / "blueprints"
    collected["blueprints"] = resolve_patterns(blueprints_dir, path_content.blueprints)

    # Theory
    theory_dir = WHITE_PAPER_ROOT / "theory"
    collected["theory"] = resolve_patterns(theory_dir, path_content.theory)

    # Guides
    guides_dir = WHITE_PAPER_ROOT / "guides"
    collected["guides"] = resolve_patterns(guides_dir, path_content.guides)

    # References
    references_dir = WHITE_PAPER_ROOT / "references"
    collected["references"] = resolve_patterns(references_dir, path_content.references)

    # Figures (only if requested)
    if include_figures:
        figures_dir = WHITE_PAPER_ROOT / "figures"
        collected["figures"] = resolve_patterns(figures_dir, path_content.figures)

    # Planning
    planning_dir = WHITE_PAPER_ROOT / "planning"
    collected["planning"] = resolve_patterns(planning_dir, path_content.planning)

    # Reviewers
    reviewers_dir = WHITE_PAPER_ROOT / "reviewers"
    collected["reviewers"] = resolve_patterns(reviewers_dir, path_content.reviewers)

    # Filter out PDFs unless explicitly requested
    if not include_pdf:
        for category in collected:
            collected[category] = [f for f in collected[category] if f.suffix.lower() != ".pdf"]

    return collected


def generate_manifest(
    path_content: PathContent,
    collected: Dict[str, List[Path]],
    output_dir: Path,
    include_figures: bool,
    include_pdf: bool,
    llm_files_copied: List[str] = None
) -> str:
    """Generate PACKAGE_MANIFEST.md content."""

    llm_files_copied = llm_files_copied or []
    total_files = sum(len(files) for files in collected.values()) + len(llm_files_copied)
    total_size = sum(calculate_total_size(files) for files in collected.values())

    lines = [
        f"# Review Package: {path_content.name.upper()}",
        "",
        f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        f"**Target Venue:** {path_content.target_venue}",
        f"**Total Size:** {format_size(total_size)}",
        f"**Total Files:** {total_files}",
        "",
        "---",
        "",
        f"## Description",
        "",
        path_content.description,
        "",
        "---",
        "",
        "## Reading Order",
        "",
        "Start with these files in order:",
        "",
    ]

    for i, path in enumerate(path_content.reading_order, 1):
        lines.append(f"{i}. `{path}`")

    lines.extend([
        "",
        "---",
        "",
        "## Contents",
        "",
        "| Category | Files | Size |",
        "|----------|-------|------|",
    ])

    for category, files in collected.items():
        if files:
            size = format_size(calculate_total_size(files))
            lines.append(f"| {category}/ | {len(files)} files | {size} |")

    # Add LLM_SYNTHESIS row if files were copied
    if llm_files_copied:
        lines.append(f"| LLM_SYNTHESIS/ | {len(llm_files_copied)} files | (included) |")

    lines.extend([
        "",
        f"**Total:** {total_files} files, {format_size(total_size)}",
        "",
        "---",
        "",
        "## File Listing",
        "",
    ])

    for category, files in collected.items():
        if files:
            lines.append(f"### {category}/")
            lines.append("")
            for f in files:
                rel_path = f.relative_to(WHITE_PAPER_ROOT)
                size = format_size(f.stat().st_size)
                lines.append(f"- `{rel_path}` ({size})")
            lines.append("")

    # Add LLM_SYNTHESIS listing if files were copied
    if llm_files_copied:
        lines.append("### LLM_SYNTHESIS/")
        lines.append("")
        lines.append("*NotebookLM-generated content for this publication path:*")
        lines.append("")
        for filename in llm_files_copied:
            lines.append(f"- `LLM_SYNTHESIS/{filename}`")
        lines.append("")

    # Add recommended .shared/ content section
    shared_content = get_shared_content_for_path(path_content.name)
    if shared_content:
        lines.extend([
            "---",
            "",
            "## Recommended .shared/ Content",
            "",
            "This path should also reference the following files from `.shared/`:",
            "",
        ])

        for category, files in sorted(shared_content.items()):
            lines.append(f"### .shared/{category}/")
            lines.append("")
            for file_info in files:
                lines.append(f"- **{file_info['file']}** — {file_info['description']}")
            lines.append("")

        lines.extend([
            "*These files live in `.shared/` to avoid duplication across paths.*",
            "*See `.shared/PACKAGE_INDEX.json` for complete content mapping.*",
            "",
        ])

    lines.extend([
        "---",
        "",
        "## What's NOT Included",
        "",
    ])

    if not include_figures:
        lines.append("- Figure specification files (included by default, use `--no-figures` to exclude)")
    if not include_pdf:
        lines.append("- PDF files including 14MB arxiv PDF (use `--include-pdf` to add)")
    lines.append("- Other publication path content")
    lines.append("- Large binary files")

    lines.extend([
        "",
        "---",
        "",
        "## Review Instructions",
        "",
        "Please review this package for:",
        "",
        "1. **Accuracy of claims** - Are statements supported by evidence?",
        "2. **Clarity of presentation** - Is the writing clear and accessible?",
        "3. **Completeness of evidence** - Are key findings documented?",
        "4. **Suggested improvements** - What would strengthen the paper?",
        "",
        "Return feedback to: `WHITE-PAPER/reviewers/from_reviewers/{reviewer}/`",
        "",
        "---",
        "",
        f"*Package extracted from WHITE-PAPER/ for {path_content.target_venue} submission review.*",
    ])

    return "\n".join(lines)


def generate_readme(path_content: PathContent) -> str:
    """Generate README.md with reviewer instructions for the package."""

    lines = [
        f"# {path_content.name.upper()} Review Package",
        "",
        f"**Target Venue:** {path_content.target_venue}",
        f"**Package Type:** {path_content.description}",
        "",
        "---",
        "",
        "## Instructions for Reviewers",
        "",
        "This package contains all materials needed to review the Nyquist Consciousness",
        f"research for **{path_content.target_venue}** submission.",
        "",
        "### Getting Started",
        "",
        "1. **Read `PACKAGE_MANIFEST.md`** for the complete file listing and reading order",
        "2. **Follow the Reading Order** to understand the research systematically",
        "3. **Return feedback** to `WHITE-PAPER/reviewers/from_reviewers/{your_name}/`",
        "",
        "### Reading Order",
        "",
    ]

    for i, path in enumerate(path_content.reading_order, 1):
        lines.append(f"{i}. `{path}`")

    lines.extend([
        "",
        "---",
        "",
        "## Review Criteria",
        "",
        "Please evaluate this package for:",
        "",
        "### 1. Accuracy of Claims",
        "",
        "- Are statements supported by evidence?",
        "- Are statistics correctly reported?",
        "- Are limitations appropriately acknowledged?",
        "",
        "### 2. Clarity of Presentation",
        "",
        "- Is the writing clear and accessible for the target audience?",
        "- Are technical terms defined?",
        "- Is the logical flow easy to follow?",
        "",
        "### 3. Completeness of Evidence",
        "",
        "- Are key findings documented?",
        "- Is the methodology reproducible?",
        "- Are counterarguments addressed?",
        "",
        "### 4. Suggested Improvements",
        "",
        "- What would strengthen the paper?",
        "- Are there missing analyses?",
        "- What would a hostile reviewer attack?",
        "",
        "---",
        "",
        "## Key Research Claims (Run 023 IRON CLAD)",
        "",
        "The Nyquist Consciousness framework makes **5 core claims** - ALL VALIDATED:",
        "",
        "| Claim | Statement | Evidence | Methodology |",
        "|-------|-----------|----------|-------------|",
        "| **A** | PFI is valid structured measurement | rho = 0.91, d = 0.698 | Cosine |",
        "| **B** | Regime threshold at D = 0.80 | p = 2.40e-23 | Cosine |",
        "| **C** | Damped oscillator dynamics | Settling time, ringbacks measurable | Cosine |",
        "| **D** | Context damping works | 97.5% stability | - |",
        "| **E** | Drift mostly inherent (92%) | Control vs Treatment | - |",
        "",
        "**Run 023 Stats:** 750 experiments, 25 models, 5 providers",
        "",
        "---",
        "",
        "## NotebookLLM Validation",
        "",
        "Google's NotebookLLM independently processed this research and correctly identified:",
        "- All 5 core claims (A-E)",
        "- Event Horizon = 0.80",
        "- Cohen's d = 0.698",
        "- 92% inherent drift ratio",
        "- Novel phenomena: Oobleck Effect, Provider Fingerprints, Nano Control Hypothesis",
        "",
        "See: `LLM_SYNTHESIS/` directory for AI-generated publication content.",
        "",
        "---",
        "",
        "## Terminology Quick Reference",
        "",
        "| Term | Definition |",
        "|------|------------|",
        "| **PFI** | Persona Fidelity Index (1 - drift) |",
        "| **Drift (D)** | Cosine distance from baseline identity |",
        "| **Event Horizon** | Regime transition threshold (D = 0.80 Cosine) |",
        "| **Context Damping** | Stability via I_AM + research frame |",
        "| **Inherent Drift** | Drift without probing (92% of total) |",
        "",
        "For complete terminology, see `guides/summary_statistics.md` (if included).",
        "",
        "---",
        "",
        "## Feedback Format",
        "",
        "Please structure your feedback as:",
        "",
        "```markdown",
        f"# Review: {path_content.name.upper()}",
        "",
        "**Reviewer:** [Your name/ID]",
        "**Date:** [Date]",
        "",
        "## Overall Assessment",
        "[1-2 paragraph summary]",
        "",
        "## Specific Comments",
        "",
        "### Claim A (PFI Validity)",
        "[Comments]",
        "",
        "### Claim B (Threshold)",
        "[Comments]",
        "",
        "## Suggested Changes",
        "[Prioritized list]",
        "",
        "## Questions for Authors",
        "[List of clarifying questions]",
        "```",
        "",
        "---",
        "",
        f"*Package extracted from WHITE-PAPER/ for {path_content.target_venue} submission.*",
    ])

    return "\n".join(lines)


def extract_package(
    path_name: str,
    output_dir: Optional[Path] = None,
    include_figures: bool = False,
    include_pdf: bool = False,
    dry_run: bool = False
) -> Dict:
    """
    Extract a review package for a specific publication path.

    Args:
        path_name: One of PUBLICATION_PATHS
        output_dir: Where to write the package (default: reviewers/packages/{path}/)
        include_figures: Include figure specification files
        include_pdf: Include PDF files
        dry_run: Preview without writing files

    Returns:
        Dict with extraction results
    """
    if path_name not in PATH_CONTENT_MAP:
        return {"error": f"Unknown path: {path_name}. Valid: {PUBLICATION_PATHS}"}

    path_content = PATH_CONTENT_MAP[path_name]

    # Determine output directory
    if output_dir is None:
        output_dir = DEFAULT_OUTPUT_DIR / path_name
    else:
        output_dir = output_dir / path_name

    # Collect files
    collected = collect_package_files(path_content, include_figures, include_pdf)

    # Calculate statistics
    total_files = sum(len(files) for files in collected.values())
    total_size = sum(calculate_total_size(files) for files in collected.values())

    result = {
        "path": path_name,
        "description": path_content.description,
        "target_venue": path_content.target_venue,
        "output_dir": str(output_dir),
        "dry_run": dry_run,
        "include_figures": include_figures,
        "include_pdf": include_pdf,
        "statistics": {
            "total_files": total_files,
            "total_size_bytes": total_size,
            "total_size_human": format_size(total_size),
        },
        "categories": {},
        "files_copied": [],
        "errors": [],
    }

    for category, files in collected.items():
        result["categories"][category] = {
            "count": len(files),
            "size_bytes": calculate_total_size(files),
            "files": [str(f.relative_to(WHITE_PAPER_ROOT)) for f in files]
        }

    if dry_run:
        result["message"] = "Dry run - no files written"
        return result

    # Create output directory
    try:
        output_dir.mkdir(parents=True, exist_ok=True)
    except Exception as e:
        result["errors"].append(f"Failed to create output dir: {e}")
        return result

    # Copy files preserving relative structure
    # Markdown files from guides/ and planning/ get path conversion for reviewer packages
    for category, files in collected.items():
        for src_file in files:
            # Calculate relative path from WHITE_PAPER_ROOT
            rel_path = src_file.relative_to(WHITE_PAPER_ROOT)

            # FLATTEN submissions: remove path-specific subdirectory
            # e.g., submissions/journal/README.md → submissions/README.md
            if category == "submissions":
                parts = rel_path.parts
                if len(parts) >= 2 and parts[0] == "submissions":
                    # Remove the path-specific dir (e.g., "journal", "arxiv")
                    # submissions/journal/README.md → submissions/README.md
                    new_parts = ("submissions",) + parts[2:]
                    rel_path = Path(*new_parts)

            # FLATTEN blueprints: put at package root, not in blueprints/ subdirectory
            # e.g., submissions/blueprints/JOURNAL_BLUEPRINT.md → JOURNAL_BLUEPRINT.md
            if category == "blueprints":
                rel_path = Path(rel_path.name)

            dst_file = output_dir / rel_path

            try:
                dst_file.parent.mkdir(parents=True, exist_ok=True)

                # Apply path conversion for markdown files in guides/, planning/, theory/
                if src_file.suffix.lower() == ".md":
                    content = src_file.read_text(encoding="utf-8")

                    # Convert paths based on source directory
                    if category == "guides" or "guides" in str(rel_path):
                        content = convert_guides_content(content)
                    elif category == "planning" or "planning" in str(rel_path):
                        content = convert_planning_content(content)
                    elif category == "theory" or "theory" in str(rel_path):
                        content = convert_theory_content(content)

                    dst_file.write_text(content, encoding="utf-8")
                    # Preserve timestamps
                    shutil.copystat(src_file, dst_file)
                else:
                    # Non-markdown files: direct copy
                    shutil.copy2(src_file, dst_file)

                result["files_copied"].append(str(rel_path))
            except Exception as e:
                result["errors"].append(f"Failed to copy {rel_path}: {e}")

    # Generate and write README.md (reviewer instructions)
    readme_content = generate_readme(path_content)
    readme_path = output_dir / "README.md"
    try:
        readme_path.write_text(readme_content, encoding="utf-8")
        result["readme_path"] = str(readme_path)
    except Exception as e:
        result["errors"].append(f"Failed to write README: {e}")

    # Copy NotebookLM synthesis files BEFORE generating manifest
    llm_files_copied = []
    if not dry_run:
        llm_result = copy_notebooklm_synthesis(path_name, output_dir)
        if llm_result.get("files_copied"):
            llm_files_copied = llm_result["files_copied"]
            result["llm_synthesis_copied"] = llm_files_copied
        if llm_result.get("errors"):
            result["errors"].extend(llm_result["errors"])

    # Generate and write manifest (includes LLM_SYNTHESIS files)
    manifest_content = generate_manifest(
        path_content, collected, output_dir, include_figures, include_pdf, llm_files_copied
    )
    manifest_path = output_dir / "PACKAGE_MANIFEST.md"
    try:
        manifest_path.write_text(manifest_content, encoding="utf-8")
        result["manifest_path"] = str(manifest_path)
    except Exception as e:
        result["errors"].append(f"Failed to write manifest: {e}")

    result["message"] = f"Extracted {total_files} files ({format_size(total_size)}) to {output_dir}"

    return result


def copy_notebooklm_synthesis(path_name: str, output_dir: Path) -> Dict:
    """
    Copy relevant NotebookLM synthesis files to the package's LLM_SYNTHESIS/ directory.

    Files are sourced from REPO-SYNC/LLM_BOOK/2_PUBLICATIONS/{subdir}/
    Each entry in NOTEBOOKLM_INTEGRATION is a tuple: (source_subdir, filename)

    Args:
        path_name: Publication path (e.g., "arxiv", "workshop")
        output_dir: Package output directory

    Returns:
        Dict with files_copied and errors lists
    """
    result = {"files_copied": [], "errors": []}

    if path_name not in NOTEBOOKLM_INTEGRATION:
        return result

    # Check if source directory exists
    if not LLM_PUBLICATIONS_DIR.exists():
        result["errors"].append(f"LLM publications directory not found: {LLM_PUBLICATIONS_DIR}")
        return result

    synthesis_dir = output_dir / "LLM_SYNTHESIS"

    try:
        synthesis_dir.mkdir(parents=True, exist_ok=True)
    except Exception as e:
        result["errors"].append(f"Failed to create LLM_SYNTHESIS dir: {e}")
        return result

    for source_subdir, filename in NOTEBOOKLM_INTEGRATION[path_name]:
        # Source: REPO-SYNC/LLM_BOOK/2_PUBLICATIONS/{source_subdir}/{filename}
        src_file = LLM_PUBLICATIONS_DIR / source_subdir / filename
        if src_file.exists():
            dst_file = synthesis_dir / filename
            try:
                shutil.copy2(src_file, dst_file)
                result["files_copied"].append(filename)
            except Exception as e:
                result["errors"].append(f"Failed to copy {filename}: {e}")
        else:
            result["errors"].append(f"LLM synthesis file not found: {src_file}")

    return result


def generate_status_report(paths: Optional[List[str]] = None) -> str:
    """Generate a status report showing what would be extracted for each path."""

    paths_to_report = paths if paths else PUBLICATION_PATHS

    lines = [
        "=" * 70,
        "REVIEW PACKAGE EXTRACTION STATUS",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 70,
        "",
        "## Available Paths (figures included by default)",
        "",
        "| Path | Target | Est. Size | Files |",
        "|------|--------|-----------|-------|",
    ]

    total_files = 0
    total_size = 0

    for path_name in paths_to_report:
        if path_name not in PATH_CONTENT_MAP:
            lines.append(f"| {path_name} | UNKNOWN | - | - |")
            continue

        path_content = PATH_CONTENT_MAP[path_name]
        collected = collect_package_files(path_content, include_figures=True, include_pdf=False)

        file_count = sum(len(f) for f in collected.values())
        size = sum(calculate_total_size(f) for f in collected.values())

        total_files += file_count
        total_size += size

        lines.append(
            f"| {path_name} | {path_content.target_venue[:25]} | {format_size(size)} | {file_count} |"
        )

    lines.extend([
        "",
        f"**Total (all paths):** {total_files} files, {format_size(total_size)}",
        "",
        "---",
        "",
        "## Extraction Commands",
        "",
        "```bash",
        "# Extract single path (with figures)",
        "py 2_package_review.py workshop",
        "",
        "# Extract multiple paths",
        "py 2_package_review.py workshop arxiv",
        "",
        "# Extract ALL 8 paths",
        "py 2_package_review.py --all",
        "",
        "# Exclude figures (smaller packages)",
        "py 2_package_review.py arxiv --no-figures",
        "",
        "# Preview without extracting",
        "py 2_package_review.py workshop --dry-run",
        "",
        "# Custom output location",
        "py 2_package_review.py workshop --output ./FOR_OPUS",
        "```",
        "",
        "---",
        "",
        f"Output directory: {DEFAULT_OUTPUT_DIR.relative_to(REPO_ROOT)}/",
    ])

    return "\n".join(lines)


def generate_extraction_report(results: List[Dict]) -> str:
    """Generate a report of extraction results."""

    lines = [
        "=" * 70,
        "REVIEW PACKAGE EXTRACTION REPORT",
        f"Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 70,
        "",
    ]

    total_files = 0
    total_size = 0
    total_errors = 0

    for result in results:
        if result.get("error"):
            lines.append(f"## ERROR: {result['path']}")
            lines.append(f"  {result['error']}")
            total_errors += 1
            continue

        path_name = result["path"]
        stats = result["statistics"]

        lines.append(f"## {path_name.upper()}")
        lines.append(f"  Target: {result['target_venue']}")
        lines.append(f"  Output: {result['output_dir']}")
        lines.append(f"  Files:  {stats['total_files']}")
        lines.append(f"  Size:   {stats['total_size_human']}")

        if result["dry_run"]:
            lines.append("  Status: DRY RUN (no files written)")
        else:
            lines.append(f"  Status: EXTRACTED ({len(result.get('files_copied', []))} files copied)")

        if result.get("errors"):
            lines.append(f"  Errors: {len(result['errors'])}")
            for err in result["errors"][:3]:
                lines.append(f"    - {err}")

        lines.append("")

        total_files += stats["total_files"]
        total_size += stats["total_size_bytes"]
        total_errors += len(result.get("errors", []))

    lines.extend([
        "---",
        "",
        "## Summary",
        f"  Packages extracted: {len(results)}",
        f"  Total files:        {total_files}",
        f"  Total size:         {format_size(total_size)}",
        f"  Errors:             {total_errors}",
    ])

    if any(r.get("dry_run") for r in results):
        lines.append("")
        lines.append("Dry run complete. Remove --dry-run to actually extract.")

    return "\n".join(lines)


# === SHARED CONTENT SYNC ===

SHARED_OUTPUT_DIR = DEFAULT_OUTPUT_DIR / ".shared"
REVIEWER_TEMPLATES_DIR = WHITE_PAPER_ROOT / "planning" / "reviewer_templates"

# Define what goes into .shared/ (union of all path content)
SHARED_CONTENT_SPEC = {
    "theory": ["*.md"],  # All theory docs
    "guides": ["*.md"],  # All guides
    "planning": ["*.md"],  # All planning docs
    "references": ["references.md", "references.bib"],
    "figures": ["conceptual/", "ascii/", "experiments/", "visual_index.md"],
}

# Core template files that go in .shared/ root
CORE_TEMPLATES = [
    "START_HERE.md",
    "REVIEWER_BRIEF.md",
    "PACKAGE_INDEX.json",
]


def check_template_staleness() -> Dict:
    """
    Compare templates in planning/reviewer_templates/ against .shared/.
    Returns staleness report.
    """
    report = {
        "stale_files": [],
        "missing_in_shared": [],
        "missing_templates": [],
        "up_to_date": [],
    }

    for template_file in CORE_TEMPLATES:
        template_path = REVIEWER_TEMPLATES_DIR / template_file
        shared_path = SHARED_OUTPUT_DIR / template_file

        if not template_path.exists():
            report["missing_templates"].append(template_file)
            continue

        if not shared_path.exists():
            report["missing_in_shared"].append(template_file)
            continue

        # Compare modification times
        template_mtime = template_path.stat().st_mtime
        shared_mtime = shared_path.stat().st_mtime

        if template_mtime > shared_mtime:
            report["stale_files"].append({
                "file": template_file,
                "template_mtime": datetime.fromtimestamp(template_mtime).isoformat(),
                "shared_mtime": datetime.fromtimestamp(shared_mtime).isoformat(),
            })
        else:
            report["up_to_date"].append(template_file)

    return report


def merge_package_index(template_index: Dict, existing_index: Dict) -> Dict:
    """
    Merge PACKAGE_INDEX.json intelligently:
    - Increment version
    - Preserve existing path mappings
    - Add new entries from template
    - Update _meta with new timestamp
    """
    merged = existing_index.copy()

    # Update metadata
    if "_meta" in template_index:
        old_version = existing_index.get("_meta", {}).get("version", "1.0")
        try:
            # Try to increment version
            parts = old_version.split(".")
            parts[-1] = str(int(parts[-1]) + 1)
            new_version = ".".join(parts)
        except (ValueError, IndexError):
            new_version = old_version

        merged["_meta"] = template_index["_meta"].copy()
        merged["_meta"]["version"] = new_version
        merged["_meta"]["updated"] = datetime.now().strftime("%Y-%m-%d")

    # Merge shared_content (add new entries, don't remove old)
    if "shared_content" in template_index:
        if "shared_content" not in merged:
            merged["shared_content"] = {}
        for category, entries in template_index["shared_content"].items():
            if category not in merged["shared_content"]:
                merged["shared_content"][category] = entries
            else:
                # Merge entries
                if isinstance(entries, dict):
                    for key, value in entries.items():
                        if key not in merged["shared_content"][category]:
                            merged["shared_content"][category][key] = value

    # Preserve other sections from existing
    for key in existing_index:
        if key not in merged:
            merged[key] = existing_index[key]

    return merged


def sync_shared_content(dry_run: bool = False, force: bool = False) -> Dict:
    """
    Sync shared content to .shared/ directory.

    This creates a self-contained minimum viable package that can be
    given to any reviewer first.

    Args:
        dry_run: Preview without writing files
        force: Overwrite even if .shared/ files are newer than templates

    Returns:
        Dict with sync results
    """
    result = {
        "mode": "sync_shared",
        "output_dir": str(SHARED_OUTPUT_DIR),
        "dry_run": dry_run,
        "files_copied": [],
        "templates_copied": [],
        "errors": [],
        "categories": {},
        "staleness_report": None,
    }

    # Check template staleness first
    staleness = check_template_staleness()
    result["staleness_report"] = staleness

    if not dry_run:
        SHARED_OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # === SYNC CORE TEMPLATES FROM planning/reviewer_templates/ ===
    result["categories"]["templates"] = {"count": 0, "files": []}

    for template_file in CORE_TEMPLATES:
        template_path = REVIEWER_TEMPLATES_DIR / template_file
        shared_path = SHARED_OUTPUT_DIR / template_file

        if not template_path.exists():
            result["errors"].append(f"Template missing: {template_file}")
            continue

        result["categories"]["templates"]["count"] += 1
        result["categories"]["templates"]["files"].append(template_file)

        if not dry_run:
            try:
                if template_file == "PACKAGE_INDEX.json":
                    # Special handling for PACKAGE_INDEX.json - merge if exists
                    template_content = json.loads(template_path.read_text(encoding="utf-8"))

                    if shared_path.exists():
                        existing_content = json.loads(shared_path.read_text(encoding="utf-8"))
                        merged = merge_package_index(template_content, existing_content)
                        shared_path.write_text(json.dumps(merged, indent=2), encoding="utf-8")
                        result["templates_copied"].append(f"{template_file} (merged)")
                    else:
                        shared_path.write_text(json.dumps(template_content, indent=2), encoding="utf-8")
                        result["templates_copied"].append(template_file)
                else:
                    # Direct copy for markdown files
                    shutil.copy2(template_path, shared_path)
                    result["templates_copied"].append(template_file)
            except Exception as e:
                result["errors"].append(f"Failed to copy template {template_file}: {e}")

    # === SYNC CATEGORY CONTENT ===
    for category, patterns in SHARED_CONTENT_SPEC.items():
        source_dir = WHITE_PAPER_ROOT / category
        files = resolve_patterns(source_dir, patterns)

        result["categories"][category] = {
            "count": len(files),
            "size_bytes": calculate_total_size(files),
            "files": [f.name for f in files]
        }

        if not dry_run:
            dest_dir = SHARED_OUTPUT_DIR / category
            dest_dir.mkdir(parents=True, exist_ok=True)

            for src_file in files:
                # Preserve subdirectory structure within category
                rel_to_source = src_file.relative_to(source_dir)
                dst_file = dest_dir / rel_to_source

                try:
                    dst_file.parent.mkdir(parents=True, exist_ok=True)

                    # Apply path conversion for markdown files
                    if src_file.suffix.lower() == ".md":
                        content = src_file.read_text(encoding="utf-8")
                        if category == "guides":
                            content = convert_guides_content(content)
                        elif category == "planning":
                            content = convert_planning_content(content)
                        elif category == "theory":
                            content = convert_theory_content(content)
                        dst_file.write_text(content, encoding="utf-8")
                        shutil.copystat(src_file, dst_file)
                    else:
                        shutil.copy2(src_file, dst_file)

                    result["files_copied"].append(f"{category}/{rel_to_source}")
                except Exception as e:
                    result["errors"].append(f"Failed to copy {category}/{rel_to_source}: {e}")

    # === SYNC LLM_SYNTHESIS CONTENT (shared/common files for .shared/) ===
    # Copy academic LLM content to .shared/LLM_SYNTHESIS/ as reference material
    # Path-specific content is copied during individual package extraction
    if LLM_PUBLICATIONS_DIR.exists():
        result["categories"]["LLM_SYNTHESIS"] = {"count": 0, "files": []}
        dest_llm_dir = SHARED_OUTPUT_DIR / "LLM_SYNTHESIS"

        if not dry_run:
            dest_llm_dir.mkdir(parents=True, exist_ok=True)

        # Copy all academic LLM publications to .shared/ as reference
        academic_dir = LLM_PUBLICATIONS_DIR / "academic"
        if academic_dir.exists():
            for src_file in academic_dir.iterdir():
                if src_file.is_file():
                    result["categories"]["LLM_SYNTHESIS"]["count"] += 1
                    result["categories"]["LLM_SYNTHESIS"]["files"].append(src_file.name)

                    if not dry_run:
                        try:
                            shutil.copy2(src_file, dest_llm_dir / src_file.name)
                            result["files_copied"].append(f"LLM_SYNTHESIS/{src_file.name}")
                        except Exception as e:
                            result["errors"].append(f"Failed to copy LLM_SYNTHESIS/{src_file.name}: {e}")

    # Calculate totals
    total_files = sum(cat.get("count", 0) for cat in result["categories"].values())
    total_size = sum(cat.get("size_bytes", 0) for cat in result["categories"].values())

    result["statistics"] = {
        "total_files": total_files,
        "total_size_bytes": total_size,
        "total_size_human": format_size(total_size),
    }

    result["message"] = f"{'Would sync' if dry_run else 'Synced'} {len(result['files_copied']) + len(result['templates_copied'])} files to {SHARED_OUTPUT_DIR}"

    return result


def generate_shared_sync_report(result: Dict) -> str:
    """Generate a report of shared content sync."""

    lines = [
        "=" * 70,
        ".SHARED/ CONTENT SYNC REPORT",
        f"Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 70,
        "",
        f"Output:  {result['output_dir']}",
    ]

    if result.get("statistics"):
        stats = result["statistics"]
        lines.append(f"Files:   {stats['total_files']}")
        lines.append(f"Size:    {stats['total_size_human']}")

    # Show template status
    if result.get("templates_copied"):
        lines.extend(["", "## Core Templates (from planning/reviewer_templates/)", ""])
        for t in result["templates_copied"]:
            lines.append(f"  - {t}")

    # Show staleness report
    staleness = result.get("staleness_report", {})
    if staleness:
        if staleness.get("stale_files"):
            lines.extend(["", "## WARNING: Stale Files in .shared/", ""])
            for sf in staleness["stale_files"]:
                lines.append(f"  - {sf['file']}: template newer ({sf['template_mtime'][:10]})")
        if staleness.get("missing_in_shared"):
            lines.extend(["", "## Missing in .shared/ (will be created)", ""])
            for mf in staleness["missing_in_shared"]:
                lines.append(f"  - {mf}")
        if staleness.get("missing_templates"):
            lines.extend(["", "## ERROR: Missing templates in planning/reviewer_templates/", ""])
            for mt in staleness["missing_templates"]:
                lines.append(f"  - {mt}")

    lines.extend(["", "## By Category", "", "| Category | Files | Size |", "|----------|-------|------|"])

    for category, info in result.get("categories", {}).items():
        count = info.get("count", 0)
        size = format_size(info.get("size_bytes", 0))
        lines.append(f"| {category}/ | {count} | {size} |")

    lines.append("")

    if result["dry_run"]:
        lines.append("Status: DRY RUN (no files written)")
    else:
        total_synced = len(result.get('files_copied', [])) + len(result.get('templates_copied', []))
        lines.append(f"Status: SYNCED ({total_synced} files)")

    if result.get("errors"):
        lines.extend(["", f"Errors: {len(result['errors'])}"])
        for err in result["errors"][:5]:
            lines.append(f"  - {err}")

    lines.extend([
        "",
        "---",
        "",
        ".shared/ is now a self-contained minimum viable package.",
        "Templates source: planning/reviewer_templates/",
        "Send this directory first to any reviewer.",
    ])

    return "\n".join(lines)


# === PDF LAYER EXTRACTION ===

# Map publication paths to their PDF source directories
PDF_SOURCE_MAP = {
    "arxiv": ["submissions/arxiv/"],
    "journal": ["submissions/journal/", "submissions/arxiv/"],
    "workshop": ["submissions/workshop/"],
    # Other paths don't have PDFs yet - add as they're generated
}


def collect_pdf_files() -> Dict[str, List[Path]]:
    """
    Collect all PDF files from WHITE-PAPER, organized by publication path.

    Returns:
        Dict mapping path names to lists of PDF files
    """
    collected: Dict[str, List[Path]] = {}

    for path_name, source_dirs in PDF_SOURCE_MAP.items():
        pdfs = []
        for source_dir in source_dirs:
            dir_path = WHITE_PAPER_ROOT / source_dir
            if dir_path.exists():
                pdfs.extend(dir_path.glob("**/*.pdf"))
                pdfs.extend(dir_path.glob("**/*.PDF"))
        collected[path_name] = sorted(set(pdfs))  # Remove duplicates

    # Also collect any PDFs from other locations
    other_pdfs = []
    for pdf in WHITE_PAPER_ROOT.glob("**/*.pdf"):
        # Skip if already categorized
        already_collected = any(pdf in files for files in collected.values())
        # Skip packages directory (we're creating that)
        if "packages" in str(pdf):
            continue
        if not already_collected:
            other_pdfs.append(pdf)

    if other_pdfs:
        collected["other"] = sorted(other_pdfs)

    return collected


def generate_pdf_readme(collected: Dict[str, List[Path]]) -> str:
    """Generate README.md for the PDF layer."""

    total_files = sum(len(files) for files in collected.values())
    total_size = sum(calculate_total_size(files) for files in collected.values())

    lines = [
        "# PDF Layer",
        "",
        f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        f"**Total PDFs:** {total_files}",
        f"**Total Size:** {format_size(total_size)}",
        "",
        "---",
        "",
        "## Purpose",
        "",
        "This directory contains PDF files separated from the main review packages.",
        "The text-based packages in `../` are lightweight (~100-700 KB each) and can",
        "be processed by AI reviewers. PDFs are kept separate to manage file sizes.",
        "",
        "---",
        "",
        "## Contents",
        "",
        "| Path | Files | Size | Description |",
        "|------|-------|------|-------------|",
    ]

    path_descriptions = {
        "arxiv": "arXiv preprint PDFs",
        "journal": "Journal submission PDFs",
        "workshop": "Workshop paper PDFs",
        "other": "Other PDFs (figures, etc.)",
    }

    for path_name, files in collected.items():
        if files:
            size = format_size(calculate_total_size(files))
            desc = path_descriptions.get(path_name, "")
            lines.append(f"| {path_name}/ | {len(files)} | {size} | {desc} |")

    lines.extend([
        "",
        f"**Total:** {total_files} files, {format_size(total_size)}",
        "",
        "---",
        "",
        "## File Listing",
        "",
    ])

    for path_name, files in collected.items():
        if files:
            lines.append(f"### {path_name}/")
            lines.append("")
            for f in files:
                rel_path = f.relative_to(WHITE_PAPER_ROOT)
                size = format_size(f.stat().st_size)
                lines.append(f"- `{f.name}` ({size})")
                lines.append(f"  - Source: `{rel_path}`")
            lines.append("")

    lines.extend([
        "---",
        "",
        "## Usage",
        "",
        "To include PDFs in a review package, use:",
        "",
        "```bash",
        "py 2_package_review.py arxiv --include-pdf",
        "```",
        "",
        "Or send this PDF layer separately alongside the text packages.",
        "",
        "---",
        "",
        "*PDF layer extracted from WHITE-PAPER/ for reviewer distribution.*",
    ])

    return "\n".join(lines)


def extract_pdf_layer(output_dir: Optional[Path] = None, dry_run: bool = False) -> Dict:
    """
    Extract all PDFs to a separate layer: packages/pdf/{path}/

    Args:
        output_dir: Where to write (default: reviewers/packages/pdf/)
        dry_run: Preview without writing files

    Returns:
        Dict with extraction results
    """
    if output_dir is None:
        output_dir = PDF_OUTPUT_DIR

    collected = collect_pdf_files()

    total_files = sum(len(files) for files in collected.values())
    total_size = sum(calculate_total_size(files) for files in collected.values())

    result = {
        "mode": "pdf_layer",
        "output_dir": str(output_dir),
        "dry_run": dry_run,
        "statistics": {
            "total_files": total_files,
            "total_size_bytes": total_size,
            "total_size_human": format_size(total_size),
        },
        "categories": {},
        "files_copied": [],
        "errors": [],
    }

    for path_name, files in collected.items():
        result["categories"][path_name] = {
            "count": len(files),
            "size_bytes": calculate_total_size(files),
            "files": [str(f.relative_to(WHITE_PAPER_ROOT)) for f in files]
        }

    if dry_run:
        result["message"] = "Dry run - no files written"
        return result

    # Create output directory
    try:
        output_dir.mkdir(parents=True, exist_ok=True)
    except Exception as e:
        result["errors"].append(f"Failed to create output dir: {e}")
        return result

    # Copy PDFs organized by path
    for path_name, files in collected.items():
        path_dir = output_dir / path_name
        path_dir.mkdir(parents=True, exist_ok=True)

        for src_file in files:
            dst_file = path_dir / src_file.name
            try:
                shutil.copy2(src_file, dst_file)
                result["files_copied"].append(f"{path_name}/{src_file.name}")
            except Exception as e:
                result["errors"].append(f"Failed to copy {src_file.name}: {e}")

    # Generate and write README
    readme_content = generate_pdf_readme(collected)
    readme_path = output_dir / "README.md"
    try:
        readme_path.write_text(readme_content, encoding="utf-8")
        result["readme_path"] = str(readme_path)
    except Exception as e:
        result["errors"].append(f"Failed to write README: {e}")

    result["message"] = f"Extracted {total_files} PDFs ({format_size(total_size)}) to {output_dir}"

    return result


def generate_pdf_extraction_report(result: Dict) -> str:
    """Generate a report of PDF extraction results."""

    lines = [
        "=" * 70,
        "PDF LAYER EXTRACTION REPORT",
        f"Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 70,
        "",
    ]

    if result.get("error"):
        lines.append(f"ERROR: {result['error']}")
        return "\n".join(lines)

    stats = result["statistics"]

    lines.append(f"Output:  {result['output_dir']}")
    lines.append(f"Files:   {stats['total_files']}")
    lines.append(f"Size:    {stats['total_size_human']}")
    lines.append("")

    lines.append("## By Publication Path")
    lines.append("")
    lines.append("| Path | Files | Size |")
    lines.append("|------|-------|------|")

    for path_name, info in result["categories"].items():
        if info["count"] > 0:
            size = format_size(info["size_bytes"])
            lines.append(f"| {path_name} | {info['count']} | {size} |")

    lines.append("")

    if result["dry_run"]:
        lines.append("Status: DRY RUN (no files written)")
    else:
        lines.append(f"Status: EXTRACTED ({len(result.get('files_copied', []))} files copied)")

    if result.get("errors"):
        lines.append("")
        lines.append(f"Errors: {len(result['errors'])}")
        for err in result["errors"][:5]:
            lines.append(f"  - {err}")

    lines.extend([
        "",
        "---",
        "",
        "The PDF layer is separate from text packages to keep them lightweight.",
        "Send PDFs separately or use --include-pdf to embed in specific packages.",
    ])

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Extract review packages from WHITE-PAPER for AI reviewers",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Available paths: {', '.join(PUBLICATION_PATHS)}

Examples:
  py 2_package_review.py workshop          # Extract workshop package (with figures)
  py 2_package_review.py workshop arxiv    # Extract multiple packages
  py 2_package_review.py --all             # Extract ALL 8 packages
  py 2_package_review.py arxiv --no-figures       # Exclude figure specs
  py 2_package_review.py workshop --dry-run       # Preview only
  py 2_package_review.py workshop --output ./FOR_OPUS  # Custom output

Expected package sizes (with figures):
  workshop:        ~120 KB
  arxiv:           ~500 KB
  journal:         ~665 KB
  popular_science: ~30 KB
  education:       ~40 KB
  policy:          ~30 KB
  funding:         ~70 KB
  media:           ~35 KB

PDF Layer (separate from text packages):
  py 2_package_review.py --extract-pdfs    # Extract to packages/pdf/
  py 2_package_review.py --extract-pdfs --dry-run  # Preview

Shared Content (.shared/ self-contained core):
  NOTE: .shared/ auto-syncs when extracting packages (--all or specific paths)
  py 2_package_review.py --sync-shared     # Sync ONLY .shared/ (no packages)
  py 2_package_review.py --all --no-sync-shared  # Skip auto-sync

Output: packages/pdf/arxiv/, packages/pdf/journal/, etc. (~14 MB total)
        packages/v4/.shared/ (self-contained reviewer core package)
        """
    )

    # Positional arguments for paths
    parser.add_argument("paths", nargs="*", choices=PUBLICATION_PATHS + ["all"],
                        help="Publication paths to extract (or 'all')")

    # Extraction options
    parser.add_argument("--all", action="store_true",
                        help="Extract ALL publication paths")
    parser.add_argument("--no-figures", action="store_true",
                        help="Exclude figure specification files (figures included by default)")
    parser.add_argument("--include-pdf", action="store_true",
                        help="Include PDF files in text packages (adds ~14MB for arxiv)")
    parser.add_argument("--extract-pdfs", action="store_true",
                        help="Extract PDFs to separate layer: packages/pdf/")
    parser.add_argument("--sync-shared", action="store_true",
                        help="Sync shared content to .shared/ (self-contained core package)")
    parser.add_argument("--no-sync-shared", action="store_true",
                        help="Skip automatic .shared/ sync when extracting packages")

    # Output options
    parser.add_argument("--output", type=Path, default=None,
                        help="Custom output directory (default: reviewers/packages/)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview extraction without writing files")

    # Report options
    parser.add_argument("--json", action="store_true",
                        help="Output results as JSON")
    parser.add_argument("--status", action="store_true",
                        help="Show status report without extracting")

    args = parser.parse_args()

    # Handle --status mode
    if args.status:
        print(generate_status_report())
        return

    # Handle --sync-shared mode
    if args.sync_shared:
        result = sync_shared_content(dry_run=args.dry_run)
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            print(generate_shared_sync_report(result))
        return

    # Handle --extract-pdfs mode
    if args.extract_pdfs:
        result = extract_pdf_layer(output_dir=args.output, dry_run=args.dry_run)
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            print(generate_pdf_extraction_report(result))
        return

    # Determine which paths to extract
    if args.all or "all" in args.paths:
        paths_to_extract = PUBLICATION_PATHS
    elif args.paths:
        paths_to_extract = [p for p in args.paths if p != "all"]
    else:
        # No paths specified - show status
        print(generate_status_report())
        return

    # AUTO-SYNC .shared/ before extracting packages (unless --no-sync-shared)
    shared_result = None
    if not args.no_sync_shared:
        print("=" * 60)
        print("STEP 1: Syncing .shared/ (core reviewer package)")
        print("=" * 60)
        shared_result = sync_shared_content(dry_run=args.dry_run)
        print(generate_shared_sync_report(shared_result))
        print()
        print("=" * 60)
        print("STEP 2: Extracting path-specific packages")
        print("=" * 60)

    # Extract packages (figures included by default, --no-figures to exclude)
    include_figures = not args.no_figures
    results = []
    for path_name in paths_to_extract:
        result = extract_package(
            path_name=path_name,
            output_dir=args.output,
            include_figures=include_figures,
            include_pdf=args.include_pdf,
            dry_run=args.dry_run
        )
        results.append(result)

    # Output results
    if args.json:
        combined = {
            "shared_sync": shared_result,
            "packages": results
        }
        print(json.dumps(combined, indent=2))
    else:
        print(generate_extraction_report(results))


if __name__ == "__main__":
    main()
