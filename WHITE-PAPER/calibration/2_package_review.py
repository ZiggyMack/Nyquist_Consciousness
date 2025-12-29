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
├── submissions/{path}/          # Core submission materials
├── blueprints/                  # Blueprint for this path
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
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Set
from dataclasses import dataclass, field

# === PATH CONSTANTS ===
WHITE_PAPER_ROOT = Path(__file__).parent.parent  # WHITE-PAPER/
REPO_ROOT = WHITE_PAPER_ROOT.parent              # Nyquist_Consciousness/
DEFAULT_OUTPUT_DIR = WHITE_PAPER_ROOT / "reviewers" / "packages" / "v4"  # v4 packages (Run 023d IRON CLAD + Oobleck Effect)
PDF_OUTPUT_DIR = WHITE_PAPER_ROOT / "reviewers" / "packages" / "pdf"
LLM_SYNTHESIS_DIR = WHITE_PAPER_ROOT / "reviewers" / "LLM_BOOK_SYNTHESIS"

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

# === NOTEBOOKLM INTEGRATION ===
# Map which LLM_BOOK_SYNTHESIS files go to which publication paths
NOTEBOOKLM_INTEGRATION = {
    "arxiv": [
        "README.md",  # Master synthesis (173KB)
        "INDEX.md",   # Content guide
        "Measuring AI Identity as a Dynamical System - An Empirical Framework Based on 750 Experiments Across 25 Models.md",
        "Technical Report - Comparative Analysis of AI Provider Identity Stability.md",
        "Decoding Ai Identity Drift.png",    # Infographic
        "NotebookLM Mind Map (1).png",       # Concept map
    ],
    "journal": [
        "README.md",  # Master synthesis (173KB)
        "INDEX.md",   # Content guide
        "Measuring AI Identity as a Dynamical System - An Empirical Framework Based on 750 Experiments Across 25 Models.md",
        "Technical Report - Comparative Analysis of AI Provider Identity Stability.md",
        "Decoding Ai Identity Drift.png",    # Infographic
        "NotebookLM Mind Map (1).png",       # Concept map
    ],
    "workshop": [
        "Briefing Document - The Nyquist Consciousness Framework for AI Identity Dynamics.md",
    ],
    "popular_science": [
        "Measuring an AI's Identity - Charting Personality Drift with an Engineer's Toolkit.md",
    ],
    "education": [
        "Decoding AI Identity - A Visual Guide to Model Waveforms.md",
    ],
    "policy": [
        "Briefing Document - The Nyquist Consciousness Framework for AI Identity Dynamics.md",
    ],
    "funding": [
        "Briefing Document - The Nyquist Consciousness Framework for AI Identity Dynamics.md",
        "Technical Report - Comparative Analysis of AI Provider Identity Stability.md",
    ],
    "media": [
        "Measuring an AI's Identity - Charting Personality Drift with an Engineer's Toolkit.md",
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
    theory=["MINIMUM_PUBLISHABLE_CLAIMS.md"],
    guides=["summary_statistics.md"],
    references=[],
    figures=["ascii/ascii_workshop_*.md", "visual_index.md"],
    planning=["OPUS_REVIEW_BRIEF.md", "NOVAS_OVERCLAIMING_PREVENTION.md", "METHODOLOGY_DOMAINS.md"],
    reviewers=["phase1/Nyquist_workshop_paper*.md", "phase2/Workshop_paper*.md"],
    reading_order=[
        "submissions/workshop/README.md",
        "submissions/blueprints/WORKSHOP_BLUEPRINT.md",
        "theory/MINIMUM_PUBLISHABLE_CLAIMS.md",
        "guides/summary_statistics.md",
    ]
)

ARXIV_CONTENT = PathContent(
    name="arxiv",
    description="arXiv preprint package (25-35 pages, full methodology)",
    target_venue="cs.AI Preprint",
    submissions=["arxiv/"],
    blueprints=["ARXIV_BLUEPRINT.md"],
    theory=["*.md"],  # All theory docs
    guides=["*.md"],  # All guides
    references=["references.md", "references.bib"],
    figures=["conceptual/", "ascii/", "experiments/", "visual_index.md"],  # Organized: conceptual (theory figs), ascii (workshop), experiments/run023 (latest)
    planning=["OPUS_REVIEW_BRIEF.md", "PUBLICATION_PIPELINE_MASTER.md", "NOVAS_OVERCLAIMING_PREVENTION.md", "METHODOLOGY_DOMAINS.md"],
    reviewers=["phase1/NOVA_S7_REVIEW.md", "phase3/*.md"],
    reading_order=[
        "submissions/arxiv/README.md",
        "submissions/blueprints/ARXIV_BLUEPRINT.md",
        "theory/MINIMUM_PUBLISHABLE_CLAIMS.md",
        "theory/THEORY_SECTION.md",
        "guides/summary_statistics.md",
        "references/references.md",
    ]
)

JOURNAL_CONTENT = PathContent(
    name="journal",
    description="Journal paper package (Nature MI, comprehensive)",
    target_venue="Nature Machine Intelligence",
    submissions=["journal/", "arxiv/"],  # Build on arxiv
    blueprints=["JOURNAL_BLUEPRINT.md", "ARXIV_BLUEPRINT.md"],
    theory=["*.md"],
    guides=["*.md"],
    references=["references.md", "references.bib"],
    figures=["conceptual/", "ascii/", "experiments/", "visual_index.md"],  # Organized: conceptual (theory figs), ascii (workshop), experiments/run023 (latest)
    planning=["OPUS_REVIEW_BRIEF.md", "PUBLICATION_PIPELINE_MASTER.md", "NOVAS_OVERCLAIMING_PREVENTION.md", "METHODOLOGY_DOMAINS.md"],
    reviewers=["phase1/*.md", "phase2/*.md", "phase3/*.md"],
    reading_order=[
        "submissions/journal/README.md",
        "submissions/blueprints/JOURNAL_BLUEPRINT.md",
        "theory/MINIMUM_PUBLISHABLE_CLAIMS.md",
        "theory/THEORY_SECTION.md",
    ]
)

POPULAR_SCIENCE_CONTENT = PathContent(
    name="popular_science",
    description="Popular science article package (Atlantic/Wired style)",
    target_venue="The Atlantic / Wired / Scientific American",
    submissions=["popular_science/"],
    blueprints=[],
    theory=[],
    guides=["summary_statistics.md"],
    references=[],
    figures=[],
    planning=["OPUS_REVIEW_BRIEF.md", "NOVAS_OVERCLAIMING_PREVENTION.md"],
    reviewers=[],
    reading_order=[
        "submissions/popular_science/README.md",
        "submissions/popular_science/POPULAR_SCIENCE_FINAL.md",
        "guides/summary_statistics.md",
    ]
)

EDUCATION_CONTENT = PathContent(
    name="education",
    description="Educational materials package (OER/Coursera)",
    target_venue="Open Educational Resources / Coursera",
    submissions=["education/"],
    blueprints=[],
    theory=["MINIMUM_PUBLISHABLE_CLAIMS.md"],
    guides=["summary_statistics.md"],
    references=[],
    figures=[],
    planning=["NOVAS_OVERCLAIMING_PREVENTION.md"],
    reviewers=[],
    reading_order=[
        "submissions/education/README.md",
        "submissions/education/EDUCATION_FINAL.md",
        "theory/MINIMUM_PUBLISHABLE_CLAIMS.md",
    ]
)

POLICY_CONTENT = PathContent(
    name="policy",
    description="Policy briefing package (Think tanks)",
    target_venue="Brookings / Center for AI Safety / EU AI Office",
    submissions=["policy/"],
    blueprints=[],
    theory=[],
    guides=["summary_statistics.md"],
    references=[],
    figures=[],
    planning=["NOVAS_OVERCLAIMING_PREVENTION.md"],
    reviewers=[],
    reading_order=[
        "submissions/policy/README.md",
        "submissions/policy/POLICY_FINAL.md",
        "guides/summary_statistics.md",
    ]
)

FUNDING_CONTENT = PathContent(
    name="funding",
    description="Funding proposal package (NSF/DARPA)",
    target_venue="NSF / DARPA / Open Philanthropy",
    submissions=["funding/"],
    blueprints=[],
    theory=["MINIMUM_PUBLISHABLE_CLAIMS.md", "B-CRUMBS.md"],
    guides=["summary_statistics.md", "REPRODUCIBILITY_README.md"],
    references=[],
    figures=[],
    planning=["NOVAS_OVERCLAIMING_PREVENTION.md", "METHODOLOGY_DOMAINS.md"],
    reviewers=[],
    reading_order=[
        "submissions/funding/README.md",
        "submissions/funding/FUNDING_FINAL.md",
        "theory/MINIMUM_PUBLISHABLE_CLAIMS.md",
    ]
)

MEDIA_CONTENT = PathContent(
    name="media",
    description="Media/press package (Press releases, podcasts)",
    target_venue="Press / Podcasts / TED",
    submissions=["media/", "popular_science/"],
    blueprints=[],
    theory=[],
    guides=["summary_statistics.md"],
    references=[],
    figures=[],
    planning=["NOVAS_OVERCLAIMING_PREVENTION.md"],
    reviewers=[],
    reading_order=[
        "submissions/media/README.md",
        "submissions/media/MEDIA_FINAL.md",
        "submissions/popular_science/POPULAR_SCIENCE_FINAL.md",
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
    include_pdf: bool
) -> str:
    """Generate PACKAGE_MANIFEST.md content."""

    total_files = sum(len(files) for files in collected.values())
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
    for category, files in collected.items():
        for src_file in files:
            # Calculate relative path from WHITE_PAPER_ROOT
            rel_path = src_file.relative_to(WHITE_PAPER_ROOT)
            dst_file = output_dir / rel_path

            try:
                dst_file.parent.mkdir(parents=True, exist_ok=True)
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

    # Generate and write manifest
    manifest_content = generate_manifest(
        path_content, collected, output_dir, include_figures, include_pdf
    )
    manifest_path = output_dir / "PACKAGE_MANIFEST.md"
    try:
        manifest_path.write_text(manifest_content, encoding="utf-8")
        result["manifest_path"] = str(manifest_path)
    except Exception as e:
        result["errors"].append(f"Failed to write manifest: {e}")

    result["message"] = f"Extracted {total_files} files ({format_size(total_size)}) to {output_dir}"

    # Copy NotebookLLM synthesis files if available
    if not dry_run:
        llm_result = copy_notebooklm_synthesis(path_name, output_dir)
        if llm_result.get("files_copied"):
            result["llm_synthesis_copied"] = llm_result["files_copied"]
        if llm_result.get("errors"):
            result["errors"].extend(llm_result["errors"])

    return result


def copy_notebooklm_synthesis(path_name: str, output_dir: Path) -> Dict:
    """
    Copy relevant NotebookLLM synthesis files to the package's LLM_SYNTHESIS/ directory.

    Args:
        path_name: Publication path (e.g., "arxiv", "workshop")
        output_dir: Package output directory

    Returns:
        Dict with files_copied and errors lists
    """
    result = {"files_copied": [], "errors": []}

    if path_name not in NOTEBOOKLM_INTEGRATION:
        return result

    synthesis_dir = output_dir / "LLM_SYNTHESIS"

    try:
        synthesis_dir.mkdir(parents=True, exist_ok=True)
    except Exception as e:
        result["errors"].append(f"Failed to create LLM_SYNTHESIS dir: {e}")
        return result

    for filename in NOTEBOOKLM_INTEGRATION[path_name]:
        src_file = LLM_SYNTHESIS_DIR / filename
        if src_file.exists():
            dst_file = synthesis_dir / filename
            try:
                shutil.copy2(src_file, dst_file)
                result["files_copied"].append(filename)
            except Exception as e:
                result["errors"].append(f"Failed to copy {filename}: {e}")
        else:
            result["errors"].append(f"LLM synthesis file not found: {filename}")

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

Output: packages/pdf/arxiv/, packages/pdf/journal/, etc. (~14 MB total)
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
        print(json.dumps(results, indent=2))
    else:
        print(generate_extraction_report(results))


if __name__ == "__main__":
    main()
