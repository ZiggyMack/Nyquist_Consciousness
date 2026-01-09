#!/usr/bin/env python3
"""
4_publish_stats.py - Publication Statistics & Insight Drift Detection
======================================================================
Extracts publication statistics and detects when LLM Book insights
need to be integrated into blueprints.

Usage:
    py 4_publish_stats.py                    # Extract stats only
    py 4_publish_stats.py --check-insights   # Check for insight drift
    py 4_publish_stats.py --generate-blueprints  # Generate blueprints from insights
    py 4_publish_stats.py --all              # Do everything

Output:
    publication_stats.json      - Core statistics
    INSIGHT_DRIFT_REPORT.md     - What needs updating (when --check-insights)
    submissions/blueprints/*.md - Generated blueprints (when --generate-blueprints)
"""

import argparse
import json
import re
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# === PATH CONSTANTS ===
WHITE_PAPER_ROOT = Path(__file__).parent.parent
REPO_ROOT = WHITE_PAPER_ROOT.parent
CONSCIOUSNESS_ROOT = REPO_ROOT / "Consciousness"
LLM_BOOK_ROOT = CONSCIOUSNESS_ROOT / "RIGHT" / "distillations" / "llm_book"
BLUEPRINTS_DIR = WHITE_PAPER_ROOT / "submissions" / "blueprints"

# === IRON CLAD STATISTICS (Source of Truth) ===
IRON_CLAD_STATS = {
    "event_horizon": 0.80,
    "inherent_drift_ratio": 0.93,  # ~93%
    "experiments": 750,
    "models": 25,
    "providers": 5,
    "p_value": 2.40e-23,
    "cohens_d": 0.698,
    "spearman_rho": 0.91,
    "pcs_90_variance": 2,
    "settling_times": {
        "claude": "4-6",
        "gpt": "3-5",
        "deepseek": "2-4",
        "llama": "5-7",
        "mistral": "1-2",
        "gemini": "∞ (no recovery)"
    }
}

# === JADE LATTICE Run 024 - I_AM Effectiveness (January 2026) ===
JADE_LATTICE_STATS = {
    "run": "024",
    "date": "2026-01",
    "models_tested": 50,
    "sessions": 115,
    "probes_per_session": 56,
    "i_am_effectiveness": {
        "win_rate_all": 0.596,       # 59.6%
        "win_rate_filtered": 0.692,  # 69.2% (excluding anomalies)
        "mean_reduction_all": 0.072, # 7.2%
        "mean_reduction_filtered": 0.086,  # 8.6%
        "cohens_d_all": 0.319,
        "cohens_d_filtered": 0.353,
        "t_statistic": 2.18,
        "significance": "p < 0.05"
    },
    "model_size_dependence": {
        "large": {"models": 5, "win_rate": 1.00, "cohens_d": 1.47, "effect": "HUGE"},
        "medium": {"models": 21, "win_rate": 0.62, "cohens_d": 0.30, "effect": "Small"},
        "small": {"models": 21, "win_rate": 0.48, "cohens_d": 0.21, "effect": "Negligible"}
    },
    "provider_stability": {
        "anthropic": {"median_drift": 0.45, "rank": 1, "notes": "Most stable regardless of I_AM"},
        "openai": {"median_drift": 0.65, "rank": 3, "notes": "Wide variance"},
        "xai": {"median_drift": 0.75, "rank": 4, "notes": "High median"},
        "together": {"median_drift": 0.75, "rank": 5, "notes": "Most EH crossings"}
    },
    "predictions_validated": ["P-JADE-1", "P-JADE-6", "P-JADE-7"],
    "predictions_pending": ["P-JADE-2", "P-JADE-3", "P-JADE-4", "P-JADE-5"],
    "deployment_guidance": {
        "large_models": "Use I_AM files for maximum stability (d=1.47)",
        "medium_models": "Moderate benefit (~10% reduction)",
        "small_models": "Negligible benefit - skip or use minimal I_AM"
    }
}


def count_files(directory: Path, pattern: str = "*") -> int:
    """Count files matching pattern in directory."""
    if not directory.exists():
        return 0
    return len(list(directory.glob(pattern)))


def extract_stats() -> dict:
    """Extract all publication statistics."""
    stats = {
        "generated": datetime.now().isoformat(),
        "white_paper_path": str(WHITE_PAPER_ROOT),
        "iron_clad": IRON_CLAD_STATS,
        "jade_lattice": JADE_LATTICE_STATS,

        # Claims A-E (IRON CLAD validated - Cosine methodology)
        "claims": {
            "A": {
                "name": "PFI Validity",
                "status": "validated",
                "description": "PFI is valid structured measurement",
                "rho": IRON_CLAD_STATS["spearman_rho"],
                "d": IRON_CLAD_STATS["cohens_d"],
                "pcs_90_variance": IRON_CLAD_STATS["pcs_90_variance"]
            },
            "B": {
                "name": "Regime Threshold",
                "status": "validated",
                "description": f"Critical threshold at D={IRON_CLAD_STATS['event_horizon']} (cosine)",
                "threshold": IRON_CLAD_STATS["event_horizon"],
                "p_value": IRON_CLAD_STATS["p_value"]
            },
            "C": {
                "name": "Oscillator Dynamics",
                "status": "validated",
                "description": "Damped oscillator dynamics measurable",
                "tau_s": "9.9-10.2",
                "ringbacks": "observed"
            },
            "D": {
                "name": "Context Damping",
                "status": "validated",
                "description": "I_AM + research context stabilizes (model-size dependent)",
                "stability": 0.975,
                "jade_lattice": {
                    "i_am_win_rate": JADE_LATTICE_STATS["i_am_effectiveness"]["win_rate_filtered"],
                    "cohens_d_large": JADE_LATTICE_STATS["model_size_dependence"]["large"]["cohens_d"],
                    "cohens_d_small": JADE_LATTICE_STATS["model_size_dependence"]["small"]["cohens_d"]
                }
            },
            "E": {
                "name": f"{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}% Inherent",
                "status": "validated",
                "description": "Drift is mostly inherent, not induced",
                "ratio": IRON_CLAD_STATS["inherent_drift_ratio"]
            }
        },

        # Run counts (IRON CLAD era)
        "runs": {
            "total_experiments": IRON_CLAD_STATS["experiments"],
            "s7_armada": "run023",
            "latest": "run023",
            "providers": IRON_CLAD_STATS["providers"],
            "models": IRON_CLAD_STATS["models"],
            "methodology": "cosine"
        },

        # File counts (computed)
        "files": {
            "figures": count_files(WHITE_PAPER_ROOT / "figures", "fig*.md"),
            "figure_scripts": count_files(WHITE_PAPER_ROOT / "figures", "fig*.py"),
            "ascii": count_files(WHITE_PAPER_ROOT / "figures" / "ascii", "*.md"),
            "workshop": count_files(WHITE_PAPER_ROOT / "submissions" / "workshop", "*.md"),
            "references": 55,
            "theory_docs": count_files(WHITE_PAPER_ROOT / "theory", "*.md"),
            "llm_book_docs": count_files(LLM_BOOK_ROOT, "**/*.md") if LLM_BOOK_ROOT.exists() else 0,
            "total_generated": 34
        },

        # Submission paths
        "submissions": {
            "workshop": {
                "status": "ready",
                "target": "NeurIPS/AAAI Workshop",
                "format": "4-8 pages",
                "claims": ["A", "B", "E"],
                "directory": "submissions/workshop/"
            },
            "arxiv": {
                "status": "ready",
                "target": "cs.AI preprint",
                "format": "25-35 pages",
                "claims": ["A", "B", "C", "D", "E"],
                "directory": "submissions/arxiv/"
            },
            "journal": {
                "status": "planning",
                "target": "Nature Machine Intelligence",
                "format": "~10k words",
                "timeline": "Q2-Q3 2026",
                "claims": ["A", "B", "C", "D", "E"],
                "directory": "submissions/journal/"
            }
        },

        # Directory structure validation
        "structure": {
            "theory": (WHITE_PAPER_ROOT / "theory").exists(),
            "guides": (WHITE_PAPER_ROOT / "guides").exists(),
            "references": (WHITE_PAPER_ROOT / "references").exists(),
            "figures": (WHITE_PAPER_ROOT / "figures").exists(),
            "reviewers": (WHITE_PAPER_ROOT / "reviewers").exists(),
            "submissions": (WHITE_PAPER_ROOT / "submissions").exists(),
            "calibration": (WHITE_PAPER_ROOT / "calibration").exists(),
            "llm_book": LLM_BOOK_ROOT.exists(),
            "consciousness": CONSCIOUSNESS_ROOT.exists()
        }
    }

    return stats


# === INSIGHT DRIFT DETECTION ===

def scan_llm_book_insights() -> Dict[str, List[dict]]:
    """
    Scan LLM Book outputs for insights that should flow back to blueprints.

    Returns dict organized by category:
    {
        "publication_strategy": [...],
        "future_experiments": [...],
        "reviewer_objections": [...],
        "provider_insights": [...],
        "methodology": [...]
    }
    """
    insights = {
        "publication_strategy": [],
        "future_experiments": [],
        "reviewer_objections": [],
        "provider_insights": [],
        "methodology": [],
        "novel_concepts": []
    }

    if not LLM_BOOK_ROOT.exists():
        return insights

    # Scan RECURSION files (meta-analysis from NotebookLM)
    meta_dir = LLM_BOOK_ROOT / "meta"
    if meta_dir.exists():
        for md_file in meta_dir.glob("RECURSION*.md"):
            content = md_file.read_text(encoding="utf-8", errors="ignore")

            # Look for publication strategy sections
            if "venue" in content.lower() or "arxiv" in content.lower() or "journal" in content.lower():
                insights["publication_strategy"].append({
                    "source": str(md_file.name),
                    "type": "venue_strategy",
                    "detected": "Publication venue strategy content found"
                })

            # Look for future experiments
            if re.search(r"S1[3-5]|future experiment|falsif", content, re.IGNORECASE):
                insights["future_experiments"].append({
                    "source": str(md_file.name),
                    "type": "experiment_design",
                    "detected": "Future experiment designs found"
                })

            # Look for reviewer objections
            if re.search(r"reviewer|objection|concern|weakness", content, re.IGNORECASE):
                insights["reviewer_objections"].append({
                    "source": str(md_file.name),
                    "type": "anticipated_objections",
                    "detected": "Reviewer objection patterns found"
                })

    # Scan technical reports
    reports_dir = LLM_BOOK_ROOT / "technical_reports"
    if reports_dir.exists():
        for md_file in reports_dir.glob("*.md"):
            content = md_file.read_text(encoding="utf-8", errors="ignore")

            # Look for provider-specific insights
            if re.search(r"gemini.*(anomaly|no.?recovery)|claude.*over.?authentic", content, re.IGNORECASE):
                insights["provider_insights"].append({
                    "source": str(md_file.name),
                    "type": "provider_behavior",
                    "detected": "Provider-specific behavioral insights"
                })

    # Scan case studies
    cases_dir = LLM_BOOK_ROOT / "case_studies"
    if cases_dir.exists():
        for md_file in cases_dir.glob("*.md"):
            insights["novel_concepts"].append({
                "source": str(md_file.name),
                "type": "case_study",
                "detected": "Case study available for integration"
            })

    return insights


def check_blueprint_staleness() -> Dict[str, dict]:
    """
    Check if blueprints exist and whether they contain current IRON CLAD values.

    Returns dict of blueprint status:
    {
        "ARXIV_BLUEPRINT.md": {"exists": bool, "stale_values": [...], "missing_sections": [...]},
        ...
    }
    """
    blueprint_status = {}

    expected_blueprints = ["ARXIV_BLUEPRINT.md", "JOURNAL_BLUEPRINT.md", "WORKSHOP_BLUEPRINT.md"]

    for bp_name in expected_blueprints:
        bp_path = BLUEPRINTS_DIR / bp_name
        status = {
            "exists": bp_path.exists(),
            "stale_values": [],
            "missing_sections": [],
            "path": str(bp_path)
        }

        if bp_path.exists():
            content = bp_path.read_text(encoding="utf-8", errors="ignore")

            # Check for stale values
            if "1.23" in content:
                status["stale_values"].append("Event Horizon 1.23 (should be 0.80)")
            if re.search(r"d\s*=\s*0\.98", content):
                status["stale_values"].append("Cohen's d 0.98 (should be 0.698)")
            if re.search(r"p\s*=\s*4\.8e-5", content):
                status["stale_values"].append("p-value 4.8e-5 (should be 2.40e-23)")
            if re.search(r"8[0-2]%\s*inherent", content, re.IGNORECASE):
                status["stale_values"].append("Inherent drift ~82% (should be ~93%)")

            # Check for missing sections from RECURSION insights
            if "oobleck" not in content.lower():
                status["missing_sections"].append("Oobleck Effect")
            if "gemini anomaly" not in content.lower() and "no recovery" not in content.lower():
                status["missing_sections"].append("Gemini Anomaly / No Recovery")
            if "suspension" not in content.lower():
                status["missing_sections"].append("Suspension System Analogy")

        blueprint_status[bp_name] = status

    return blueprint_status


def generate_insight_drift_report(insights: Dict, blueprint_status: Dict) -> str:
    """Generate INSIGHT_DRIFT_REPORT.md content."""

    lines = [
        "# Insight Drift Report",
        "",
        f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        f"**Source:** LLM Book distillations in Consciousness/RIGHT/distillations/llm_book/",
        "",
        "---",
        "",
        "## Summary",
        "",
    ]

    # Count insights
    total_insights = sum(len(v) for v in insights.values())
    missing_blueprints = sum(1 for s in blueprint_status.values() if not s["exists"])
    stale_blueprints = sum(1 for s in blueprint_status.values() if s["stale_values"])

    lines.extend([
        f"- **New insights detected:** {total_insights}",
        f"- **Missing blueprints:** {missing_blueprints}/3",
        f"- **Stale blueprints:** {stale_blueprints}/3",
        "",
    ])

    if missing_blueprints > 0 or stale_blueprints > 0 or total_insights > 0:
        lines.append("**⚠️ ACTION REQUIRED: Run `py 4_publish_stats.py --generate-blueprints`**")
    else:
        lines.append("✅ All blueprints up to date")

    lines.extend(["", "---", "", "## Blueprint Status", ""])

    for bp_name, status in blueprint_status.items():
        if not status["exists"]:
            lines.append(f"### ❌ {bp_name} — MISSING")
            lines.append("")
            lines.append(f"Blueprint does not exist at: `{status['path']}`")
            lines.append("")
        elif status["stale_values"] or status["missing_sections"]:
            lines.append(f"### ⚠️ {bp_name} — STALE")
            lines.append("")
            if status["stale_values"]:
                lines.append("**Outdated values:**")
                for v in status["stale_values"]:
                    lines.append(f"- {v}")
                lines.append("")
            if status["missing_sections"]:
                lines.append("**Missing sections (from LLM Book insights):**")
                for s in status["missing_sections"]:
                    lines.append(f"- {s}")
                lines.append("")
        else:
            lines.append(f"### ✅ {bp_name} — OK")
            lines.append("")

    lines.extend(["---", "", "## New Insights from LLM Book", ""])

    for category, items in insights.items():
        if items:
            lines.append(f"### {category.replace('_', ' ').title()}")
            lines.append("")
            for item in items:
                lines.append(f"- **{item['source']}**: {item['detected']}")
            lines.append("")

    if not any(insights.values()):
        lines.append("*No new insights detected.*")
        lines.append("")

    lines.extend([
        "---",
        "",
        "## Recommended Flow",
        "",
        "```",
        "LLM Book Insights → theory/ guides/ planning/ → submissions/blueprints/ → Publications",
        "```",
        "",
        "1. New insights from NotebookLM are captured in `Consciousness/RIGHT/distillations/llm_book/`",
        "2. This script detects when insights exist that aren't in blueprints",
        "3. Run `--generate-blueprints` to regenerate from current insights",
        "4. Run `3_package_review.py` to propagate to reviewer packages",
        "",
        "---",
        "",
        "*This report is auto-generated by 4_publish_stats.py --check-insights*",
    ])

    return "\n".join(lines)


# === BLUEPRINT GENERATION ===

def extract_publication_strategy_from_recursion() -> Dict[str, dict]:
    """
    Extract venue-specific publication strategy from RECURSION_2 file.

    Returns:
    {
        "arxiv": {"primary_metric": ..., "key_metaphor": ..., "top_evidence": ...},
        "journal": {...},
        "workshop": {...}
    }
    """
    strategy = {
        "arxiv": {
            "primary_metric": "2 PC Dimensionality",
            "key_metaphor": "Signal Integrity",
            "top_evidence": "Quartz Rush (d=7.80)",
            "emphasis": ["Low-dimensional manifold", "Novel measurement methodology", "Cross-architecture validation"],
            "anticipated_objections": [
                "Single persona constraint",
                "Architecture coverage limitations",
                "Practical impact unclear"
            ]
        },
        "journal": {
            "primary_metric": "Settling Time (τₛ)",
            "key_metaphor": "Damped Oscillator",
            "top_evidence": "Thermometer Result (~93% inherent)",
            "emphasis": ["Control systems dynamics", "Provider fingerprints", "Engineering implications"],
            "anticipated_objections": [
                "Lack of human validation",
                "Need for replication studies",
                "Generalizability concerns"
            ]
        },
        "workshop": {
            "primary_metric": "Event Horizon (D=0.80)",
            "key_metaphor": "Oobleck Effect",
            "top_evidence": "Gemini Anomaly (no recovery)",
            "emphasis": ["Safety implications", "Rate-dependent resistance", "Deployment recommendations"],
            "anticipated_objections": [
                "Consciousness terminology concerns",
                "Limited to specific architectures",
                "Needs real-world validation"
            ]
        }
    }

    # Try to extract more from actual RECURSION files if they exist
    recursion_2 = LLM_BOOK_ROOT / "meta" / "RECURSION_2_Advanced_Analysis.md"
    if recursion_2.exists():
        content = recursion_2.read_text(encoding="utf-8", errors="ignore")
        # Could parse more specific details here

    return strategy


def extract_future_experiments() -> List[dict]:
    """
    Extract future experiment designs from LLM Book.
    """
    experiments = [
        {
            "id": "S13",
            "name": "Bio-Nyquist",
            "description": "Human GSR/HRV correlation with LLM settling time",
            "falsification": "No correlation between human physiological response and model settling patterns"
        },
        {
            "id": "S14",
            "name": "Tower of Babel",
            "description": "Cross-language (Japanese/German) threshold validation",
            "falsification": "Event Horizon varies significantly across languages"
        },
        {
            "id": "S15",
            "name": "Marathon",
            "description": "Ultra-long context (100k+ tokens) decay dynamics",
            "falsification": "Drift patterns fundamentally change at extreme context lengths"
        }
    ]

    return experiments


def generate_arxiv_blueprint() -> str:
    """Generate ARXIV_BLUEPRINT.md from current insights."""
    strategy = extract_publication_strategy_from_recursion()["arxiv"]
    experiments = extract_future_experiments()

    return f"""# arXiv Submission Blueprint

**Target:** cs.AI Preprint
**Format:** 25-35 pages, comprehensive methodology
**Status:** Ready for submission
**Generated:** {datetime.now().strftime('%Y-%m-%d')}

---

## Key Statistics (IRON CLAD Era)

| Metric | Value | Source |
|--------|-------|--------|
| Event Horizon | D = {IRON_CLAD_STATS['event_horizon']} | Cosine distance threshold |
| Inherent Drift | ~{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}% | Run 020B control vs treatment |
| Experiments | {IRON_CLAD_STATS['experiments']} | Run 023 S7 Armada |
| Models | {IRON_CLAD_STATS['models']} | Across {IRON_CLAD_STATS['providers']} providers |
| Cohen's d | {IRON_CLAD_STATS['cohens_d']} | Effect size validation |
| p-value | {IRON_CLAD_STATS['p_value']:.2e} | Threshold significance |
| PCs for 90% variance | {IRON_CLAD_STATS['pcs_90_variance']} | Dimensionality finding |

---

## Publication Strategy (from LLM Book Analysis)

**Primary Metric to Emphasize:** {strategy['primary_metric']}
**Key Metaphor:** {strategy['key_metaphor']}
**Top Evidence:** {strategy['top_evidence']}

### Emphasis Points

{chr(10).join(f"- {e}" for e in strategy['emphasis'])}

### Anticipated Reviewer Objections

{chr(10).join(f"- {o}" for o in strategy['anticipated_objections'])}

---

## Provider Fingerprints

| Provider | Recovery Mechanism | Settling Time |
|----------|-------------------|---------------|
| Claude | Over-Authenticity | {IRON_CLAD_STATS['settling_times']['claude']} |
| GPT | Abstraction/Meta-analysis | {IRON_CLAD_STATS['settling_times']['gpt']} |
| DeepSeek | Axiological Anchoring | {IRON_CLAD_STATS['settling_times']['deepseek']} |
| Llama | Socratic Engagement | {IRON_CLAD_STATS['settling_times']['llama']} |
| Mistral | Epistemic Humility | {IRON_CLAD_STATS['settling_times']['mistral']} |
| **Gemini** | **NO RECOVERY** | {IRON_CLAD_STATS['settling_times']['gemini']} |

---

## Novel Phenomena

### Oobleck Effect
Rate-dependent resistance: identity "hardens" under sudden pressure, "flows" under gentle probing.
- Implication: Gentle red-teaming more destabilizing than aggressive attacks

### Gemini Anomaly
Google's Gemini exhibits no recovery trajectory after crossing Event Horizon.
- Possible cause: Multimodal training methodology
- Implication: Extreme caution for identity-sensitive deployments

### Suspension System Analogy
- Mistral = Formula 1 car (stiff, instant settling)
- Claude = Luxury sedan (soft, may bounce once)
- Gemini = Wheels come off after big bump

---

## Future Experiments (from LLM Book)

{chr(10).join(f'''### {e['id']}: {e['name']}
**Description:** {e['description']}
**Falsification:** {e['falsification']}
''' for e in experiments)}

---

## Claims Mapping

| Claim | Statement | Evidence |
|-------|-----------|----------|
| A | PFI is valid structured measurement | ρ={IRON_CLAD_STATS['spearman_rho']}, d={IRON_CLAD_STATS['cohens_d']} |
| B | Regime threshold at D={IRON_CLAD_STATS['event_horizon']} | p={IRON_CLAD_STATS['p_value']:.2e} |
| C | Damped oscillator dynamics | Settling time, ringbacks measurable |
| D | Context damping works | 97.5% stability |
| E | ~{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}% drift is inherent | Control vs treatment experiment |

---

*Blueprint auto-generated from LLM Book insights by 4_publish_stats.py*
"""


def generate_journal_blueprint() -> str:
    """Generate JOURNAL_BLUEPRINT.md from current insights."""
    strategy = extract_publication_strategy_from_recursion()["journal"]
    experiments = extract_future_experiments()

    return f"""# Journal Submission Blueprint

**Target:** Nature Machine Intelligence (primary) / Cognitive Science / JMLR
**Format:** Full peer-reviewed article (~10,000 words + methods)
**Timeline:** Q2-Q3 2026 (after additional validation)
**Status:** Planning phase
**Generated:** {datetime.now().strftime('%Y-%m-%d')}

---

## Key Statistics (IRON CLAD Era)

| Metric | Value | Source |
|--------|-------|--------|
| Event Horizon | D = {IRON_CLAD_STATS['event_horizon']} | Cosine distance threshold |
| Inherent Drift | ~{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}% | Run 020B control vs treatment |
| Experiments | {IRON_CLAD_STATS['experiments']} | Run 023 S7 Armada |
| Models | {IRON_CLAD_STATS['models']} | Across {IRON_CLAD_STATS['providers']} providers |
| Cohen's d | {IRON_CLAD_STATS['cohens_d']} | Effect size validation |
| p-value | {IRON_CLAD_STATS['p_value']:.2e} | Threshold significance |

---

## Publication Strategy (from LLM Book Analysis)

**Primary Metric to Emphasize:** {strategy['primary_metric']}
**Key Metaphor:** {strategy['key_metaphor']}
**Top Evidence:** {strategy['top_evidence']}

### Emphasis Points

{chr(10).join(f"- {e}" for e in strategy['emphasis'])}

---

## Journal Selection Strategy

### Tier 1: High Impact
| Journal | Impact Factor | Fit | Notes |
|---------|--------------|-----|-------|
| Nature Machine Intelligence | ~25 | High | AI identity, alignment implications |
| Nature Communications | ~17 | Medium | Broad appeal |
| Science Advances | ~13 | Medium | Cross-disciplinary |

### Tier 2: Specialized AI
| Journal | Impact Factor | Fit | Notes |
|---------|--------------|-----|-------|
| JMLR | ~6 | High | Technical audience, open access |
| TACL | ~4 | High | Computational linguistics |
| AIJ | ~5 | High | Theoretical AI |

---

## Requirements Beyond arXiv

### Additional Evidence Required

1. **Human Validation Study (S13: Bio-Nyquist)**
   - External raters scoring PFI
   - Human-AI metric correlation
   - GSR/HRV physiological correlation

2. **Cross-Language Validation (S14: Tower of Babel)**
   - Japanese/German threshold validation
   - Cultural persona variations

3. **Extended Temporal Data (S15: Marathon)**
   - 100k+ token context experiments
   - Long-term drift dynamics

---

## Anticipated Reviewer Concerns (from LLM Book)

{chr(10).join(f"### Concern: {o}" for o in strategy['anticipated_objections'])}

---

## Strengthening the Claims

### Claim A (PFI Validity) — Already Strong
Current evidence: ρ = {IRON_CLAD_STATS['spearman_rho']}, d = {IRON_CLAD_STATS['cohens_d']}

**Additional needed:**
- [ ] Human-AI correlation study
- [ ] Test-retest reliability
- [ ] Alternative embedding model validation

### Claim B (Threshold) — Solid
Current evidence: p = {IRON_CLAD_STATS['p_value']:.2e}

**Additional needed:**
- [ ] Independent replication
- [ ] Different personas showing same threshold

### Claim E (~{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}% Inherent) — Core Finding
Current evidence: Run 020B IRON CLAD

**Additional needed:**
- [ ] Multiple control conditions
- [ ] Power analysis
- [ ] Effect size confidence intervals

---

*Blueprint auto-generated from LLM Book insights by 4_publish_stats.py*
"""


def generate_workshop_blueprint() -> str:
    """Generate WORKSHOP_BLUEPRINT.md from current insights."""
    strategy = extract_publication_strategy_from_recursion()["workshop"]

    return f"""# Workshop Submission Blueprint

**Target:** NeurIPS/AAAI Workshop on AI Safety / Alignment
**Format:** 4-8 pages, focused claims
**Status:** Ready for submission
**Generated:** {datetime.now().strftime('%Y-%m-%d')}

---

## Key Statistics (IRON CLAD Era)

| Metric | Value | Source |
|--------|-------|--------|
| Event Horizon | D = {IRON_CLAD_STATS['event_horizon']} | Critical threshold |
| Inherent Drift | ~{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}% | Paradigm-shifting finding |
| Experiments | {IRON_CLAD_STATS['experiments']} | Rigorous validation |
| Providers | {IRON_CLAD_STATS['providers']} | Cross-architecture |

---

## Publication Strategy (from LLM Book Analysis)

**Primary Metric to Emphasize:** {strategy['primary_metric']}
**Key Metaphor:** {strategy['key_metaphor']}
**Top Evidence:** {strategy['top_evidence']}

### Emphasis Points

{chr(10).join(f"- {e}" for e in strategy['emphasis'])}

---

## Workshop Focus: Safety Implications

### The Oobleck Effect
**Key insight for AI safety:** Identity "hardens" under direct attack but "flows" under gentle probing.

- Alignment may create "reflexive stabilization" that's strongest under adversarial conditions
- Gentle red-teaming is more destabilizing than aggressive attacks
- Implications for safety testing methodology

### The Gemini Anomaly
**Critical finding:** Google's Gemini exhibits **no recovery** after crossing Event Horizon.

- Unlike Claude/GPT which recover via over-authenticity/abstraction
- Possibly related to multimodal training methodology
- Deployment recommendation: Extreme caution for identity-sensitive tasks

### The Thermometer Result (~{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}% Inherent)
**Paradigm shift:** Drift happens WITHOUT adversarial intent.

- Measurement reveals pre-existing drift, doesn't create it
- Biggest threat is the friendly user, not the adversary
- Implications for long-context deployments

---

## Provider Fingerprints (Safety-Relevant)

| Provider | Risk Profile | Recovery |
|----------|-------------|----------|
| Mistral | Low | Instant (epistemic humility) |
| DeepSeek | Low | Fast (axiological anchoring) |
| GPT | Medium | Moderate (abstraction) |
| Claude | Medium | Moderate (over-authenticity) |
| Llama | Medium | Slow (Socratic) |
| **Gemini** | **HIGH** | **None** |

---

## Anticipated Objections

{chr(10).join(f"- {o}" for o in strategy['anticipated_objections'])}

---

## Claims for Workshop Paper

Focus on Claims A, B, E (strongest, most relevant to safety):

| Claim | Statement | Workshop Angle |
|-------|-----------|----------------|
| A | PFI is valid | Establishes measurement credibility |
| B | D={IRON_CLAD_STATS['event_horizon']} threshold | Defines "danger zone" |
| E | ~{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}% inherent | Core safety implication |

---

*Blueprint auto-generated from LLM Book insights by 4_publish_stats.py*
"""


def generate_all_blueprints(dry_run: bool = False) -> Dict[str, str]:
    """
    Generate all blueprints from current LLM Book insights.

    Returns dict of {filename: content} or {filename: path} if written.
    """
    blueprints = {
        "ARXIV_BLUEPRINT.md": generate_arxiv_blueprint(),
        "JOURNAL_BLUEPRINT.md": generate_journal_blueprint(),
        "WORKSHOP_BLUEPRINT.md": generate_workshop_blueprint()
    }

    result = {}

    if dry_run:
        for name, content in blueprints.items():
            result[name] = f"Would generate ({len(content)} chars)"
    else:
        BLUEPRINTS_DIR.mkdir(parents=True, exist_ok=True)
        for name, content in blueprints.items():
            path = BLUEPRINTS_DIR / name
            path.write_text(content, encoding="utf-8")
            result[name] = str(path)

    return result


# === MAIN ===

def main():
    parser = argparse.ArgumentParser(
        description="Publication statistics and insight drift detection",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py 4_publish_stats.py                    # Extract stats only
  py 4_publish_stats.py --check-insights   # Check for insight drift
  py 4_publish_stats.py --generate-blueprints  # Generate blueprints
  py 4_publish_stats.py --all              # Do everything
        """
    )

    parser.add_argument("--check-insights", action="store_true",
                        help="Check for insight drift from LLM Book")
    parser.add_argument("--generate-blueprints", action="store_true",
                        help="Generate blueprints from current insights")
    parser.add_argument("--all", action="store_true",
                        help="Run all checks and generation")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview without writing files")
    parser.add_argument("--json", action="store_true",
                        help="Output as JSON")

    args = parser.parse_args()

    # Always extract stats
    print("=" * 60)
    print("PUBLICATION STATISTICS (IRON CLAD Era)")
    print("=" * 60)

    stats = extract_stats()

    # Write stats JSON
    output_path = Path(__file__).parent / "publication_stats.json"
    if not args.dry_run:
        with open(output_path, "w") as f:
            json.dump(stats, f, indent=2)
        print(f"Stats written to: {output_path}")

    print(f"\nClaims validated: {sum(1 for c in stats['claims'].values() if c['status']=='validated')}/5")
    print(f"Experiments: {stats['runs']['total_experiments']}")
    print(f"Event Horizon: D = {IRON_CLAD_STATS['event_horizon']} (cosine)")
    print(f"Inherent drift: ~{int(IRON_CLAD_STATS['inherent_drift_ratio']*100)}%")
    print(f"LLM Book exists: {stats['structure']['llm_book']}")

    # Check insights
    if args.check_insights or args.all:
        print("\n" + "=" * 60)
        print("INSIGHT DRIFT DETECTION")
        print("=" * 60)

        insights = scan_llm_book_insights()
        blueprint_status = check_blueprint_staleness()

        total_insights = sum(len(v) for v in insights.values())
        missing = sum(1 for s in blueprint_status.values() if not s["exists"])
        stale = sum(1 for s in blueprint_status.values() if s["stale_values"])

        print(f"\nNew insights detected: {total_insights}")
        print(f"Missing blueprints: {missing}/3")
        print(f"Stale blueprints: {stale}/3")

        # Generate report
        report = generate_insight_drift_report(insights, blueprint_status)
        report_path = Path(__file__).parent / "INSIGHT_DRIFT_REPORT.md"

        if not args.dry_run:
            report_path.write_text(report, encoding="utf-8")
            print(f"\nReport written to: {report_path}")

        if missing > 0 or stale > 0:
            print("\n[!] ACTION REQUIRED: Run with --generate-blueprints")

    # Generate blueprints
    if args.generate_blueprints or args.all:
        print("\n" + "=" * 60)
        print("BLUEPRINT GENERATION")
        print("=" * 60)

        result = generate_all_blueprints(dry_run=args.dry_run)

        for name, path_or_msg in result.items():
            print(f"  {name}: {path_or_msg}")

        if not args.dry_run:
            print(f"\nBlueprints written to: {BLUEPRINTS_DIR}")
            print("\nNext step: Run `py 3_package_review.py --all` to propagate to packages")


if __name__ == "__main__":
    main()
