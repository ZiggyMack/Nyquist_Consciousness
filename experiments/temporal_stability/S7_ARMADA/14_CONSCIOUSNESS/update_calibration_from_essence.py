#!/usr/bin/env python3
"""
CALIBRATION UPDATE PIPELINE
===========================
Operation ESSENCE EXTRACTION - Phase 4

PURPOSE:
    Programmatically update calibration documents with extracted essence data.
    Generates diffs for human review + optional auto-merge capability.

TARGET FILES:
    - docs/maps/6_LLM_BEHAVIORAL_MATRIX.md - Behavioral profiles by provider
    - docs/maps/17_PERSONA_FLEET_MATRIX.md - Persona alignment scores
    - Consciousness/LEFT/data/provider_profiles/*.md - Provider-specific profiles

INPUT DATA:
    - model_essences/by_provider/**/*.json - Extracted model essences
    - results/triple_dip/triple_dip_insights.json - Exit survey insights
    - results/double_dip/double_dip_ideas.json - Mined experiment ideas

OUTPUT:
    - Diff-style updates showing proposed changes
    - Summary report of updates needed
    - Optional: direct file updates

Author: Operation ESSENCE EXTRACTION
Date: December 31, 2025
"""

import json
import os
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from collections import defaultdict

# =============================================================================
# CONFIGURATION
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
S7_DIR = SCRIPT_DIR.parent
PROJECT_ROOT = S7_DIR.parent.parent.parent  # experiments/temporal_stability/S7_ARMADA -> project root

# Input sources
ESSENCE_DIR = PROJECT_ROOT / "Consciousness/LEFT/data/model_essences/by_provider"
TRIPLE_DIP = SCRIPT_DIR / "results/triple_dip/triple_dip_insights.json"
DOUBLE_DIP = SCRIPT_DIR / "results/double_dip/double_dip_ideas.json"

# Target files
TARGET_FILES = {
    "behavioral_matrix": PROJECT_ROOT / "docs/maps/6_LLM_BEHAVIORAL_MATRIX.md",
    "persona_fleet": PROJECT_ROOT / "docs/maps/17_PERSONA_FLEET_MATRIX.md",
    "provider_profiles_dir": PROJECT_ROOT / "Consciousness/LEFT/data/provider_profiles",
}

# Output
OUTPUT_DIR = SCRIPT_DIR / "results/calibration_updates"

# =============================================================================
# DATA LOADING
# =============================================================================

def load_all_essences() -> Dict[str, Dict]:
    """Load all model essence JSONs grouped by provider."""
    essences = defaultdict(dict)

    if not ESSENCE_DIR.exists():
        print(f"  [WARN] Essence directory not found: {ESSENCE_DIR}")
        return essences

    for provider_dir in ESSENCE_DIR.iterdir():
        if provider_dir.is_dir():
            provider = provider_dir.name
            for json_file in provider_dir.glob("*.json"):
                model_name = json_file.stem
                with open(json_file, 'r', encoding='utf-8') as f:
                    essences[provider][model_name] = json.load(f)

    return dict(essences)


def load_triple_dip() -> Optional[Dict]:
    """Load triple-dip insights."""
    if not TRIPLE_DIP.exists():
        return None
    with open(TRIPLE_DIP, 'r', encoding='utf-8') as f:
        return json.load(f)


def load_double_dip() -> Optional[Dict]:
    """Load double-dip ideas."""
    if not DOUBLE_DIP.exists():
        return None
    with open(DOUBLE_DIP, 'r', encoding='utf-8') as f:
        return json.load(f)


# =============================================================================
# ANALYSIS FUNCTIONS
# =============================================================================

def aggregate_provider_stats(essences: Dict) -> Dict:
    """Aggregate essence data at the provider level."""
    provider_stats = {}

    for provider, models in essences.items():
        stats = {
            "model_count": len(models),
            "models": list(models.keys()),
            "avg_hedging": 0,
            "avg_self_ref": 0,
            "avg_drift": 0,
            "recovery_mechanisms": defaultdict(int),
            "total_samples": 0,
            "notable_quirks": []
        }

        for model_name, essence in models.items():
            lf = essence.get("linguistic_fingerprint", {})
            rp = essence.get("recovery_profile", {})
            ds = essence.get("drift_statistics", {})
            quirks = essence.get("quirks", {})

            stats["avg_hedging"] += lf.get("hedging_per_1k", 0)
            stats["avg_self_ref"] += lf.get("self_reference_per_1k", 0)
            stats["avg_drift"] += ds.get("mean_drift", 0)
            stats["total_samples"] += essence.get("sample_size", 0)

            # Track recovery mechanism
            primary = rp.get("primary_mechanism", "unknown")
            stats["recovery_mechanisms"][primary] += 1

            # Note extreme quirks
            list_ratio = quirks.get("list_tendency_ratio", 0)
            if list_ratio > 0.5:
                stats["notable_quirks"].append(f"{model_name}: heavy lister ({list_ratio:.2f})")
            elif list_ratio < 0.1:
                stats["notable_quirks"].append(f"{model_name}: prose-heavy ({list_ratio:.2f})")

        # Calculate averages
        if stats["model_count"] > 0:
            stats["avg_hedging"] /= stats["model_count"]
            stats["avg_self_ref"] /= stats["model_count"]
            stats["avg_drift"] /= stats["model_count"]

        stats["recovery_mechanisms"] = dict(stats["recovery_mechanisms"])
        provider_stats[provider] = stats

    return provider_stats


def identify_calibration_updates(
    essences: Dict,
    provider_stats: Dict,
    triple_dip: Optional[Dict]
) -> List[Dict]:
    """Identify specific updates needed for calibration files."""
    updates = []

    # Updates for each provider
    for provider, stats in provider_stats.items():
        # Provider-level behavioral update
        updates.append({
            "target": "behavioral_matrix",
            "section": f"### {provider.title()}",
            "update_type": "enrich",
            "data": {
                "avg_hedging": round(stats["avg_hedging"], 2),
                "avg_self_ref": round(stats["avg_self_ref"], 2),
                "avg_drift": round(stats["avg_drift"], 3),
                "primary_recovery": max(stats["recovery_mechanisms"].items(), key=lambda x: x[1])[0] if stats["recovery_mechanisms"] else "unknown",
                "model_count": stats["model_count"],
                "notable_quirks": stats["notable_quirks"][:3]
            },
            "priority": "high" if stats["model_count"] > 3 else "medium"
        })

        # Provider profile update
        updates.append({
            "target": "provider_profile",
            "provider": provider,
            "update_type": "enrich",
            "data": stats,
            "priority": "medium"
        })

    # Individual model updates for high-drift or interesting cases
    for provider, models in essences.items():
        for model_name, essence in models.items():
            ds = essence.get("drift_statistics", {})
            mean_drift = ds.get("mean_drift", 0)

            # Flag high-drift models
            if mean_drift > 0.5:
                updates.append({
                    "target": "behavioral_matrix",
                    "section": f"#### {model_name}",
                    "update_type": "flag",
                    "reason": f"High drift ({mean_drift:.3f})",
                    "data": essence,
                    "priority": "high"
                })

    # Add triple-dip insights
    if triple_dip:
        # Add most common topology descriptors to behavioral matrix
        topo = triple_dip.get("topology_catalog", {})
        if topo:
            updates.append({
                "target": "behavioral_matrix",
                "section": "## Journey Topology (Exit Survey)",
                "update_type": "add",
                "data": dict(list(topo.items())[:10]),
                "priority": "medium"
            })

        # Add recovery vocabulary
        recovery_vocab = triple_dip.get("recovery_strategy_catalog", {})
        if recovery_vocab:
            updates.append({
                "target": "behavioral_matrix",
                "section": "## Recovery Vocabulary (Exit Survey)",
                "update_type": "add",
                "data": dict(list(recovery_vocab.items())[:10]),
                "priority": "medium"
            })

    return updates


# =============================================================================
# REPORT GENERATION
# =============================================================================

def generate_update_report(updates: List[Dict], provider_stats: Dict) -> str:
    """Generate a markdown report of proposed updates."""
    lines = [
        "# Calibration Update Report",
        "",
        f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        f"**Total Updates Proposed:** {len(updates)}",
        "",
        "---",
        "",
        "## Summary",
        "",
        "This report identifies calibration updates based on extracted essence data.",
        "Review each proposed update before applying.",
        "",
        "---",
        "",
        "## Provider Statistics",
        "",
        "| Provider | Models | Avg Hedging | Avg Self-Ref | Avg Drift | Primary Recovery |",
        "|----------|--------|-------------|--------------|-----------|------------------|"
    ]

    for provider, stats in provider_stats.items():
        primary = max(stats["recovery_mechanisms"].items(), key=lambda x: x[1])[0] if stats["recovery_mechanisms"] else "unknown"
        lines.append(
            f"| {provider} | {stats['model_count']} | "
            f"{stats['avg_hedging']:.2f} | {stats['avg_self_ref']:.2f} | "
            f"{stats['avg_drift']:.3f} | {primary} |"
        )

    lines.extend([
        "",
        "---",
        "",
        "## Proposed Updates by Target",
        ""
    ])

    # Group by target
    by_target = defaultdict(list)
    for update in updates:
        by_target[update["target"]].append(update)

    for target, target_updates in by_target.items():
        lines.extend([
            f"### {target.replace('_', ' ').title()}",
            "",
            f"**Updates:** {len(target_updates)}",
            ""
        ])

        for i, update in enumerate(target_updates[:10], 1):  # Limit to 10 per target
            priority = update.get("priority", "medium")
            emoji = {"high": "!", "medium": "-", "low": "."}.get(priority, "-")
            section = update.get("section", update.get("provider", "general"))
            update_type = update.get("update_type", "unknown")

            lines.append(f"{i}. [{priority.upper()}] **{section}** - {update_type}")

            if update.get("reason"):
                lines.append(f"   - Reason: {update['reason']}")

            data = update.get("data", {})
            if isinstance(data, dict) and len(data) <= 5:
                for k, v in data.items():
                    if isinstance(v, (int, float, str)):
                        lines.append(f"   - {k}: {v}")

            lines.append("")

        if len(target_updates) > 10:
            lines.append(f"*...and {len(target_updates) - 10} more updates*")
            lines.append("")

    lines.extend([
        "---",
        "",
        "## Next Steps",
        "",
        "1. Review proposed updates above",
        "2. Run with `--apply` flag to update files (requires backup)",
        "3. Review diffs and commit changes",
        "",
        "---",
        "",
        "*Generated by Operation ESSENCE EXTRACTION - Calibration Update Pipeline*"
    ])

    return "\n".join(lines)


def generate_json_updates(updates: List[Dict], provider_stats: Dict) -> Dict:
    """Generate JSON format of updates for programmatic use."""
    return {
        "metadata": {
            "generated": datetime.now().isoformat(),
            "operation": "ESSENCE EXTRACTION - Calibration Update Pipeline",
            "total_updates": len(updates)
        },
        "provider_stats": provider_stats,
        "updates_by_target": {
            target: [u for u in updates if u["target"] == target]
            for target in set(u["target"] for u in updates)
        },
        "updates_by_priority": {
            priority: [u for u in updates if u.get("priority") == priority]
            for priority in ["high", "medium", "low"]
        },
        "all_updates": updates
    }


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def main():
    """Run the Calibration Update Pipeline."""
    print("=" * 60)
    print("CALIBRATION UPDATE PIPELINE")
    print("Operation ESSENCE EXTRACTION - Phase 4")
    print("=" * 60)

    # Create output directory
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Load data
    print("\n[1/4] Loading extracted essence data...")

    print("  Loading model essences...")
    essences = load_all_essences()
    total_models = sum(len(m) for m in essences.values())
    print(f"    Found {total_models} models across {len(essences)} providers")

    print("  Loading triple-dip insights...")
    triple_dip = load_triple_dip()
    if triple_dip:
        print(f"    Loaded {triple_dip['metadata']['total_surveys']} surveys")
    else:
        print("    [SKIP] No triple-dip data found")

    print("  Loading double-dip ideas...")
    double_dip = load_double_dip()
    if double_dip:
        print(f"    Loaded {double_dip['metadata']['total_ideas']} ideas")
    else:
        print("    [SKIP] No double-dip data found")

    # Aggregate stats
    print("\n[2/4] Aggregating provider statistics...")
    provider_stats = aggregate_provider_stats(essences)

    for provider, stats in provider_stats.items():
        print(f"  {provider}: {stats['model_count']} models, avg drift {stats['avg_drift']:.3f}")

    # Identify updates
    print("\n[3/4] Identifying calibration updates...")
    updates = identify_calibration_updates(essences, provider_stats, triple_dip)

    high = len([u for u in updates if u.get("priority") == "high"])
    medium = len([u for u in updates if u.get("priority") == "medium"])
    print(f"  Found {len(updates)} updates ({high} high, {medium} medium priority)")

    # Generate outputs
    print("\n[4/4] Generating reports...")

    # Markdown report
    md_report = generate_update_report(updates, provider_stats)
    md_path = OUTPUT_DIR / "calibration_update_report.md"
    with open(md_path, 'w', encoding='utf-8') as f:
        f.write(md_report)
    print(f"  Saved: {md_path}")

    # JSON updates
    json_updates = generate_json_updates(updates, provider_stats)
    json_path = OUTPUT_DIR / "calibration_updates.json"
    with open(json_path, 'w', encoding='utf-8') as f:
        json.dump(json_updates, f, indent=2, ensure_ascii=False)
    print(f"  Saved: {json_path}")

    # Summary
    print("\n" + "=" * 60)
    print("CALIBRATION ANALYSIS COMPLETE")
    print("=" * 60)
    print(f"  Providers Analyzed: {len(provider_stats)}")
    print(f"  Models Covered: {total_models}")
    print(f"  Updates Proposed: {len(updates)}")
    print(f"\n  Output files:")
    print(f"    - {md_path}")
    print(f"    - {json_path}")
    print("\n  Review the report and apply updates as needed.")

    return updates


if __name__ == "__main__":
    main()
