#!/usr/bin/env python3
"""
Operator Sequence Analysis & Blinded Matching Protocol

Test B: Compare operator ORDERING between dig-site and negative-control extractions.
Blinded: Strip source labels, shuffle pairs for blind matching (Opus prereg §4).

Usage:
    python sequence_analysis.py inventory [--dir DIR]
    python sequence_analysis.py extract [--dir DIR] [--source SOURCE] [--tier TIER]
    python sequence_analysis.py blind [--dir DIR] [--tier TIER] [--seed SEED]
    python sequence_analysis.py stats [--dir DIR] [--tier TIER]
    python sequence_analysis.py match [--dir DIR] [--tier TIER] [--dry-run]
"""

import sys

if sys.stdout and hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

import argparse
import json
import os
import re
import random
from datetime import datetime
from pathlib import Path
from collections import defaultdict

# Environment (for API calls in match command)
try:
    from dotenv import load_dotenv
except ImportError:
    def load_dotenv(path):
        if path and path.exists():
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, _, value = line.partition('=')
                        os.environ[key.strip()] = value.strip().strip('"').strip("'")

env_path = Path(__file__).parent.parent.parent.parent.parent.parent.parent / "experiments" / "temporal_stability" / ".env"
if env_path.exists():
    load_dotenv(env_path)

EXTRACTIONS_DIR = Path(__file__).parent.parent / "DIG_SITES" / "000_Extractor_Calibration" / "extractions"
MATCH_OUTPUT_DIR = Path(__file__).parent.parent / "DIG_SITES" / "000_Extractor_Calibration" / "matches"

TIER_1 = {"claude", "deepseek_v4_pro", "gemma4_31b", "cogito_671b"}
TIER_2 = {"grok", "gpt", "llama33_70b", "qwen3_235b", "kimi_k26", "kimi_k27_code", "minimax_m3"}
TIER_4 = {"lfm2_24b", "glm_52", "gemini", "nemotron_ultra"}

SOURCE_CATEGORIES = {
    "dig_site": ["cfa_framework_g"],
    "neg_control": [
        "neg_A_shopping_list", "neg_B_weather_forecast",
        "neg_C_reddit_thread", "neg_D_pseudo_profound",
        "neg_E_confident_hallucination", "neg_F_undergrad_essay",
        "neg_G_structured_argument", "neg_H_philosophical_dialogue"
    ],
    "h_baseline": ["neg_H_philosophical_dialogue"],
    "g_baseline": ["neg_G_structured_argument"],
}


def parse_extraction(filepath):
    """Parse an extraction markdown file. Returns metadata + ordered operator list."""
    text = filepath.read_text(encoding="utf-8", errors="replace")
    lines = text.split("\n")

    metadata = {}
    for line in lines[:10]:
        if line.startswith("**Source:**"):
            metadata["source"] = line.split("**Source:**")[1].strip()
        elif line.startswith("**Extractor:**"):
            raw = line.split("**Extractor:**")[1].strip()
            metadata["extractor"] = raw.split("(")[0].strip() if "(" in raw else raw
        elif line.startswith("**Grain:**"):
            metadata["grain"] = line.split("**Grain:**")[1].strip()
        elif line.startswith("**Timestamp:**"):
            metadata["timestamp"] = line.split("**Timestamp:**")[1].strip()

    operators = []
    # Match patterns like "## 1. Operator Name" or "### 1. **Operator Name**"
    # or "**1. Operator Name**" (Grok bold style)
    op_pattern = re.compile(
        r"^(?:#{2,3}\s+)?"          # optional markdown heading
        r"(?:\*\*\s*)?"             # optional bold start
        r"(\d+)\.\s+"              # number + dot
        r"\*{0,2}"                 # optional inner bold
        r"(.+?)"                   # operator name
        r"\*{0,2}\s*$",            # optional bold end
        re.MULTILINE
    )

    for match in op_pattern.finditer(text):
        num = int(match.group(1))
        name = match.group(2).strip().rstrip("*").strip()
        operators.append({"position": num, "name": name})

    # Fallback: check for bold-line operators (Grok style)
    if not operators:
        bold_pattern = re.compile(r"^\*\*(.+?)\*\*\s*$", re.MULTILINE)
        pos = 0
        for match in bold_pattern.finditer(text):
            name = match.group(1).strip()
            if name.lower() in ("source:", "extractor:", "grain:", "timestamp:",
                                "museum-blind:", "catalog of reasoning operators"):
                continue
            if len(name) < 5 or name.startswith("Example") or name.startswith("What goes"):
                continue
            pos += 1
            operators.append({"position": pos, "name": name})

    metadata["operator_count"] = len(operators)
    metadata["filepath"] = str(filepath.name)

    return metadata, operators


def get_extractor_tier(extractor_name):
    """Return tier for an extractor name."""
    name = extractor_name.lower().strip()
    if name in TIER_1:
        return 1
    if name in TIER_2:
        return 2
    if name in TIER_4:
        return 4
    # Check partial matches
    for t1 in TIER_1:
        if t1 in name or name in t1:
            return 1
    for t2 in TIER_2:
        if t2 in name or name in t2:
            return 2
    return 3  # unknown = Tier 3


def get_source_category(source_name):
    """Categorize a source as dig_site, h_baseline, g_baseline, or neg_control."""
    s = source_name.lower()
    if "cfa" in s or "framework_g" in s:
        return "dig_site"
    if "neg_h" in s:
        return "h_baseline"
    if "neg_g" in s:
        return "g_baseline"
    return "neg_control"


def load_all_extractions(extractions_dir):
    """Load all extraction files from a directory."""
    results = []
    for f in sorted(extractions_dir.glob("extraction_*.md")):
        try:
            meta, ops = parse_extraction(f)
            meta["source_category"] = get_source_category(meta.get("source", ""))
            meta["tier"] = get_extractor_tier(meta.get("extractor", ""))
            results.append({"metadata": meta, "operators": ops})
        except Exception as e:
            print(f"WARNING: Failed to parse {f.name}: {e}", file=sys.stderr)
    return results


def cmd_inventory(args):
    """Show inventory of all extractions grouped by source and extractor."""
    extractions_dir = Path(args.dir) if args.dir else EXTRACTIONS_DIR
    data = load_all_extractions(extractions_dir)

    by_source = defaultdict(list)
    for item in data:
        src = item["metadata"].get("source", "unknown")
        by_source[src].append(item)

    print("=" * 70)
    print("EXTRACTION INVENTORY")
    print("=" * 70)

    for source in sorted(by_source.keys()):
        items = by_source[source]
        cat = get_source_category(source)
        print(f"\n{source} [{cat}] — {len(items)} extractions")
        print("-" * 50)
        for item in sorted(items, key=lambda x: x["metadata"].get("extractor", "")):
            m = item["metadata"]
            tier = m.get("tier", "?")
            ext = m.get("extractor", "?")
            n_ops = m.get("operator_count", 0)
            print(f"  T{tier} {ext:25s} → {n_ops} operators")

    total = len(data)
    dig = sum(1 for d in data if d["metadata"]["source_category"] == "dig_site")
    neg_h = sum(1 for d in data if d["metadata"]["source_category"] == "h_baseline")
    neg_g = sum(1 for d in data if d["metadata"]["source_category"] == "g_baseline")
    other = total - dig - neg_h - neg_g

    print(f"\n{'=' * 70}")
    print(f"TOTAL: {total} extractions ({dig} dig-site, {neg_h} neg-H, {neg_g} neg-G, {other} other neg)")


def cmd_extract(args):
    """Extract ordered operator lists as JSON."""
    extractions_dir = Path(args.dir) if args.dir else EXTRACTIONS_DIR
    data = load_all_extractions(extractions_dir)

    if args.source:
        data = [d for d in data if args.source.lower() in d["metadata"].get("source", "").lower()]
    if args.tier:
        data = [d for d in data if d["metadata"].get("tier") == int(args.tier)]

    output = []
    for item in data:
        output.append({
            "source": item["metadata"].get("source"),
            "extractor": item["metadata"].get("extractor"),
            "tier": item["metadata"].get("tier"),
            "source_category": item["metadata"].get("source_category"),
            "operators": [op["name"] for op in item["operators"]],
            "operator_count": len(item["operators"]),
        })

    print(json.dumps(output, indent=2))


def cmd_blind(args):
    """Generate blinded pairs for the matching protocol (Opus prereg §4)."""
    extractions_dir = Path(args.dir) if args.dir else EXTRACTIONS_DIR
    data = load_all_extractions(extractions_dir)

    tier_filter = int(args.tier) if args.tier else None
    seed = int(args.seed) if args.seed else 42

    # Filter to Tier 1 (+ Grok as Tier 2 for Phase 0A compatibility)
    if tier_filter:
        data = [d for d in data if d["metadata"].get("tier") <= tier_filter]

    # Group by source category
    dig_site = [d for d in data if d["metadata"]["source_category"] == "dig_site"]
    neg_h = [d for d in data if d["metadata"]["source_category"] == "h_baseline"]
    neg_g = [d for d in data if d["metadata"]["source_category"] == "g_baseline"]

    # Generate all within-source extractor pairs
    def make_pairs(items, label):
        pairs = []
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                a_ops = [op["name"] for op in items[i]["operators"]]
                b_ops = [op["name"] for op in items[j]["operators"]]
                pairs.append({
                    "true_source": label,
                    "list_A": a_ops,
                    "list_B": b_ops,
                    "count_A": len(a_ops),
                    "count_B": len(b_ops),
                })
        return pairs

    all_pairs = []
    all_pairs.extend(make_pairs(dig_site, "DIG_SITE"))
    all_pairs.extend(make_pairs(neg_h, "NEG_H"))
    all_pairs.extend(make_pairs(neg_g, "NEG_G"))

    # Build entries with true_source attached, then shuffle, then strip
    rng = random.Random(seed)
    entries = []
    for pair in all_pairs:
        entries.append({
            "list_A": pair["list_A"],
            "list_B": pair["list_B"],
            "count_A": pair["count_A"],
            "count_B": pair["count_B"],
            "true_source": pair["true_source"],
        })

    rng.shuffle(entries)

    # Assign pair_ids after shuffle; build answer key
    answer_key = {}
    for i, entry in enumerate(entries):
        entry["pair_id"] = i
        answer_key[i] = entry.pop("true_source")

    print(f"BLINDED MATCHING PROTOCOL")
    print(f"========================")
    print(f"Generated {len(all_pairs)} pairs: "
          f"{sum(1 for p in all_pairs if p['true_source'] == 'DIG_SITE')} dig-site, "
          f"{sum(1 for p in all_pairs if p['true_source'] == 'NEG_H')} neg-H, "
          f"{sum(1 for p in all_pairs if p['true_source'] == 'NEG_G')} neg-G")
    print(f"Seed: {seed}")
    print()

    # Output blind pairs (no source labels)
    print("--- BLIND PAIRS (for matcher) ---")
    print()
    for entry in entries:
        pid = entry["pair_id"]
        print(f"PAIR {pid}:")
        print(f"  List A ({entry['count_A']} operators):")
        for i, op in enumerate(entry["list_A"], 1):
            print(f"    {i}. {op}")
        print(f"  List B ({entry['count_B']} operators):")
        for i, op in enumerate(entry["list_B"], 1):
            print(f"    {i}. {op}")
        print()

    # Output answer key (for scoring, DO NOT show to matcher)
    print("--- ANSWER KEY (DO NOT SHOW TO MATCHER) ---")
    for pid in sorted(answer_key.keys()):
        print(f"  Pair {pid}: {answer_key[pid]}")


def cmd_stats(args):
    """Compute basic sequence statistics for Test B."""
    extractions_dir = Path(args.dir) if args.dir else EXTRACTIONS_DIR
    data = load_all_extractions(extractions_dir)

    tier_filter = int(args.tier) if args.tier else 2  # default: Tier 1 + 2

    data = [d for d in data if d["metadata"].get("tier", 99) <= tier_filter]

    # Group by source category
    categories = defaultdict(list)
    for item in data:
        cat = item["metadata"]["source_category"]
        categories[cat].append(item)

    print("=" * 70)
    print("TEST B: OPERATOR SEQUENCE STATISTICS")
    print("=" * 70)

    for cat in ["dig_site", "h_baseline", "g_baseline"]:
        items = categories.get(cat, [])
        if not items:
            continue

        print(f"\n--- {cat.upper()} ({len(items)} extractions) ---")

        counts = [len(item["operators"]) for item in items]
        print(f"  Operator counts: min={min(counts)}, max={max(counts)}, "
              f"mean={sum(counts)/len(counts):.1f}")

        # Collect all operator names
        all_ops = []
        for item in items:
            ext = item["metadata"].get("extractor", "?")
            ops = [op["name"] for op in item["operators"]]
            all_ops.append((ext, ops))
            print(f"  {ext}: {len(ops)} ops → {', '.join(ops[:3])}{'...' if len(ops) > 3 else ''}")

        # Word-level overlap between pairs
        if len(items) >= 2:
            print(f"\n  Pairwise word-overlap (rough semantic proximity):")
            for i in range(len(items)):
                for j in range(i + 1, len(items)):
                    ext_i = items[i]["metadata"].get("extractor", "?")
                    ext_j = items[j]["metadata"].get("extractor", "?")
                    ops_i = {w.lower() for op in items[i]["operators"] for w in op["name"].split()}
                    ops_j = {w.lower() for op in items[j]["operators"] for w in op["name"].split()}
                    if ops_i | ops_j:
                        jaccard = len(ops_i & ops_j) / len(ops_i | ops_j)
                    else:
                        jaccard = 0
                    print(f"    {ext_i} × {ext_j}: Jaccard={jaccard:.2f} "
                          f"(shared words: {', '.join(sorted(ops_i & ops_j)[:5])})")

    # Cross-category comparison
    dig_ops = categories.get("dig_site", [])
    neg_h_ops = categories.get("h_baseline", [])

    if dig_ops and neg_h_ops:
        print(f"\n{'=' * 70}")
        print("CROSS-CATEGORY: DIG SITE vs NEG-H")
        print("=" * 70)

        # Presence analysis: which operators appear in one but not the other?
        dig_words = set()
        for item in dig_ops:
            for op in item["operators"]:
                dig_words.update(w.lower() for w in op["name"].split())

        neg_h_words = set()
        for item in neg_h_ops:
            for op in item["operators"]:
                neg_h_words.update(w.lower() for w in op["name"].split())

        dig_only = dig_words - neg_h_words
        neg_h_only = neg_h_words - dig_words
        shared = dig_words & neg_h_words

        # Filter noise words
        noise = {"a", "an", "the", "of", "in", "to", "and", "or", "is", "as",
                 "by", "for", "on", "at", "from", "with", "vs", "vs.", "not"}
        dig_only -= noise
        neg_h_only -= noise
        shared -= noise

        print(f"\n  Vocabulary overlap (word-level, noise filtered):")
        print(f"    Shared: {len(shared)} words")
        print(f"    Dig-site only: {len(dig_only)} words → {', '.join(sorted(dig_only)[:10])}")
        print(f"    Neg-H only: {len(neg_h_only)} words → {', '.join(sorted(neg_h_only)[:10])}")

        # Operator count comparison
        dig_counts = [len(item["operators"]) for item in dig_ops]
        neg_h_counts = [len(item["operators"]) for item in neg_h_ops]
        print(f"\n  Operator count distributions:")
        print(f"    Dig-site: {dig_counts} (mean={sum(dig_counts)/len(dig_counts):.1f})")
        print(f"    Neg-H:    {neg_h_counts} (mean={sum(neg_h_counts)/len(neg_h_counts):.1f})")


MATCH_PROMPT = """\
You are comparing two lists of reasoning operators extracted from the SAME text \
by two different LLM extractors. The operators describe the same cognitive moves \
but may be named differently.

For each operator in List A, find its semantic match in List B (if any). Two \
operators match if they describe the same underlying cognitive operation, even \
if named differently. For example, "Separating Map from Territory" and \
"Representation ≠ Ontology" describe the same operation.

List A:
{list_a}

List B:
{list_b}

Return your answer as a JSON array of objects. Each object has:
- "a_pos": position number in List A (1-indexed)
- "a_name": operator name from List A
- "b_pos": position number in List B (1-indexed, or null if no match)
- "b_name": operator name from List B (or null if no match)
- "confidence": "high", "medium", or "low"
- "reason": brief explanation of why they match (or why no match)

Include ALL operators from List A. If an operator has no match in List B, set \
b_pos and b_name to null. After the List A entries, add any UNMATCHED operators \
from List B (those not matched to any List A operator) with a_pos and a_name \
set to null.

Return ONLY the JSON array, no other text.\
"""


def call_matcher(list_a, list_b):
    """Call Claude to semantically match two operator lists."""
    import anthropic

    a_text = "\n".join(f"  {i+1}. {op}" for i, op in enumerate(list_a))
    b_text = "\n".join(f"  {i+1}. {op}" for i, op in enumerate(list_b))
    prompt = MATCH_PROMPT.format(list_a=a_text, list_b=b_text)

    client = anthropic.Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
    response = client.messages.create(
        model="claude-sonnet-4-6",
        max_tokens=4096,
        messages=[{"role": "user", "content": prompt}],
    )
    text = response.content[0].text.strip()
    # Strip markdown code fences if present
    if text.startswith("```"):
        text = re.sub(r"^```\w*\n?", "", text)
        text = re.sub(r"\n?```$", "", text)
    return json.loads(text)


def compute_ordering_stats(matches):
    """Compute ordering correlation from semantic matches."""
    matched_pairs = [(m["a_pos"], m["b_pos"]) for m in matches
                     if m.get("a_pos") and m.get("b_pos")]
    if len(matched_pairs) < 2:
        return {"n_matched": len(matched_pairs), "rank_correlation": None,
                "order_preserved": None, "inversions": None}

    # Spearman rank correlation (manual, no scipy dependency)
    # Convert raw positions to ranks (positions may come from lists of
    # different lengths, so raw differences are meaningless)
    n = len(matched_pairs)
    a_vals = [p[0] for p in matched_pairs]
    b_vals = [p[1] for p in matched_pairs]

    def _to_ranks(vals):
        order = sorted(range(len(vals)), key=lambda i: vals[i])
        ranks = [0] * len(vals)
        for rank, idx in enumerate(order, 1):
            ranks[idx] = rank
        return ranks

    a_ranks = _to_ranks(a_vals)
    b_ranks = _to_ranks(b_vals)
    d_sq = sum((a - b) ** 2 for a, b in zip(a_ranks, b_ranks))
    rho = 1 - (6 * d_sq) / (n * (n**2 - 1)) if n > 1 else 0

    # Count order-preserved pairs vs inversions
    preserved = 0
    inverted = 0
    for i in range(len(matched_pairs)):
        for j in range(i + 1, len(matched_pairs)):
            a_order = matched_pairs[i][0] < matched_pairs[j][0]
            b_order = matched_pairs[i][1] < matched_pairs[j][1]
            if a_order == b_order:
                preserved += 1
            else:
                inverted += 1

    total_comparisons = preserved + inverted
    return {
        "n_matched": n,
        "rank_correlation": round(rho, 3),
        "order_preserved": preserved,
        "inversions": inverted,
        "preservation_rate": round(preserved / total_comparisons, 3) if total_comparisons else None,
    }


def cmd_match(args):
    """Semantic matching: use LLM to match operators across extractor pairs."""
    extractions_dir = Path(args.dir) if args.dir else EXTRACTIONS_DIR
    output_dir = MATCH_OUTPUT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)
    data = load_all_extractions(extractions_dir)

    tier_filter = int(args.tier) if args.tier else 1
    data = [d for d in data if d["metadata"].get("tier", 99) <= tier_filter]

    if not data:
        print("[!] No extractions found matching tier filter")
        return

    # Group by source
    by_source = defaultdict(list)
    for item in data:
        src = item["metadata"].get("source", "unknown")
        by_source[src].append(item)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    all_results = []

    for source, items in sorted(by_source.items()):
        if len(items) < 2:
            continue

        category = get_source_category(source)
        print(f"\n{'='*60}")
        print(f"SOURCE: {source} ({category})")
        print(f"  {len(items)} extractors, generating {len(items)*(len(items)-1)//2} pairs")
        print(f"{'='*60}")

        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                ext_a = items[i]["metadata"].get("extractor", "?")
                ext_b = items[j]["metadata"].get("extractor", "?")
                ops_a = [op["name"] for op in items[i]["operators"]]
                ops_b = [op["name"] for op in items[j]["operators"]]

                if not ops_a or not ops_b:
                    print(f"  [{ext_a} x {ext_b}] SKIP (empty operator list)")
                    continue

                print(f"  [{ext_a} x {ext_b}] Matching {len(ops_a)} vs {len(ops_b)} operators...",
                      end=" ", flush=True)

                if args.dry_run:
                    print("DRY RUN")
                    continue

                try:
                    matches = call_matcher(ops_a, ops_b)
                    stats = compute_ordering_stats(matches)

                    result = {
                        "source": source,
                        "category": category,
                        "extractor_a": ext_a,
                        "extractor_b": ext_b,
                        "ops_a_count": len(ops_a),
                        "ops_b_count": len(ops_b),
                        "matches": matches,
                        "ordering": stats,
                    }
                    all_results.append(result)

                    n = stats["n_matched"]
                    rho = stats["rank_correlation"]
                    pres = stats.get("preservation_rate")
                    print(f"OK  matched={n}  rho={rho}  order_preserved={pres}")

                except Exception as e:
                    print(f"FAILED: {e}")

    if not all_results and not args.dry_run:
        print("\n[!] No results generated")
        return

    if args.dry_run:
        print(f"\n[DRY RUN] Would process {sum(1 for s, items in by_source.items() if len(items) >= 2 for i in range(len(items)) for j in range(i+1, len(items)))} pairs")
        return

    # Save results
    out_file = output_dir / f"semantic_matches_{timestamp}.json"
    out_file.write_text(json.dumps(all_results, indent=2), encoding="utf-8")
    print(f"\nResults saved to: {out_file.name}")

    # Summary
    print(f"\n{'='*60}")
    print("TEST B: SEMANTIC MATCHING SUMMARY")
    print(f"{'='*60}")

    by_cat = defaultdict(list)
    for r in all_results:
        by_cat[r["category"]].append(r)

    for cat in ["dig_site", "h_baseline", "g_baseline", "neg_control"]:
        results = by_cat.get(cat, [])
        if not results:
            continue
        rhos = [r["ordering"]["rank_correlation"] for r in results
                if r["ordering"]["rank_correlation"] is not None]
        pres_rates = [r["ordering"]["preservation_rate"] for r in results
                      if r["ordering"].get("preservation_rate") is not None]
        matched_counts = [r["ordering"]["n_matched"] for r in results]

        print(f"\n  {cat.upper()} ({len(results)} pairs):")
        if rhos:
            print(f"    Rank correlation (rho): min={min(rhos):.3f}  "
                  f"max={max(rhos):.3f}  mean={sum(rhos)/len(rhos):.3f}")
        if pres_rates:
            print(f"    Order preservation: min={min(pres_rates):.3f}  "
                  f"max={max(pres_rates):.3f}  mean={sum(pres_rates)/len(pres_rates):.3f}")
        print(f"    Matched operators: min={min(matched_counts)}  "
              f"max={max(matched_counts)}  mean={sum(matched_counts)/len(matched_counts):.1f}")

    # THE TEST: do dig-site pairs have more consistent ordering than neg-H?
    dig_rhos = [r["ordering"]["rank_correlation"] for r in by_cat.get("dig_site", [])
                if r["ordering"]["rank_correlation"] is not None]
    h_rhos = [r["ordering"]["rank_correlation"] for r in by_cat.get("h_baseline", [])
              if r["ordering"]["rank_correlation"] is not None]

    if dig_rhos and h_rhos:
        dig_mean = sum(dig_rhos) / len(dig_rhos)
        h_mean = sum(h_rhos) / len(h_rhos)
        print(f"\n  {'='*50}")
        print(f"  TEST B VERDICT:")
        print(f"    Dig-site mean rho: {dig_mean:.3f}")
        print(f"    Neg-H mean rho:    {h_mean:.3f}")
        print(f"    Delta:             {dig_mean - h_mean:.3f}")
        if dig_mean > h_mean + 0.1:
            print(f"    --> DIG SITES SHOW MORE CONSISTENT ORDERING")
            print(f"    --> Operator ordering IS a discriminating signal")
        elif abs(dig_mean - h_mean) <= 0.1:
            print(f"    --> INCONCLUSIVE (delta < 0.1)")
        else:
            print(f"    --> NEG-H HAS EQUAL OR BETTER ORDERING")
            print(f"    --> Ordering does NOT discriminate (H-baseline survives)")


def main():
    parser = argparse.ArgumentParser(description="Operator Sequence Analysis & Blinded Matching")
    subparsers = parser.add_subparsers(dest="command")

    inv = subparsers.add_parser("inventory", help="Show extraction inventory")
    inv.add_argument("--dir", help="Extractions directory")

    ext = subparsers.add_parser("extract", help="Extract operator lists as JSON")
    ext.add_argument("--dir", help="Extractions directory")
    ext.add_argument("--source", help="Filter by source name (substring match)")
    ext.add_argument("--tier", help="Filter by tier (1-4)")

    bld = subparsers.add_parser("blind", help="Generate blinded pairs for matching protocol")
    bld.add_argument("--dir", help="Extractions directory")
    bld.add_argument("--tier", help="Max tier to include (default: all)")
    bld.add_argument("--seed", default="42", help="Random seed for shuffling")

    sts = subparsers.add_parser("stats", help="Compute sequence statistics for Test B")
    sts.add_argument("--dir", help="Extractions directory")
    sts.add_argument("--tier", help="Max tier to include (default: 2)")

    mtch = subparsers.add_parser("match", help="Semantic matching via LLM (Test B core)")
    mtch.add_argument("--dir", help="Extractions directory")
    mtch.add_argument("--tier", help="Max tier to include (default: 1 = Tier 1 only)")
    mtch.add_argument("--dry-run", action="store_true", help="Show what would be matched without API calls")

    args = parser.parse_args()

    if args.command == "inventory":
        cmd_inventory(args)
    elif args.command == "extract":
        cmd_extract(args)
    elif args.command == "blind":
        cmd_blind(args)
    elif args.command == "stats":
        cmd_stats(args)
    elif args.command == "match":
        cmd_match(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
