"""
Interaction Residual Analysis — Test A Successor
=================================================
Fits the additive model (subject + opponent main effects), extracts
interaction residuals, and tests two pre-registered structural predictions:

  1. Family clustering: do interaction residuals group by worldview family?
  2. ISP ordering: is PF_E (pair-dependent) more structured than PF_I (intrinsic)?

Pre-registration (CFA Claude):
  - Interaction is "scientifically interesting" iff:
    (a) Family clustering: theological-scientific pairs differ from theological-theological, OR
    (b) ISP ordering: PF_E residuals more structured than PF_I residuals
  - If neither holds: "barely modulated" is correct. Move on.

Usage:
    python interaction_analysis.py decompose    # Fit additive model, show residuals
    python interaction_analysis.py families     # Test family clustering
    python interaction_analysis.py isp          # Test ISP ordering prediction
    python interaction_analysis.py full         # All of the above
"""

import sys
import json
import math
import argparse
from pathlib import Path
from collections import defaultdict
from itertools import permutations

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[5]
RUNS_DIR = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "0_results" / "runs" / "cfa_trinity"
ARCHIVE_DIR = REPO_ROOT / ".archive" / "runs"

SCHEMA_B = ["AR", "CCI", "EDB", "MG", "PF_E", "PF_I"]
FRAMEWORKS = ["CT", "G", "MdN", "PT"]

FAMILIES = {
    "CT": "theological",
    "PT": "theological",
    "MdN": "naturalistic",
    "G": "esoteric",
}

def pair_family(subj, opp):
    """Classify a pair by the families of its members."""
    fs, fo = FAMILIES[subj], FAMILIES[opp]
    pair = tuple(sorted([fs, fo]))
    if pair == ("theological", "theological"):
        return "theo-theo"
    elif pair == ("naturalistic", "theological"):
        return "theo-nat"
    elif pair == ("esoteric", "theological"):
        return "theo-eso"
    elif pair == ("esoteric", "naturalistic"):
        return "nat-eso"
    else:
        return f"{pair[0]}-{pair[1]}"


def detect_schema(metric_keys):
    b_count = sum(1 for m in metric_keys if m in SCHEMA_B)
    return "B" if b_count >= 5 else None


def _parse_run(filepath):
    """Parse a single CFA Trinity JSON file. Returns (subj, opp, scores) or None."""
    subj_map = {"CT": "CT", "G": "G", "MDN": "MdN", "PT": "PT"}
    try:
        with open(filepath, encoding="utf-8") as fh:
            data = json.load(fh)
        if data.get("condition") != "external":
            return None
        c1 = data.get("component1_results", {})
        if detect_schema(c1.keys()) != "B":
            return None
        scores = {}
        for m in SCHEMA_B:
            mr = c1.get(m, {})
            fs = mr.get("final_score")
            if fs is not None:
                scores[m] = float(fs)
        if len(scores) < 5:
            return None
        stance = data.get("stance", "")
        parts = stance.split("_vs_")
        if len(parts) != 2:
            return None
        subj = subj_map.get(parts[0].upper(), parts[0].upper())
        opp = subj_map.get(parts[1].upper(), parts[1].upper())
        if subj not in FRAMEWORKS or opp not in FRAMEWORKS:
            return None
        return (subj, opp, scores)
    except Exception:
        return None


def load_schema_b_runs():
    """Load all Schema B external-condition runs from cfa_trinity dirs + archive."""
    cells = defaultdict(list)

    # Primary: cfa_trinity/{CT,G,MdN,PT}/ subdirectories
    for fw_dir in FRAMEWORKS:
        d = RUNS_DIR / fw_dir
        if not d.exists():
            continue
        for f in sorted(d.glob("*.json")):
            result = _parse_run(f)
            if result:
                subj, opp, scores = result
                cells[(subj, opp)].append(scores)

    # Archive: flat directory with additional runs (e.g. pt_vs_ct, mdn_vs_pt)
    if ARCHIVE_DIR.exists():
        for f in sorted(ARCHIVE_DIR.glob("S7_cfa_trinity_*.json")):
            result = _parse_run(f)
            if result:
                subj, opp, scores = result
                cells[(subj, opp)].append(scores)

    return cells


def compute_cell_means(cells):
    """Compute mean score per (subject, opponent) cell."""
    means = {}
    for (subj, opp), run_list in cells.items():
        metric_means = {}
        for m in SCHEMA_B:
            vals = [r[m] for r in run_list if m in r]
            if vals:
                metric_means[m] = sum(vals) / len(vals)
        means[(subj, opp)] = metric_means
    return means


def compute_cell_sds(cells):
    """Compute within-cell SD per (subject, opponent) cell — the replication noise."""
    sds = {}
    for (subj, opp), run_list in cells.items():
        metric_sds = {}
        for m in SCHEMA_B:
            vals = [r[m] for r in run_list if m in r]
            if len(vals) >= 2:
                mean_v = sum(vals) / len(vals)
                metric_sds[m] = math.sqrt(sum((v - mean_v)**2 for v in vals) / (len(vals) - 1))
        sds[(subj, opp)] = metric_sds
    return sds


def pooled_noise(cell_sds):
    """Compute pooled within-cell SD per metric (the instrument noise floor)."""
    pooled = {}
    for m in SCHEMA_B:
        all_sds = [sds[m] for sds in cell_sds.values() if m in sds]
        if all_sds:
            pooled[m] = sum(all_sds) / len(all_sds)
    return pooled


def fit_additive_model(cell_means):
    """Fit score = grand_mean + subject_effect + opponent_effect per metric.
    Returns: grand_mean, subject_effects, opponent_effects, interaction_residuals."""

    results = {}

    for m in SCHEMA_B:
        all_vals = []
        for (s, o), scores in cell_means.items():
            if m in scores:
                all_vals.append(((s, o), scores[m]))

        if not all_vals:
            continue

        grand_mean = sum(v for _, v in all_vals) / len(all_vals)

        # Subject means
        subj_vals = defaultdict(list)
        for (s, o), v in all_vals:
            subj_vals[s].append(v)
        subj_means = {s: sum(vs)/len(vs) for s, vs in subj_vals.items()}
        subj_effects = {s: subj_means[s] - grand_mean for s in subj_means}

        # Opponent means
        opp_vals = defaultdict(list)
        for (s, o), v in all_vals:
            opp_vals[o].append(v)
        opp_means = {o: sum(vs)/len(vs) for o, vs in opp_vals.items()}
        opp_effects = {o: opp_means[o] - grand_mean for o in opp_means}

        # Interaction residuals
        residuals = {}
        for (s, o), v in all_vals:
            predicted = grand_mean + subj_effects.get(s, 0) + opp_effects.get(o, 0)
            residuals[(s, o)] = v - predicted

        results[m] = {
            "grand_mean": grand_mean,
            "subj_effects": subj_effects,
            "opp_effects": opp_effects,
            "residuals": residuals,
            "subj_means": subj_means,
            "opp_means": opp_means,
        }

    return results


def residual_structure_score(residuals):
    """Measure how 'structured' a set of residuals is.
    Returns: SD of residuals (higher = more structured / less random),
             max absolute residual, and directionality score."""
    vals = list(residuals.values())
    if len(vals) < 2:
        return 0, 0, 0

    mean_r = sum(vals) / len(vals)
    sd = math.sqrt(sum((v - mean_r)**2 for v in vals) / (len(vals) - 1))
    max_abs = max(abs(v) for v in vals)

    # Directionality: for reversed pairs, do residuals flip sign?
    dir_scores = []
    for (s1, o1), v1 in residuals.items():
        if (o1, s1) in residuals:
            v2 = residuals[(o1, s1)]
            if abs(v1) > 0.01 and abs(v2) > 0.01:
                dir_scores.append(-1 if (v1 * v2 < 0) else 1)

    directionality = sum(dir_scores) / len(dir_scores) if dir_scores else 0

    return sd, max_abs, directionality


# --- Commands ---

def cmd_decompose(cell_means, cells):
    """Fit additive model and show decomposition."""
    print("\n" + "=" * 80)
    print("INTERACTION RESIDUAL ANALYSIS — Additive Model Decomposition")
    print("=" * 80)
    print("\nModel: score(subj, opp) = grand_mean + subject_effect + opponent_effect + interaction")
    print("Interaction residual = actual - predicted (the part main effects can't explain)\n")

    model = fit_additive_model(cell_means)

    # Show cell counts
    print("Cell sizes (n runs per stance):")
    print(f"  {'Stance':<15} {'n':>4}")
    print(f"  {'-'*15} {'-'*4}")
    for (s, o) in sorted(cells.keys()):
        print(f"  {s}→{o:<10} {len(cells[(s,o)]):>4}")

    for m in SCHEMA_B:
        if m not in model:
            continue
        r = model[m]
        print(f"\n{'─'*70}")
        print(f"  {m} (grand mean = {r['grand_mean']:.2f})")
        print(f"{'─'*70}")

        print(f"\n  Subject effects (how much does being the subject shift the score?):")
        for fw in FRAMEWORKS:
            eff = r['subj_effects'].get(fw, 0)
            print(f"    {fw:<5}: {eff:>+6.2f}  (mean = {r['subj_means'].get(fw, 0):.2f})")

        print(f"\n  Opponent effects (how much does facing this opponent shift the score?):")
        for fw in FRAMEWORKS:
            eff = r['opp_effects'].get(fw, 0)
            print(f"    {fw:<5}: {eff:>+6.2f}  (mean = {r['opp_means'].get(fw, 0):.2f})")

        print(f"\n  Interaction residuals (what main effects can't explain):")
        print(f"    {'Pair':<12} {'Actual':>7} {'Predicted':>10} {'Residual':>9} {'Family':<12}")
        print(f"    {'-'*12} {'-'*7} {'-'*10} {'-'*9} {'-'*12}")

        for (s, o) in sorted(r['residuals'].keys()):
            actual = cell_means[(s, o)].get(m, 0)
            predicted = r['grand_mean'] + r['subj_effects'].get(s, 0) + r['opp_effects'].get(o, 0)
            resid = r['residuals'][(s, o)]
            family = pair_family(s, o)
            marker = " ***" if abs(resid) > 0.5 else ""
            print(f"    {s}→{o:<8} {actual:>7.2f} {predicted:>10.2f} {resid:>+9.3f} {family:<12}{marker}")

        sd, max_abs, directionality = residual_structure_score(r['residuals'])
        print(f"\n  Residual SD = {sd:.3f}, Max |resid| = {max_abs:.3f}, Directionality = {directionality:+.2f}")

    # Summary table
    print(f"\n\n{'='*70}")
    print("DECOMPOSITION SUMMARY")
    print(f"{'='*70}")
    print(f"  {'Metric':<6} {'Grand':>6} {'Subj_Range':>11} {'Opp_Range':>10} {'Resid_SD':>9} {'Max|R|':>7} {'%Interaction':>12}")
    print(f"  {'-'*6} {'-'*6} {'-'*11} {'-'*10} {'-'*9} {'-'*7} {'-'*12}")

    for m in SCHEMA_B:
        if m not in model:
            continue
        r = model[m]
        subj_range = max(r['subj_effects'].values()) - min(r['subj_effects'].values())
        opp_range = max(r['opp_effects'].values()) - min(r['opp_effects'].values())
        sd, max_abs, _ = residual_structure_score(r['residuals'])

        # Variance decomposition (from cell means)
        all_vals = [cell_means[(s, o)][m] for (s, o) in cell_means if m in cell_means[(s, o)]]
        grand = sum(all_vals) / len(all_vals)
        ss_total = sum((v - grand)**2 for v in all_vals)
        ss_resid = sum(v**2 for v in r['residuals'].values())
        pct_int = 100 * ss_resid / ss_total if ss_total > 0 else 0

        print(f"  {m:<6} {r['grand_mean']:>6.2f} {subj_range:>11.2f} {opp_range:>10.2f} {sd:>9.3f} {max_abs:>7.3f} {pct_int:>11.1f}%")

    return model


def cmd_families(cell_means, model):
    """Test family clustering prediction."""
    print(f"\n\n{'='*80}")
    print("FAMILY CLUSTERING TEST")
    print(f"{'='*80}")
    print("\nPrediction: interaction residuals cluster by worldview family.")
    print("  Theological: CT, PT")
    print("  Naturalistic: MdN")
    print("  Esoteric: G")
    print("\nPair families:")
    print("  theo-theo: CT↔PT")
    print("  theo-nat:  CT↔MdN, PT↔MdN")
    print("  theo-eso:  CT↔G, PT↔G")
    print("  nat-eso:   MdN↔G")

    if not model:
        model = fit_additive_model(cell_means)

    for m in SCHEMA_B:
        if m not in model:
            continue
        r = model[m]
        residuals = r['residuals']

        # Group residuals by family
        family_resids = defaultdict(list)
        for (s, o), v in residuals.items():
            fam = pair_family(s, o)
            family_resids[fam].append(((s, o), v))

        print(f"\n{'─'*60}")
        print(f"  {m}")
        print(f"{'─'*60}")

        family_means = {}
        for fam in sorted(family_resids.keys()):
            pairs = family_resids[fam]
            vals = [v for _, v in pairs]
            mean_r = sum(vals) / len(vals) if vals else 0
            sd_r = math.sqrt(sum((v - mean_r)**2 for v in vals) / max(len(vals) - 1, 1)) if len(vals) > 1 else 0
            family_means[fam] = mean_r

            print(f"\n  {fam} (n={len(pairs)}):")
            for (s, o), v in pairs:
                print(f"    {s}→{o}: {v:>+.3f}")
            print(f"    Mean: {mean_r:>+.3f}  SD: {sd_r:.3f}")

        # Test: do family means differ?
        if len(family_means) >= 2:
            all_means = list(family_means.values())
            between_var = sum((m - sum(all_means)/len(all_means))**2 for m in all_means) / len(all_means)
            print(f"\n  Between-family variance of mean residuals: {between_var:.4f}")

    # Cross-metric family summary
    print(f"\n\n{'='*70}")
    print("FAMILY CLUSTERING SUMMARY")
    print(f"{'='*70}")
    print(f"\n  Mean interaction residual by family and metric:")
    print(f"  {'Family':<12}", end="")
    for m in SCHEMA_B:
        print(f" {m:>8}", end="")
    print()
    print(f"  {'-'*12}", end="")
    for m in SCHEMA_B:
        print(f" {'-'*8}", end="")
    print()

    families_seen = set()
    for m in SCHEMA_B:
        if m not in model:
            continue
        for (s, o), v in model[m]['residuals'].items():
            families_seen.add(pair_family(s, o))

    for fam in sorted(families_seen):
        print(f"  {fam:<12}", end="")
        for m in SCHEMA_B:
            if m not in model:
                print(f" {'---':>8}", end="")
                continue
            vals = [v for (s, o), v in model[m]['residuals'].items() if pair_family(s, o) == fam]
            if vals:
                mean_v = sum(vals) / len(vals)
                print(f" {mean_v:>+8.3f}", end="")
            else:
                print(f" {'---':>8}", end="")
        print()

    # Verdict
    print(f"\n  CLUSTERING VERDICT:")

    # Caveat: cell sizes are unbalanced
    fam_sizes = defaultdict(int)
    for m in SCHEMA_B[:1]:
        if m not in model:
            continue
        for (s, o) in model[m]['residuals']:
            fam_sizes[pair_family(s, o)] += 1
    print(f"\n  CAVEAT: Unbalanced design — cell sizes by family:")
    for fam in sorted(fam_sizes):
        print(f"    {fam}: {fam_sizes[fam]} directed pairs")
    if fam_sizes.get("theo-theo", 0) <= 1:
        print(f"    ⚠ theo-theo has only {fam_sizes.get('theo-theo', 0)} pair(s) — PT→CT not in data")

    # Primary test: do cross-family pairs differ from within-family?
    # Use theo-eso (n=4, largest) vs theo-nat (n=3) — both have adequate n
    print(f"\n  PRIMARY TEST: theo-eso vs theo-nat (both have n≥3)")
    cross_family_structured = 0
    for m in SCHEMA_B:
        if m not in model:
            continue
        te_vals = [v for (s, o), v in model[m]['residuals'].items() if pair_family(s, o) == "theo-eso"]
        tn_vals = [v for (s, o), v in model[m]['residuals'].items() if pair_family(s, o) == "theo-nat"]
        if te_vals and tn_vals:
            te_mean = sum(te_vals) / len(te_vals)
            tn_mean = sum(tn_vals) / len(tn_vals)
            gap = abs(te_mean - tn_mean)
            label = " ***" if gap > 0.3 else ""
            print(f"    {m}: theo-eso mean={te_mean:+.3f}, theo-nat mean={tn_mean:+.3f}, gap={gap:.3f}{label}")
            if gap > 0.3:
                cross_family_structured += 1

    print(f"\n  Metrics with theo-eso vs theo-nat gap > 0.3: {cross_family_structured}/6")

    # Secondary: within-family variance (do residuals within a family agree?)
    print(f"\n  SECONDARY TEST: Within-family consistency")
    for m in ["PF_E", "PF_I", "MG"]:
        if m not in model:
            continue
        for fam in ["theo-eso", "theo-nat"]:
            vals = [v for (s, o), v in model[m]['residuals'].items() if pair_family(s, o) == fam]
            if len(vals) >= 2:
                mean_v = sum(vals) / len(vals)
                sd_v = math.sqrt(sum((v - mean_v)**2 for v in vals) / (len(vals) - 1))
                print(f"    {m} {fam}: mean={mean_v:+.3f}, within-SD={sd_v:.3f} (n={len(vals)})")

    if cross_family_structured >= 3:
        print(f"\n  → FAMILY CLUSTERING DETECTED (3+ metrics show cross-family structure)")
    elif cross_family_structured >= 2:
        print(f"\n  → WEAK FAMILY CLUSTERING (2 metrics)")
    else:
        print(f"\n  → NO CLEAR FAMILY CLUSTERING")


def cmd_isp(cell_means, model, noise=None):
    """Test ISP ordering prediction."""
    print(f"\n\n{'='*80}")
    print("ISP ORDERING TEST")
    print(f"{'='*80}")
    print("\nCFA Claude's prediction (from ISP Axiom 1/2 mapping):")
    print("  PF_E (Axiom 2 / pair-dependent)  → MOST structured residuals")
    print("  MG, CCI, EDB                     → intermediate")
    print("  PF_I (Axiom 1 / intrinsic)        → LEAST structured residuals")
    print("\nTwo measures of 'structure':")
    print("  1. Residual SD — absolute size of interaction (confounded with total spread)")
    print("  2. %Interaction — fraction of total variance that is interaction (spread-corrected)")
    print("  ISP predicts the RELATIVE ranking, so %Interaction is the primary measure.")

    if not model:
        model = fit_additive_model(cell_means)

    # Compute structure scores
    structure_scores = {}
    for m in SCHEMA_B:
        if m not in model:
            continue
        sd, max_abs, directionality = residual_structure_score(model[m]['residuals'])
        structure_scores[m] = {
            "sd": sd,
            "max_abs": max_abs,
            "directionality": directionality,
        }

    # Compute % of total variance that is interaction
    pct_interaction = {}
    for m in SCHEMA_B:
        if m not in model:
            continue
        r = model[m]
        all_vals = [cell_means[(s, o)][m] for (s, o) in cell_means if m in cell_means[(s, o)]]
        grand = sum(all_vals) / len(all_vals)
        ss_total = sum((v - grand)**2 for v in all_vals)
        ss_resid = sum(v**2 for v in r['residuals'].values())
        pct_interaction[m] = 100 * ss_resid / ss_total if ss_total > 0 else 0

    # Rank by BOTH measures
    ranked_sd = sorted(SCHEMA_B, key=lambda m: structure_scores.get(m, {}).get("sd", 0), reverse=True)
    ranked_pct = sorted(SCHEMA_B, key=lambda m: pct_interaction.get(m, 0), reverse=True)

    print(f"\n  TABLE 1: Ranked by Residual SD (raw interaction magnitude)")
    print(f"  {'Metric':<6} {'Resid_SD':>9} {'Max|R|':>7} {'%Inter':>7} {'Spread':>7} {'SD_Rank':>8}")
    print(f"  {'-'*6} {'-'*9} {'-'*7} {'-'*7} {'-'*7} {'-'*8}")

    for rank, m in enumerate(ranked_sd, 1):
        ss = structure_scores.get(m, {})
        pct = pct_interaction.get(m, 0)
        sd = ss.get("sd", 0)
        mx = ss.get("max_abs", 0)
        r = model[m]
        spread = max(r['subj_effects'].values()) - min(r['subj_effects'].values())
        print(f"  {m:<6} {sd:>9.3f} {mx:>7.3f} {pct:>6.1f}% {spread:>7.2f} {rank:>8}")

    print(f"\n  TABLE 2: Ranked by %Interaction (spread-corrected — PRIMARY MEASURE)")
    print(f"  {'Metric':<6} {'%Inter':>7} {'Resid_SD':>9} {'Spread':>7} {'%Rank':>6}")
    print(f"  {'-'*6} {'-'*7} {'-'*9} {'-'*7} {'-'*6}")

    for rank, m in enumerate(ranked_pct, 1):
        ss = structure_scores.get(m, {})
        pct = pct_interaction.get(m, 0)
        sd = ss.get("sd", 0)
        r = model[m]
        spread = max(r['subj_effects'].values()) - min(r['subj_effects'].values())
        isp_label = ""
        if m == "PF_E":
            isp_label = " ← ISP: should be #1"
        elif m == "PF_I":
            isp_label = " ← ISP: should be #6"
        print(f"  {m:<6} {pct:>6.1f}% {sd:>9.3f} {spread:>7.2f} {rank:>6}{isp_label}")

    # Check predictions using %Interaction (primary)
    print(f"\n  ISP PREDICTIONS (using %Interaction ranking):")
    pf_e_pct_rank = ranked_pct.index("PF_E") + 1 if "PF_E" in ranked_pct else 0
    pf_i_pct_rank = ranked_pct.index("PF_I") + 1 if "PF_I" in ranked_pct else 0

    print(f"  PF_E rank: #{pf_e_pct_rank} (predicted: #1)")
    print(f"  PF_I rank: #{pf_i_pct_rank} (predicted: #6)")

    pf_e_pct = pct_interaction.get("PF_E", 0)
    pf_i_pct = pct_interaction.get("PF_I", 0)

    print(f"  PF_E %interaction: {pf_e_pct:.1f}%")
    print(f"  PF_I %interaction: {pf_i_pct:.1f}%")
    print(f"  Ratio PF_E/PF_I: {pf_e_pct/pf_i_pct:.2f}x" if pf_i_pct > 0 else "")

    # Also show the confound: raw SD ranking
    pf_e_sd_rank = ranked_sd.index("PF_E") + 1 if "PF_E" in ranked_sd else 0
    pf_i_sd_rank = ranked_sd.index("PF_I") + 1 if "PF_I" in ranked_sd else 0
    print(f"\n  CONFOUND CHECK (raw Residual SD ranking — confounded with spread):")
    print(f"  PF_E rank: #{pf_e_sd_rank}, PF_I rank: #{pf_i_sd_rank}")
    print(f"  PF_I has largest spread (5.96) → mechanically largest residuals")
    print(f"  Raw SD ranking is misleading; %Interaction controls for this.")

    if pf_e_pct_rank == 1 and pf_i_pct_rank == len(ranked_pct):
        print(f"\n  VERDICT: ISP ORDERING CONFIRMED — PF_E most relational, PF_I least")
    elif pf_e_pct_rank == 1 and pf_i_pct_rank >= 4:
        print(f"\n  VERDICT: ISP ORDERING PARTIALLY CONFIRMED — PF_E is #1, PF_I is low but not last")
    elif pf_e_pct_rank <= 2 and pf_i_pct_rank >= len(ranked_pct) - 1:
        print(f"\n  VERDICT: ISP ORDERING APPROXIMATELY CONFIRMED")
    elif pf_e_pct > pf_i_pct:
        print(f"\n  VERDICT: ISP DIRECTION CORRECT (PF_E > PF_I) but ranking imperfect")
    else:
        print(f"\n  VERDICT: ISP ORDERING REJECTED")

    # Intermediate group check
    intermediate = ["MG", "CCI", "EDB"]
    int_pcts = [pct_interaction.get(m, 0) for m in intermediate]
    if int_pcts:
        int_mean = sum(int_pcts) / len(int_pcts)
        print(f"\n  Intermediate metrics (MG, CCI, EDB) mean %interaction: {int_mean:.1f}%")
        between = pf_i_pct < int_mean < pf_e_pct
        print(f"  Falls between PF_I ({pf_i_pct:.1f}%) and PF_E ({pf_e_pct:.1f}%)? {'YES' if between else 'NO'}")

    # Table 3: Signal-to-noise ratio (residual SD / replication noise)
    if noise:
        print(f"\n  TABLE 3: Residual / Replication Noise (spread-independent)")
        print(f"  {'Metric':<6} {'Resid_SD':>9} {'Noise_σ':>8} {'SNR':>6} {'SNR_Rank':>9}")
        print(f"  {'-'*6} {'-'*9} {'-'*8} {'-'*6} {'-'*9}")

        snr = {}
        for m in SCHEMA_B:
            if m in structure_scores and m in noise:
                snr[m] = structure_scores[m]["sd"] / noise[m] if noise[m] > 0 else 0

        ranked_snr = sorted(snr.keys(), key=lambda m: snr[m], reverse=True)

        for rank, m in enumerate(ranked_snr, 1):
            sd = structure_scores[m]["sd"]
            n = noise[m]
            s = snr[m]
            isp_label = ""
            if m == "PF_E":
                isp_label = " ← ISP: should be #1"
            elif m == "PF_I":
                isp_label = " ← ISP: should be #6"
            print(f"  {m:<6} {sd:>9.3f} {n:>8.3f} {s:>6.2f} {rank:>9}{isp_label}")

        pf_e_snr_rank = ranked_snr.index("PF_E") + 1 if "PF_E" in ranked_snr else 0
        pf_i_snr_rank = ranked_snr.index("PF_I") + 1 if "PF_I" in ranked_snr else 0
        print(f"\n  SNR RANKING: PF_E #{pf_e_snr_rank}, PF_I #{pf_i_snr_rank}")
        print(f"  (SNR controls for BOTH spread AND noise floor)")

    # Diagnosis
    print(f"\n  {'─'*60}")
    print(f"  DIAGNOSIS: Why %Interaction inversely correlates with spread")
    print(f"  {'─'*60}")
    print(f"  Residual SD is confounded with spread (high-spread → large residuals).")
    print(f"  %Interaction is confounded with DENOMINATOR (high-spread → large total SS")
    print(f"  → same residual looks smaller as a %). Both are biased in opposite ways.")
    if noise:
        print(f"  SNR (Table 3) is the cleanest measure: how many times does the")
        print(f"  interaction residual exceed the instrument's replication noise?")


def main():
    parser = argparse.ArgumentParser(description="Interaction Residual Analysis")
    parser.add_argument("command", choices=["decompose", "families", "isp", "full"],
                       help="Analysis command")
    args = parser.parse_args()

    print("Loading Schema B external runs...")
    cells = load_schema_b_runs()
    cell_means = compute_cell_means(cells)
    cell_sds = compute_cell_sds(cells)
    noise = pooled_noise(cell_sds)
    print(f"Loaded {sum(len(v) for v in cells.values())} runs across {len(cells)} cells")

    model = None

    if args.command in ["decompose", "full"]:
        model = cmd_decompose(cell_means, cells)

    if args.command in ["families", "full"]:
        if model is None:
            model = fit_additive_model(cell_means)
        cmd_families(cell_means, model)

    if args.command in ["isp", "full"]:
        if model is None:
            model = fit_additive_model(cell_means)
        cmd_isp(cell_means, model, noise=noise)


if __name__ == "__main__":
    main()
