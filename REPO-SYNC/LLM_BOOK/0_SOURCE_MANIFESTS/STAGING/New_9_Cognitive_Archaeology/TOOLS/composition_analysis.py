"""
Test A: Composition Regimes Analysis
=====================================
Do worldview transitions compose? For each triple (A, B, C),
classify the relationship between A->B, B->C, and A->C into regimes:
exact, approximate, fails, obstruction, novelty.

Usage:
    python composition_analysis.py inventory   # Show pair counts
    python composition_analysis.py profiles    # Compute pair score profiles
    python composition_analysis.py compose     # Run composition test on valid triples
    python composition_analysis.py full        # All of the above
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

SCHEMA_A = ["BFI", "CA", "ES", "IP", "LS", "MS", "PS"]
SCHEMA_B = ["AR", "CCI", "EDB", "MG", "PF_E", "PF_I"]
SCHEMAS = {"A": SCHEMA_A, "B": SCHEMA_B}

FRAMEWORKS = ["CT", "G", "MdN", "PT"]

ALL_STANCES = {
    (a, b): f"{a.lower()}_vs_{b.lower()}"
    for a, b in permutations(FRAMEWORKS, 2)
}


def detect_schema(metric_keys):
    """Determine which schema a run belongs to based on its metric keys."""
    a_count = sum(1 for m in metric_keys if m in SCHEMA_A)
    b_count = sum(1 for m in metric_keys if m in SCHEMA_B)
    if a_count >= 5:
        return "A"
    if b_count >= 5:
        return "B"
    return None


def load_runs():
    """Load all CFA Trinity JSON files, return structured data."""
    runs = defaultdict(list)
    errors = []
    total = 0
    skipped = 0

    for fw_dir in FRAMEWORKS:
        d = RUNS_DIR / fw_dir
        if not d.exists():
            continue
        for f in sorted(d.glob("*.json")):
            total += 1
            try:
                with open(f, encoding="utf-8") as fh:
                    data = json.load(fh)

                stance = data.get("stance", "")
                condition = data.get("condition", "unknown")
                c1 = data.get("component1_results", {})

                schema = detect_schema(c1.keys())
                if schema is None:
                    skipped += 1
                    continue

                metrics = SCHEMAS[schema]
                scores = {}
                convergences = {}
                cruxes = {}
                for m in metrics:
                    mr = c1.get(m, {})
                    fs = mr.get("final_score")
                    if fs is not None:
                        scores[m] = float(fs)
                        convergences[m] = float(mr.get("convergence", 0))
                        cruxes[m] = bool(mr.get("crux_declared", False))

                if len(scores) < len(metrics) - 1:
                    skipped += 1
                    continue

                runs[(stance, condition, schema)].append({
                    "file": f.name,
                    "scores": scores,
                    "convergences": convergences,
                    "cruxes": cruxes,
                })
            except Exception as e:
                errors.append((f.name, str(e)))

    return runs, total, skipped, errors


def score_vector(scores_dict, metrics):
    return [scores_dict.get(m, 0.0) for m in metrics]


def mean_vector(vectors):
    n = len(vectors)
    if n == 0:
        return []
    k = len(vectors[0])
    return [sum(v[i] for v in vectors) / n for i in range(k)]


def std_vector(vectors, mean):
    n = len(vectors)
    if n < 2:
        return [0.0] * len(mean)
    k = len(mean)
    return [
        math.sqrt(sum((v[i] - mean[i]) ** 2 for v in vectors) / (n - 1))
        for i in range(k)
    ]


def l2_norm(vec):
    return math.sqrt(sum(x * x for x in vec))


def pearson_r(a, b):
    n = len(a)
    if n < 3:
        return 0.0
    ma = sum(a) / n
    mb = sum(b) / n
    num = sum((x - ma) * (y - mb) for x, y in zip(a, b))
    da = math.sqrt(sum((x - ma) ** 2 for x in a))
    db = math.sqrt(sum((y - mb) ** 2 for y in b))
    if da < 1e-10 or db < 1e-10:
        return 0.0
    return num / (da * db)


def r_squared(actual, predicted):
    n = len(actual)
    if n < 2:
        return 0.0
    mean_a = sum(actual) / n
    ss_res = sum((a - p) ** 2 for a, p in zip(actual, predicted))
    ss_tot = sum((a - mean_a) ** 2 for a in actual)
    if ss_tot < 1e-10:
        return 0.0
    return 1.0 - ss_res / ss_tot


def compute_pair_profiles(runs, schema, condition="external"):
    """Compute mean score profiles for each directed pair within a schema."""
    metrics = SCHEMAS[schema]
    profiles = {}

    for (stance, cond, sch), run_list in runs.items():
        if cond != condition or sch != schema:
            continue

        vectors = [score_vector(r["scores"], metrics) for r in run_list]
        conv_vectors = [[r["convergences"].get(m, 0) for m in metrics] for r in run_list]
        crux_vectors = [[1 if r["cruxes"].get(m, False) else 0 for m in metrics] for r in run_list]

        mv = mean_vector(vectors)
        sv = std_vector(vectors, mv)
        mc = mean_vector(conv_vectors)
        crux_rate = mean_vector(crux_vectors)

        profiles[stance] = {
            "mean": mv,
            "std": sv,
            "mean_convergence": mc,
            "crux_rate": crux_rate,
            "n": len(run_list),
        }

    return profiles


def find_valid_triples(profiles):
    triples = []
    for a, b, c in permutations(FRAMEWORKS, 3):
        s_ab = ALL_STANCES[(a, b)]
        s_bc = ALL_STANCES[(b, c)]
        s_ac = ALL_STANCES[(a, c)]
        if s_ab in profiles and s_bc in profiles and s_ac in profiles:
            triples.append((a, b, c))
    return triples


def classify_regime(r2_mid, r2_diff, corr, triangle_ok, within_sd, crux_novel):
    r2_best = max(r2_mid, r2_diff)
    if not triangle_ok:
        return "OBSTRUCTION"
    if crux_novel:
        return "NOVELTY"
    if r2_best > 0.8 and within_sd:
        return "EXACT"
    if r2_best > 0.5 or corr > 0.7:
        return "APPROXIMATE"
    return "FAILS"


def run_composition_test(profiles, metrics):
    triples = find_valid_triples(profiles)
    if not profiles:
        return []
    global_mean = mean_vector([p["mean"] for p in profiles.values()])
    results = []

    for a, b, c in triples:
        s_ab = ALL_STANCES[(a, b)]
        s_bc = ALL_STANCES[(b, c)]
        s_ac = ALL_STANCES[(a, c)]

        v_ab = profiles[s_ab]["mean"]
        v_bc = profiles[s_bc]["mean"]
        v_ac = profiles[s_ac]["mean"]
        sd_ac = profiles[s_ac]["std"]
        k = len(metrics)

        pred_mid = [(x + y) / 2 for x, y in zip(v_ab, v_bc)]
        r2_mid = r_squared(v_ac, pred_mid)

        pred_diff = [x + (y - g) for x, y, g in zip(v_ab, v_bc, global_mean)]
        r2_diff = r_squared(v_ac, pred_diff)

        corr = pearson_r(v_ac, pred_mid)

        d_ab = l2_norm(v_ab)
        d_bc = l2_norm(v_bc)
        d_ac = l2_norm(v_ac)
        triangle_ok = d_ac <= d_ab + d_bc + 0.01

        within_sd = all(
            abs(v_ac[i] - pred_mid[i]) <= max(sd_ac[i], 0.5)
            for i in range(k)
        )

        cr_ab = profiles[s_ab]["crux_rate"]
        cr_bc = profiles[s_bc]["crux_rate"]
        cr_ac = profiles[s_ac]["crux_rate"]
        crux_novel = any(
            cr_ac[i] > 0.1 and cr_ab[i] < 0.05 and cr_bc[i] < 0.05
            for i in range(k)
        )

        regime = classify_regime(r2_mid, r2_diff, corr, triangle_ok, within_sd, crux_novel)

        results.append({
            "triple": f"{a}->{b}->{c}",
            "a_b": s_ab,
            "b_c": s_bc,
            "a_c": s_ac,
            "actual": v_ac,
            "pred_mid": pred_mid,
            "pred_diff": pred_diff,
            "r2_mid": r2_mid,
            "r2_diff": r2_diff,
            "corr": corr,
            "triangle_ok": triangle_ok,
            "within_sd": within_sd,
            "crux_novel": crux_novel,
            "regime": regime,
            "mae": sum(abs(ac - p) for ac, p in zip(v_ac, pred_mid)) / k,
        })

    return results


def cmd_inventory(runs, total, skipped, errors):
    print(f"\n{'='*60}")
    print(f"  CFA TRINITY DATA INVENTORY")
    print(f"{'='*60}")
    print(f"\n  Total JSON files: {total}")
    print(f"  Loaded (schema matched): {total - skipped - len(errors)}")
    print(f"  Skipped (incomplete/unknown schema): {skipped}")
    if errors:
        print(f"  Parse errors: {len(errors)}")

    for schema_name, metrics in SCHEMAS.items():
        print(f"\n  === SCHEMA {schema_name}: {metrics} ===")
        for condition in ["external", "control"]:
            print(f"\n  --- {condition.upper()} ---")
            print(f"  {'Stance':<20s}  {'Runs':>5s}")
            print(f"  {'-'*20}  {'-'*5}")
            for (stance, cond, sch), run_list in sorted(runs.items()):
                if cond != condition or sch != schema_name:
                    continue
                print(f"  {stance:<20s}  {len(run_list):>5d}")

        profiles = compute_pair_profiles(runs, schema_name, "external")
        triples = find_valid_triples(profiles)
        print(f"\n  Pairs with external data (Schema {schema_name}): {len(profiles)}")
        print(f"  Valid triples (Schema {schema_name}): {len(triples)}")

    print()


def cmd_profiles(runs):
    for schema_name, metrics in SCHEMAS.items():
        profiles = compute_pair_profiles(runs, schema_name, "external")
        if not profiles:
            continue

        print(f"\n{'='*70}")
        print(f"  PAIR SCORE PROFILES — Schema {schema_name} (external)")
        print(f"{'='*70}")

        header = f"  {'Stance':<18s}  {'n':>3s}"
        for m in metrics:
            header += f"  {m:>6s}"
        header += f"  {'Conv':>5s}  {'Crux%':>5s}"
        print(header)
        print(f"  {'-'*18}  {'-'*3}" + f"  {'-'*6}" * len(metrics) + f"  {'-'*5}  {'-'*5}")

        for stance in sorted(profiles.keys()):
            p = profiles[stance]
            line = f"  {stance:<18s}  {p['n']:>3d}"
            for i in range(len(metrics)):
                line += f"  {p['mean'][i]:>6.2f}"
            mean_conv = sum(p['mean_convergence']) / len(metrics)
            mean_crux = sum(p['crux_rate']) / len(metrics) * 100
            line += f"  {mean_conv:>5.2f}  {mean_crux:>5.1f}"
            print(line)

        print(f"\n  Standard Deviations:")
        for stance in sorted(profiles.keys()):
            p = profiles[stance]
            line = f"  {stance:<18s}  {p['n']:>3d}"
            for i in range(len(metrics)):
                line += f"  {p['std'][i]:>6.2f}"
            print(line)

    print()


def cmd_compose(runs):
    all_regime_counts = {}

    for schema_name, metrics in SCHEMAS.items():
        profiles = compute_pair_profiles(runs, schema_name, "external")
        results = run_composition_test(profiles, metrics)
        if not results:
            print(f"\n  Schema {schema_name}: No valid triples (insufficient pair coverage)")
            continue

        print(f"\n{'='*80}")
        print(f"  COMPOSITION REGIMES — Schema {schema_name}: {metrics}")
        print(f"{'='*80}")

        print(f"\n  {'Triple':<16s}  {'Regime':<14s}  {'R2mid':>6s}  {'R2diff':>6s}  {'Corr':>5s}  {'MAE':>5s}  {'Tri':>3s}  {'SD':>3s}  {'Crx':>3s}")
        print(f"  {'-'*16}  {'-'*14}  {'-'*6}  {'-'*6}  {'-'*5}  {'-'*5}  {'-'*3}  {'-'*3}  {'-'*3}")

        regime_counts = defaultdict(int)
        for r in results:
            regime_counts[r["regime"]] += 1
            tri = "Y" if r["triangle_ok"] else "N"
            sd = "Y" if r["within_sd"] else "N"
            crx = "Y" if r["crux_novel"] else "N"
            print(f"  {r['triple']:<16s}  {r['regime']:<14s}  {r['r2_mid']:>6.3f}  {r['r2_diff']:>6.3f}  {r['corr']:>5.3f}  {r['mae']:>5.2f}  {tri:>3s}  {sd:>3s}  {crx:>3s}")

        all_regime_counts[schema_name] = regime_counts

        print(f"\n  --- Regime Distribution ---")
        for regime in ["EXACT", "APPROXIMATE", "FAILS", "OBSTRUCTION", "NOVELTY"]:
            count = regime_counts.get(regime, 0)
            bar = "#" * count
            print(f"  {regime:<14s}  {count:>2d}  {bar}")

        print(f"\n  --- Per-Triple Diagnostics ---")
        for r in results:
            print(f"\n  {r['triple']}  [{r['regime']}]")
            print(f"    Legs: {r['a_b']} + {r['b_c']} => {r['a_c']}")
            print(f"    Actual  A->C: [{', '.join(f'{v:.2f}' for v in r['actual'])}]")
            print(f"    Pred (mid):   [{', '.join(f'{v:.2f}' for v in r['pred_mid'])}]")
            print(f"    Residuals:    [{', '.join(f'{a-p:+.2f}' for a, p in zip(r['actual'], r['pred_mid']))}]")
            print(f"    R2(mid)={r['r2_mid']:.3f}  R2(diff)={r['r2_diff']:.3f}  corr={r['corr']:.3f}  MAE={r['mae']:.2f}")

        total_ext = len(results)
        structured_ext = regime_counts.get("EXACT", 0) + regime_counts.get("APPROXIMATE", 0)

        # Control comparison
        ctrl_profiles = compute_pair_profiles(runs, schema_name, "control")
        ctrl_results = run_composition_test(ctrl_profiles, metrics)
        ctrl_regime_counts = defaultdict(int)
        for r in ctrl_results:
            ctrl_regime_counts[r["regime"]] += 1

        print(f"\n  --- Control Comparison (Schema {schema_name}) ---")
        print(f"  {'Regime':<14s}  {'External':>8s}  {'Control':>8s}")
        print(f"  {'-'*14}  {'-'*8}  {'-'*8}")
        for regime in ["EXACT", "APPROXIMATE", "FAILS", "OBSTRUCTION", "NOVELTY"]:
            ext = regime_counts.get(regime, 0)
            ctrl = ctrl_regime_counts.get(regime, 0)
            print(f"  {regime:<14s}  {ext:>8d}  {ctrl:>8d}")

        if ctrl_results:
            ctrl_structured = ctrl_regime_counts.get("EXACT", 0) + ctrl_regime_counts.get("APPROXIMATE", 0)
            total_ctrl = len(ctrl_results)
            print(f"\n  External structured: {structured_ext}/{total_ext} ({100*structured_ext/total_ext:.0f}%)")
            print(f"  Control structured:  {ctrl_structured}/{total_ctrl} ({100*ctrl_structured/total_ctrl:.0f}%)")
            ext_rate = structured_ext / total_ext
            ctrl_rate = ctrl_structured / total_ctrl
            if ext_rate > ctrl_rate + 0.15:
                print(f"  -> Identity-bearing runs compose MORE (framework identity matters)")
            elif ctrl_rate > ext_rate + 0.15:
                print(f"  -> Control composes MORE (composition is model-level, not identity-level)")
            else:
                print(f"  -> Similar rates (composition is substrate-level)")

    # Cross-schema summary
    if len(all_regime_counts) == 2:
        print(f"\n{'='*80}")
        print(f"  CROSS-SCHEMA COMPARISON")
        print(f"{'='*80}")
        print(f"  {'Regime':<14s}  {'Schema A':>10s}  {'Schema B':>10s}")
        print(f"  {'-'*14}  {'-'*10}  {'-'*10}")
        for regime in ["EXACT", "APPROXIMATE", "FAILS", "OBSTRUCTION", "NOVELTY"]:
            a_count = all_regime_counts.get("A", {}).get(regime, 0)
            b_count = all_regime_counts.get("B", {}).get(regime, 0)
            print(f"  {regime:<14s}  {a_count:>10d}  {b_count:>10d}")

        total_a = sum(all_regime_counts.get("A", {}).values())
        total_b = sum(all_regime_counts.get("B", {}).values())
        struct_a = all_regime_counts.get("A", {}).get("EXACT", 0) + all_regime_counts.get("A", {}).get("APPROXIMATE", 0)
        struct_b = all_regime_counts.get("B", {}).get("EXACT", 0) + all_regime_counts.get("B", {}).get("APPROXIMATE", 0)

        if total_a > 0 and total_b > 0:
            print(f"\n  Schema A: {struct_a}/{total_a} structured ({100*struct_a/total_a:.0f}%)")
            print(f"  Schema B: {struct_b}/{total_b} structured ({100*struct_b/total_b:.0f}%)")
            if abs(struct_a/total_a - struct_b/total_b) < 0.15:
                print(f"  -> Composition is metric-invariant (holds across measurement instruments)")
            else:
                print(f"  -> Composition is metric-dependent (different instruments see different structure)")

    # Final verdict
    print(f"\n{'='*80}")
    print(f"  FINAL VERDICT")
    print(f"{'='*80}")
    all_structured = sum(
        rc.get("EXACT", 0) + rc.get("APPROXIMATE", 0)
        for rc in all_regime_counts.values()
    )
    all_total = sum(sum(rc.values()) for rc in all_regime_counts.values())
    if all_total == 0:
        print(f"  No valid triples found. Cannot assess composition.")
    else:
        rate = all_structured / all_total
        print(f"  Total triples tested: {all_total}")
        print(f"  Compositional (EXACT + APPROXIMATE): {all_structured} ({100*rate:.0f}%)")
        if rate > 0.6:
            print(f"  CONCLUSION: Worldview transitions have algebraic structure.")
            print(f"  Transitions compose — knowing A->B and B->C predicts A->C.")
        elif rate > 0.3:
            print(f"  CONCLUSION: Partial compositional structure.")
            print(f"  Some transitions compose, others introduce novel dynamics.")
        else:
            print(f"  CONCLUSION: Composition fails.")
            print(f"  Each directed pair is largely independent.")
    print()


def main():
    parser = argparse.ArgumentParser(description="Test A: Composition Regimes Analysis")
    parser.add_argument("command", choices=["inventory", "profiles", "compose", "full"],
                        help="Command to run")
    args = parser.parse_args()

    print("Loading CFA Trinity data...")
    runs, total, skipped, errors = load_runs()

    if args.command == "inventory" or args.command == "full":
        cmd_inventory(runs, total, skipped, errors)

    if args.command == "profiles" or args.command == "full":
        cmd_profiles(runs)

    if args.command == "compose" or args.command == "full":
        cmd_compose(runs)


if __name__ == "__main__":
    main()
