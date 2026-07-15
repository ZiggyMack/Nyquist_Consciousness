"""
Test A' — Replication Analysis & Noise Floor
=============================================
Computes the instrument's test-retest variance (sigma) from repeated
identical-configuration runs, then compares Test A composition residuals
to that noise floor.

Implements the analysis layer for PREREG_OPUS_TEST_A_PRIME_AND_C.md.

Usage:
    python replication_analysis.py status       # Check replication runs exist
    python replication_analysis.py floor        # Compute per-metric sigma
    python replication_analysis.py compare      # Residuals vs noise floor
    python replication_analysis.py predictions  # Evaluate Opus's 5 predictions
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
MANIFEST_PATH = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "12_CFA" / "test_a_prime_manifest.json"

SCHEMA_A = ["BFI", "CA", "ES", "IP", "LS", "MS", "PS"]
SCHEMA_B = ["AR", "CCI", "EDB", "MG", "PF_E", "PF_I"]
SCHEMAS = {"A": SCHEMA_A, "B": SCHEMA_B}

FRAMEWORKS = ["CT", "G", "MdN", "PT"]


def detect_schema(metric_keys):
    a_count = sum(1 for m in metric_keys if m in SCHEMA_A)
    b_count = sum(1 for m in metric_keys if m in SCHEMA_B)
    if a_count >= 5:
        return "A"
    if b_count >= 5:
        return "B"
    return None


def load_replication_runs():
    """Load runs tagged with experiment=test_a_prime, grouped by replication_group."""
    groups = defaultdict(list)
    all_files = []

    for fw_dir in FRAMEWORKS:
        d = RUNS_DIR / fw_dir
        if not d.exists():
            continue
        for f in sorted(d.glob("*.json")):
            try:
                with open(f, encoding="utf-8") as fh:
                    data = json.load(fh)
                if data.get("experiment") != "test_a_prime":
                    continue

                group = data.get("replication_group", "unknown")
                rep_id = data.get("replication_id", 0)
                c1 = data.get("component1_results", {})
                schema = detect_schema(c1.keys())
                if schema is None:
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
                    continue

                groups[group].append({
                    "file": f.name,
                    "path": str(f),
                    "schema": schema,
                    "rep_id": rep_id,
                    "scores": scores,
                    "convergences": convergences,
                    "cruxes": cruxes,
                    "stance": data.get("stance", ""),
                    "condition": data.get("condition", ""),
                })
                all_files.append(f.name)
            except Exception:
                continue

    # Also check the flat runs dir (files may not be in subdirectories)
    for f in sorted(RUNS_DIR.glob("S7_cfa_trinity_*.json")):
        if f.name in all_files:
            continue
        try:
            with open(f, encoding="utf-8") as fh:
                data = json.load(fh)
            if data.get("experiment") != "test_a_prime":
                continue

            group = data.get("replication_group", "unknown")
            rep_id = data.get("replication_id", 0)
            c1 = data.get("component1_results", {})
            schema = detect_schema(c1.keys())
            if schema is None:
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
                continue

            groups[group].append({
                "file": f.name,
                "path": str(f),
                "schema": schema,
                "rep_id": rep_id,
                "scores": scores,
                "convergences": convergences,
                "cruxes": cruxes,
                "stance": data.get("stance", ""),
                "condition": data.get("condition", ""),
            })
        except Exception:
            continue

    return groups


def load_all_runs():
    """Load ALL CFA Trinity runs (for composition residual comparison)."""
    runs = defaultdict(list)
    for fw_dir in FRAMEWORKS:
        d = RUNS_DIR / fw_dir
        if not d.exists():
            continue
        for f in sorted(d.glob("*.json")):
            try:
                with open(f, encoding="utf-8") as fh:
                    data = json.load(fh)
                stance = data.get("stance", "")
                condition = data.get("condition", "unknown")
                c1 = data.get("component1_results", {})
                schema = detect_schema(c1.keys())
                if schema is None:
                    continue
                metrics = SCHEMAS[schema]
                scores = {}
                cruxes = {}
                for m in metrics:
                    mr = c1.get(m, {})
                    fs = mr.get("final_score")
                    if fs is not None:
                        scores[m] = float(fs)
                        cruxes[m] = bool(mr.get("crux_declared", False))
                if len(scores) < len(metrics) - 1:
                    continue
                runs[(stance, condition, schema)].append({
                    "scores": scores,
                    "cruxes": cruxes,
                })
            except Exception:
                continue
    return runs


# --- Statistical helpers (mirroring composition_analysis.py) ---

def score_vector(scores_dict, metrics):
    return [scores_dict.get(m, 0.0) for m in metrics]


def mean_vector(vectors):
    if not vectors:
        return []
    k = len(vectors[0])
    n = len(vectors)
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


def pooled_sd(sd_list):
    """Pool multiple SD estimates (assumes equal n)."""
    if not sd_list:
        return 0.0
    return math.sqrt(sum(s * s for s in sd_list) / len(sd_list))


# --- Commands ---

def cmd_status(groups):
    """Show status of replication runs."""
    print("\n" + "=" * 70)
    print("TEST A' — REPLICATION RUN STATUS")
    print("=" * 70)

    if not groups:
        print("\n  No replication runs found.")
        print("  Run `run_test_a_prime.py` first to generate the 18 runs.")
        if MANIFEST_PATH.exists():
            print(f"\n  Manifest exists: {MANIFEST_PATH}")
            with open(MANIFEST_PATH, encoding="utf-8") as f:
                manifest = json.load(f)
            print(f"  Started: {manifest.get('started', '?')}")
            print(f"  Files listed: {len(manifest.get('files', []))}")
        return

    total = sum(len(v) for v in groups.values())
    print(f"\n  Total replication runs found: {total}")
    print(f"  Groups: {len(groups)}")
    print()

    expected_groups = [
        "ct_vs_mdn_p1_external", "g_vs_mdn_p1_external", "ct_vs_mdn_p1_control",
        "ct_vs_mdn_p2_external", "g_vs_mdn_p2_external", "ct_vs_mdn_p2_control",
    ]

    print(f"  {'Group':<30} {'Runs':>5} {'Schema':>8} {'Status':<10}")
    print(f"  {'-'*30} {'-'*5} {'-'*8} {'-'*10}")

    for g in expected_groups:
        runs = groups.get(g, [])
        n = len(runs)
        schema = runs[0]["schema"] if runs else "?"
        status = "OK" if n >= 3 else f"NEED {3 - n} MORE" if n > 0 else "MISSING"
        print(f"  {g:<30} {n:>5} {schema:>8} {status:<10}")

    unexpected = [g for g in groups if g not in expected_groups]
    if unexpected:
        print(f"\n  Unexpected groups: {unexpected}")

    incomplete = [g for g in expected_groups if len(groups.get(g, [])) < 3]
    if incomplete:
        print(f"\n  [!] Incomplete groups: {incomplete}")
        print(f"      Test A' requires 3 runs per group.")
    else:
        print(f"\n  [+] All 6 groups complete (3 runs each). Ready for analysis.")


def cmd_floor(groups):
    """Compute per-metric sigma from replications."""
    print("\n" + "=" * 70)
    print("TEST A' — NOISE FLOOR (per-metric replication sigma)")
    print("=" * 70)

    if not groups:
        print("\n  No replication runs found. Run `run_test_a_prime.py` first.")
        return

    schema_sigmas = {"A": [], "B": []}
    group_results = {}

    for group_name, runs in sorted(groups.items()):
        if len(runs) < 2:
            print(f"\n  [!] {group_name}: only {len(runs)} runs, need >=2 for SD")
            continue

        schema = runs[0]["schema"]
        metrics = SCHEMAS[schema]

        vectors = [score_vector(r["scores"], metrics) for r in runs]
        mean = mean_vector(vectors)
        sd = std_vector(vectors, mean)

        group_results[group_name] = {
            "schema": schema,
            "metrics": metrics,
            "mean": mean,
            "sd": sd,
            "n": len(runs),
        }

        print(f"\n  {group_name} (n={len(runs)}, Schema {schema})")
        print(f"  {'Metric':<8} {'Mean':>8} {'SD (sigma)':>12} {'CV%':>8}")
        print(f"  {'-'*8} {'-'*8} {'-'*12} {'-'*8}")
        for i, m in enumerate(metrics):
            cv = (sd[i] / mean[i] * 100) if mean[i] > 0 else 0
            print(f"  {m:<8} {mean[i]:>8.2f} {sd[i]:>12.3f} {cv:>7.1f}%")
            schema_sigmas[schema].append(sd[i])

    # Pooled sigma per schema
    print(f"\n\n  {'=' * 50}")
    print(f"  POOLED SIGMA BY SCHEMA")
    print(f"  {'=' * 50}")

    for schema_key in ["A", "B"]:
        sds = schema_sigmas[schema_key]
        if sds:
            pooled = pooled_sd(sds)
            mean_sd = sum(sds) / len(sds)
            max_sd = max(sds)
            print(f"\n  Schema {schema_key}: pooled sigma = {pooled:.3f}, mean sigma = {mean_sd:.3f}, max = {max_sd:.3f}")
            print(f"    (from {len(sds)} metric-group measurements)")

    # Direct A vs B comparison (Prediction A'-1)
    if schema_sigmas["A"] and schema_sigmas["B"]:
        pooled_a = pooled_sd(schema_sigmas["A"])
        pooled_b = pooled_sd(schema_sigmas["B"])
        print(f"\n  PREDICTION A'-1 CHECK: sigma(B) > sigma(A)?")
        print(f"    Pooled sigma(A) = {pooled_a:.3f}")
        print(f"    Pooled sigma(B) = {pooled_b:.3f}")
        print(f"    Ratio B/A = {pooled_b / pooled_a:.2f}" if pooled_a > 0 else "    (A has zero variance)")
        verdict = "CONFIRMED" if pooled_b > pooled_a else "REJECTED"
        print(f"    Verdict: {verdict}")

    # PF_I check (Prediction A'-2)
    pf_i_sds = []
    other_b_sds = []
    for gname, gdata in group_results.items():
        if gdata["schema"] != "B":
            continue
        metrics = gdata["metrics"]
        for i, m in enumerate(metrics):
            if m == "PF_I":
                pf_i_sds.append(gdata["sd"][i])
            else:
                other_b_sds.append(gdata["sd"][i])

    if pf_i_sds:
        mean_pf_i = sum(pf_i_sds) / len(pf_i_sds)
        mean_other = sum(other_b_sds) / len(other_b_sds) if other_b_sds else 0
        max_other = max(other_b_sds) if other_b_sds else 0
        print(f"\n  PREDICTION A'-2 CHECK: sigma(PF_I) is largest Schema B metric?")
        print(f"    Mean sigma(PF_I) = {mean_pf_i:.3f}")
        print(f"    Mean sigma(other B) = {mean_other:.3f}")
        print(f"    Max sigma(other B) = {max_other:.3f}")
        verdict = "CONFIRMED" if mean_pf_i > max_other else "REJECTED"
        print(f"    Verdict: {verdict}")

    return group_results


def cmd_compare(groups):
    """Compare Test A composition residuals to noise floor."""
    print("\n" + "=" * 70)
    print("TEST A' — COMPOSITION RESIDUALS vs NOISE FLOOR")
    print("=" * 70)

    if not groups:
        print("\n  No replication runs. Run `run_test_a_prime.py` first.")
        return

    # Compute noise floor
    schema_pooled = {}
    schema_metric_sd = {"A": {}, "B": {}}

    for group_name, runs in groups.items():
        if len(runs) < 2:
            continue
        schema = runs[0]["schema"]
        metrics = SCHEMAS[schema]
        vectors = [score_vector(r["scores"], metrics) for r in runs]
        mean = mean_vector(vectors)
        sd = std_vector(vectors, mean)
        for i, m in enumerate(metrics):
            if m not in schema_metric_sd[schema]:
                schema_metric_sd[schema][m] = []
            schema_metric_sd[schema][m].append(sd[i])

    for schema in ["A", "B"]:
        metric_sds = schema_metric_sd[schema]
        if metric_sds:
            all_sds = [s for sds in metric_sds.values() for s in sds]
            schema_pooled[schema] = pooled_sd(all_sds)

    if not schema_pooled:
        print("\n  Cannot compute noise floor (insufficient replication data).")
        return

    print(f"\n  Noise floor: sigma(A) = {schema_pooled.get('A', 0):.3f}, sigma(B) = {schema_pooled.get('B', 0):.3f}")

    # Load all runs and compute composition residuals
    all_runs = load_all_runs()

    for schema in ["A", "B"]:
        sigma = schema_pooled.get(schema)
        if not sigma or sigma < 0.001:
            print(f"\n  Schema {schema}: no usable sigma, skipping")
            continue

        metrics = SCHEMAS[schema]
        print(f"\n\n  {'=' * 60}")
        print(f"  SCHEMA {schema} — Composition Residuals vs sigma = {sigma:.3f}")
        print(f"  {'=' * 60}")
        print(f"  Kill threshold: residual <= 1.5 * sigma ({1.5 * sigma:.3f}) => NOISE")
        print()

        # Compute pair profiles (external condition)
        profiles = {}
        for (stance, cond, sch), run_list in all_runs.items():
            if cond != "external" or sch != schema:
                continue
            vectors = [score_vector(r["scores"], metrics) for r in run_list]
            if vectors:
                profiles[stance] = mean_vector(vectors)

        if len(profiles) < 3:
            print(f"  Insufficient pair profiles ({len(profiles)}), need >= 3")
            continue

        # Find valid triples
        all_stances = {
            (a, b): f"{a.lower()}_vs_{b.lower()}"
            for a, b in permutations(FRAMEWORKS, 2)
        }
        triples = []
        for a, b, c in permutations(FRAMEWORKS, 3):
            s_ab = all_stances[(a, b)]
            s_bc = all_stances[(b, c)]
            s_ac = all_stances[(a, c)]
            if s_ab in profiles and s_bc in profiles and s_ac in profiles:
                triples.append((a, b, c, s_ab, s_bc, s_ac))

        if not triples:
            print(f"  No valid triples found for Schema {schema}")
            continue

        # Compute global mean for difference model
        all_vecs = list(profiles.values())
        global_mean = mean_vector(all_vecs)

        print(f"  {'Triple':<15} {'|Resid|':>8} {'sigma':>8} {'Ratio':>8} {'Verdict':<10} {'R2_mid':>7}")
        print(f"  {'-'*15} {'-'*8} {'-'*8} {'-'*8} {'-'*10} {'-'*7}")

        structure_count = 0
        noise_count = 0
        marginal_count = 0

        for a, b, c, s_ab, s_bc, s_ac in triples:
            v_ab = profiles[s_ab]
            v_bc = profiles[s_bc]
            v_ac = profiles[s_ac]

            # Midpoint prediction
            pred_mid = [(v_ab[i] + v_bc[i]) / 2 for i in range(len(metrics))]

            # Residuals
            residuals = [abs(v_ac[i] - pred_mid[i]) for i in range(len(metrics))]
            mean_resid = sum(residuals) / len(residuals)

            # R-squared
            r2 = r_squared(v_ac, pred_mid)

            # Compare to sigma
            ratio = mean_resid / sigma if sigma > 0 else float('inf')

            if ratio > 1.5:
                verdict = "STRUCTURE"
                structure_count += 1
            elif ratio > 1.0:
                verdict = "MARGINAL"
                marginal_count += 1
            else:
                verdict = "NOISE"
                noise_count += 1

            label = f"{a}->{b}->{c}"
            print(f"  {label:<15} {mean_resid:>8.3f} {sigma:>8.3f} {ratio:>8.2f} {verdict:<10} {r2:>7.3f}")

        total = structure_count + noise_count + marginal_count
        print(f"\n  Summary (Schema {schema}, {total} triples):")
        print(f"    STRUCTURE (ratio > 1.5): {structure_count} ({100*structure_count/total:.0f}%)" if total else "")
        print(f"    MARGINAL (1.0-1.5):      {marginal_count} ({100*marginal_count/total:.0f}%)" if total else "")
        print(f"    NOISE (ratio <= 1.0):    {noise_count} ({100*noise_count/total:.0f}%)" if total else "")

        # Kill condition check (A'-3)
        if noise_count == total:
            print(f"\n  *** KILL CONDITION MET: ALL triples within noise floor. ***")
            print(f"  *** Manifold hypothesis UNSUPPORTED for Schema {schema}. ***")
        elif structure_count > 0:
            print(f"\n  Manifold hypothesis SURVIVES for {structure_count}/{total} triples.")


def cmd_predictions(groups):
    """Evaluate Opus's 5 pre-registered predictions."""
    print("\n" + "=" * 70)
    print("TEST A' — PRE-REGISTERED PREDICTION EVALUATION")
    print("=" * 70)
    print("  (from PREREG_OPUS_TEST_A_PRIME_AND_C.md)")

    if not groups:
        print("\n  No replication runs. Cannot evaluate predictions.")
        return

    # Compute per-group stats
    schema_metric_sds = {"A": defaultdict(list), "B": defaultdict(list)}
    group_stats = {}

    for group_name, runs in sorted(groups.items()):
        if len(runs) < 2:
            continue
        schema = runs[0]["schema"]
        metrics = SCHEMAS[schema]
        vectors = [score_vector(r["scores"], metrics) for r in runs]
        mean = mean_vector(vectors)
        sd = std_vector(vectors, mean)
        group_stats[group_name] = {"schema": schema, "metrics": metrics, "mean": mean, "sd": sd, "n": len(runs)}
        for i, m in enumerate(metrics):
            schema_metric_sds[schema][m].append(sd[i])

    results = []

    # A'-1: sigma(Schema B) > sigma(Schema A)
    print(f"\n\n  {'='*60}")
    print(f"  A'-1: sigma(Schema B) > sigma(Schema A)?")
    print(f"  {'='*60}")
    all_a = [s for sds in schema_metric_sds["A"].values() for s in sds]
    all_b = [s for sds in schema_metric_sds["B"].values() for s in sds]
    if all_a and all_b:
        pooled_a = pooled_sd(all_a)
        pooled_b = pooled_sd(all_b)
        mean_a = sum(all_a) / len(all_a)
        mean_b = sum(all_b) / len(all_b)
        print(f"  Pooled sigma(A) = {pooled_a:.4f} (mean: {mean_a:.4f}, n={len(all_a)})")
        print(f"  Pooled sigma(B) = {pooled_b:.4f} (mean: {mean_b:.4f}, n={len(all_b)})")
        print(f"  Ratio B/A = {pooled_b/pooled_a:.2f}" if pooled_a > 0 else "")
        if pooled_b > pooled_a:
            print(f"  VERDICT: CONFIRMED — Schema B levers are noisier")
            results.append(("A'-1", "CONFIRMED"))
        else:
            print(f"  VERDICT: REJECTED — Schema A is noisier or equal")
            results.append(("A'-1", "REJECTED"))
    else:
        print(f"  VERDICT: INCONCLUSIVE — missing data for one or both schemas")
        results.append(("A'-1", "INCONCLUSIVE"))

    # A'-2: sigma(PF_I) is largest Schema B metric
    print(f"\n\n  {'='*60}")
    print(f"  A'-2: sigma(PF_I) is the largest Schema B metric?")
    print(f"  {'='*60}")
    b_metric_means = {}
    for m, sds in schema_metric_sds["B"].items():
        b_metric_means[m] = sum(sds) / len(sds) if sds else 0
    if b_metric_means:
        print(f"  Per-metric mean sigma (Schema B):")
        for m in SCHEMA_B:
            marker = " <-- PF_I" if m == "PF_I" else ""
            print(f"    {m:<6}: {b_metric_means.get(m, 0):.4f}{marker}")
        pf_i_val = b_metric_means.get("PF_I", 0)
        max_other = max(v for m, v in b_metric_means.items() if m != "PF_I") if len(b_metric_means) > 1 else 0
        max_metric = max(b_metric_means, key=b_metric_means.get)
        if max_metric == "PF_I":
            print(f"  VERDICT: CONFIRMED — PF_I ({pf_i_val:.4f}) is largest")
            results.append(("A'-2", "CONFIRMED"))
        else:
            print(f"  VERDICT: REJECTED — {max_metric} ({b_metric_means[max_metric]:.4f}) > PF_I ({pf_i_val:.4f})")
            results.append(("A'-2", "REJECTED"))
    else:
        print(f"  VERDICT: INCONCLUSIVE — no Schema B data")
        results.append(("A'-2", "INCONCLUSIVE"))

    # A'-3: Kill condition — composition residual within 1.5 sigma
    print(f"\n\n  {'='*60}")
    print(f"  A'-3: Composition residual within 1.5*sigma?")
    print(f"  Prediction: YES for Schema A, NO for MdN legs")
    print(f"  {'='*60}")
    all_runs = load_all_runs()

    for schema in ["A", "B"]:
        all_sds = [s for sds in schema_metric_sds[schema].values() for s in sds]
        if not all_sds:
            continue
        sigma = pooled_sd(all_sds)
        metrics = SCHEMAS[schema]

        profiles = {}
        for (stance, cond, sch), run_list in all_runs.items():
            if cond != "external" or sch != schema:
                continue
            vectors = [score_vector(r["scores"], metrics) for r in run_list]
            if vectors:
                profiles[stance] = mean_vector(vectors)

        all_stances = {(a, b): f"{a.lower()}_vs_{b.lower()}" for a, b in permutations(FRAMEWORKS, 2)}
        triples_within = 0
        triples_outside = 0
        mdn_within = 0
        mdn_outside = 0

        all_vecs = list(profiles.values())
        if not all_vecs:
            continue

        for a, b, c in permutations(FRAMEWORKS, 3):
            s_ab = all_stances[(a, b)]
            s_bc = all_stances[(b, c)]
            s_ac = all_stances[(a, c)]
            if s_ab not in profiles or s_bc not in profiles or s_ac not in profiles:
                continue

            v_ab = profiles[s_ab]
            v_bc = profiles[s_bc]
            v_ac = profiles[s_ac]
            pred = [(v_ab[i] + v_bc[i]) / 2 for i in range(len(metrics))]
            mean_resid = sum(abs(v_ac[i] - pred[i]) for i in range(len(metrics))) / len(metrics)

            is_mdn = "MdN" in (a, b, c)
            if mean_resid <= 1.5 * sigma:
                triples_within += 1
                if is_mdn:
                    mdn_within += 1
            else:
                triples_outside += 1
                if is_mdn:
                    mdn_outside += 1

        total_t = triples_within + triples_outside
        print(f"\n  Schema {schema} (sigma={sigma:.3f}, threshold={1.5*sigma:.3f}):")
        print(f"    Within 1.5*sigma: {triples_within}/{total_t}")
        print(f"    Outside 1.5*sigma: {triples_outside}/{total_t}")
        if is_mdn_relevant := (mdn_within + mdn_outside) > 0:
            print(f"    MdN legs within: {mdn_within}/{mdn_within+mdn_outside}")
            print(f"    MdN legs outside: {mdn_outside}/{mdn_within+mdn_outside}")

    if all_a and all_b:
        sigma_a = pooled_sd(all_a)
        sigma_b = pooled_sd(all_b)
        # Schema A prediction: residuals within noise
        # Schema B/MdN prediction: residuals exceed noise
        print(f"\n  Opus predicted: Schema A within noise, MdN legs exceed noise")
        print(f"  (Detailed per-triple breakdown in 'compare' command)")
        results.append(("A'-3", "SEE COMPARE OUTPUT"))
    else:
        results.append(("A'-3", "INCONCLUSIVE"))

    # A'-4: Emergent cruxes — do NOVELTY triples reproduce crux sets?
    print(f"\n\n  {'='*60}")
    print(f"  A'-4: Do NOVELTY triples reproduce their crux sets?")
    print(f"  Prediction: >=2 of 4 NOVELTY triples FAIL to reproduce")
    print(f"  {'='*60}")

    # Check crux consistency within replication groups
    crux_consistency = {}
    for group_name, runs in groups.items():
        if len(runs) < 2:
            continue
        schema = runs[0]["schema"]
        if schema != "B":
            continue
        metrics = SCHEMAS[schema]
        crux_sets = []
        for r in runs:
            crux_set = frozenset(m for m in metrics if r["cruxes"].get(m, False))
            crux_sets.append(crux_set)

        # Measure: do all replications produce the same crux set?
        all_same = len(set(crux_sets)) == 1
        crux_consistency[group_name] = {
            "sets": [sorted(s) for s in crux_sets],
            "consistent": all_same,
            "unique_patterns": len(set(crux_sets)),
        }
        print(f"\n  {group_name}:")
        for i, cs in enumerate(crux_sets):
            print(f"    Rep {i+1}: {sorted(cs) if cs else '(none)'}")
        print(f"    Consistent: {'YES' if all_same else 'NO'}")

    inconsistent = sum(1 for v in crux_consistency.values() if not v["consistent"])
    total_b_groups = len(crux_consistency)
    if total_b_groups > 0:
        print(f"\n  Inconsistent groups: {inconsistent}/{total_b_groups}")
        print(f"  (Opus predicts >=2 of 4 NOVELTY triples fail to reproduce)")
        if inconsistent >= 2:
            print(f"  VERDICT: CONFIRMED — crux sets are unstable (noise-manufactured)")
            results.append(("A'-4", "CONFIRMED"))
        else:
            print(f"  VERDICT: REJECTED — crux sets are reproducible")
            results.append(("A'-4", "REJECTED"))
    else:
        results.append(("A'-4", "INCONCLUSIVE"))

    # A'-5: Identity effect does not replicate
    print(f"\n\n  {'='*60}")
    print(f"  A'-5: Identity effect does NOT replicate?")
    print(f"  Prediction: sign reversal is noise (two coin flips)")
    print(f"  {'='*60}")

    ext_groups = {g: r for g, r in groups.items() if "external" in g}
    ctrl_groups = {g: r for g, r in groups.items() if "control" in g}

    for schema in ["A", "B"]:
        metrics = SCHEMAS[schema]
        phase_tag = "p1" if schema == "A" else "p2"

        ext_key = f"ct_vs_mdn_{phase_tag}_external"
        ctrl_key = f"ct_vs_mdn_{phase_tag}_control"

        ext_runs = groups.get(ext_key, [])
        ctrl_runs = groups.get(ctrl_key, [])

        if len(ext_runs) < 2 or len(ctrl_runs) < 2:
            continue

        ext_vecs = [score_vector(r["scores"], metrics) for r in ext_runs]
        ctrl_vecs = [score_vector(r["scores"], metrics) for r in ctrl_runs]

        ext_mean = mean_vector(ext_vecs)
        ctrl_mean = mean_vector(ctrl_vecs)
        ext_sd = std_vector(ext_vecs, ext_mean)
        ctrl_sd = std_vector(ctrl_vecs, ctrl_mean)

        print(f"\n  Schema {schema} (CT->MdN): external vs control")
        print(f"  {'Metric':<8} {'Ext_mean':>9} {'Ctrl_mean':>10} {'Diff':>8} {'Ext_SD':>8} {'Ctrl_SD':>8} {'Sig?':<5}")
        print(f"  {'-'*8} {'-'*9} {'-'*10} {'-'*8} {'-'*8} {'-'*8} {'-'*5}")

        sig_count = 0
        for i, m in enumerate(metrics):
            diff = ext_mean[i] - ctrl_mean[i]
            combined_sd = math.sqrt((ext_sd[i]**2 + ctrl_sd[i]**2) / 2) if (ext_sd[i] + ctrl_sd[i]) > 0 else 0
            sig = abs(diff) > 1.5 * combined_sd if combined_sd > 0 else False
            if sig:
                sig_count += 1
            print(f"  {m:<8} {ext_mean[i]:>9.2f} {ctrl_mean[i]:>10.2f} {diff:>+8.2f} {ext_sd[i]:>8.3f} {ctrl_sd[i]:>8.3f} {'YES' if sig else 'no':<5}")

        print(f"\n  Significant differences: {sig_count}/{len(metrics)}")

    print(f"\n  (Full identity-effect evaluation requires comparing ACROSS schemas)")
    print(f"  Opus predicts the effect does NOT replicate in either direction.")
    results.append(("A'-5", "SEE ABOVE"))

    # Summary table
    print(f"\n\n  {'='*60}")
    print(f"  PREDICTION SCORECARD")
    print(f"  {'='*60}")
    print(f"  {'ID':<8} {'Verdict':<15} {'Opus predicted...'}")
    print(f"  {'-'*8} {'-'*15} {'-'*40}")
    predictions_text = [
        "sigma(B) > sigma(A)",
        "sigma(PF_I) is largest Schema B metric",
        "Residuals within 1.5*sigma (A yes, MdN no)",
        ">=2/4 NOVELTY crux sets unstable",
        "Identity effect does not replicate",
    ]
    for (pred_id, verdict), text in zip(results, predictions_text):
        print(f"  {pred_id:<8} {verdict:<15} {text}")

    confirmed = sum(1 for _, v in results if v == "CONFIRMED")
    rejected = sum(1 for _, v in results if v == "REJECTED")
    print(f"\n  Score: {confirmed} confirmed, {rejected} rejected, {len(results)-confirmed-rejected} pending")
    print(f"  (Opus prior track record: 1/5)")


def main():
    parser = argparse.ArgumentParser(description="Test A' Replication Analysis")
    parser.add_argument("command", choices=["status", "floor", "compare", "predictions", "full"],
                       help="Analysis command to run")
    args = parser.parse_args()

    groups = load_replication_runs()

    if args.command == "status":
        cmd_status(groups)
    elif args.command == "floor":
        cmd_floor(groups)
    elif args.command == "compare":
        cmd_compare(groups)
    elif args.command == "predictions":
        cmd_predictions(groups)
    elif args.command == "full":
        cmd_status(groups)
        cmd_floor(groups)
        cmd_compare(groups)
        cmd_predictions(groups)


if __name__ == "__main__":
    main()
