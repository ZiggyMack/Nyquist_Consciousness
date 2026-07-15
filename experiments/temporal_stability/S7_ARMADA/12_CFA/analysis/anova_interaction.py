"""
anova_interaction.py — Type III ANOVA on raw CFA Trinity runs.

Replaces the n=10 cell-mean variance decomposition (browser Opus's MAIN_EFFECT_CHECK
brief) with a proper Type III ANOVA on individual runs, per metric:

    score ~ C(subject, Sum) + C(opponent, Sum) + C(subject, Sum):C(opponent, Sum)

The question it settles: how much of each CFA metric's variance is INTERACTION
(subject x opponent) — the term where a "manifold" would live — versus main effects
(subject/opponent) and residual noise?

Design notes:
- Sum (deviation) coding so anova_lm(typ=3) yields genuine Type III sums of squares.
- The design is inherently incomplete: no self-pairs (subject != opponent), so the
  subject x opponent grid has an empty diagonal. Type III on present cells still
  partitions variance correctly; cell counts are reported for transparency.
- Residual RMSE is printed beside every interaction estimate ("All Measured, All Floored").

Run:  py analysis/anova_interaction.py
Reads: 0_results/runs/cfa_trinity/{CT,G,MdN,PT,B,Framework_G,pre_schema}/*.json
Writes: analysis/anova_interaction_results.json
"""

import json
import glob
import os
import sys
import warnings
from pathlib import Path

import pandas as pd
import statsmodels.formula.api as smf
from statsmodels.stats.anova import anova_lm

# ASCII-only console (Windows cp1252 safety)
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

SCHEMA_A = ["BFI", "CA", "ES", "IP", "LS", "MS", "PS"]
SCHEMA_B = ["AR", "CCI", "EDB", "MG", "PF_E", "PF_I"]
FOLDERS = ["CT", "G", "MdN", "PT", "B", "Framework_G", "pre_schema"]

RUNS_DIR = Path(__file__).resolve().parents[2] / "0_results" / "runs" / "cfa_trinity"
OUT_PATH = Path(__file__).resolve().parent / "anova_interaction_results.json"


def load_rows():
    """One row per run: subject, opponent, condition, schema, + metric final_scores."""
    rows = []
    for folder in FOLDERS:
        for f in sorted(glob.glob(str(RUNS_DIR / folder / "*.json"))):
            try:
                d = json.load(open(f, encoding="utf-8"))
            except Exception:
                continue
            c1 = d.get("component1_results") or {}
            keys = set(c1.keys())
            if set(SCHEMA_B) & keys:
                schema, metrics = "B", SCHEMA_B
            elif set(SCHEMA_A) & keys:
                schema, metrics = "A", SCHEMA_A
            else:
                continue
            row = {
                "file": os.path.basename(f),
                "folder": folder,
                "schema": schema,
                "subject": d.get("subject_framework"),
                "opponent": d.get("opponent_framework"),
                "condition": d.get("condition"),
                "stance": d.get("stance"),
            }
            for m in metrics:
                blk = c1.get(m) or {}
                row[m] = blk.get("final_score")
            rows.append(row)
    return pd.DataFrame(rows)


def _r2(formula, data):
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        return smf.ols(formula, data=data).fit().rsquared


def variance_decomposition(df, metrics, label):
    """
    Per-metric commonality decomposition via nested R^2. Coding-independent and
    identifiable even on this incomplete (empty-diagonal), unbalanced design --
    unlike Type I (which hands shared variance to whatever enters first) or Type III
    (which collapses main effects when the diagonal is empty).

        uniq_subject   = R2(subject+opponent) - R2(opponent)
        uniq_opponent  = R2(subject+opponent) - R2(subject)
        shared_main    = R2(subject+opponent) - uniq_subject - uniq_opponent
        interaction    = R2(subject*opponent) - R2(subject+opponent)   <- the manifold
        residual       = 1 - R2(subject*opponent)                      <- the noise floor
    These five sum to 1. Interaction here is the *unique* matchup-specific structure
    beyond an additive subject+opponent model.
    """
    print(f"\n{'='*78}\n{label}\n{'='*78}")
    n_cells = df.groupby(["subject", "opponent"]).size()
    print(f"N runs: {len(df)} | subjects: {sorted(df['subject'].dropna().unique())}")
    print(f"Non-empty subject x opponent cells: {len(n_cells)} "
          f"(range {n_cells.min()}-{n_cells.max()} runs/cell)")
    print(f"\n{'metric':<7}{'uSubj%':>8}{'uOpp%':>8}{'shared%':>9}{'interX%':>9}"
          f"{'resid%':>8}{'RMSE':>8}{'p_int':>11}")
    print("-" * 78)

    out = {}
    for m in metrics:
        sub = df.dropna(subset=[m, "subject", "opponent"]).copy()
        if sub["subject"].nunique() < 2 or sub["opponent"].nunique() < 2 or len(sub) < 12:
            out[m] = {"skipped": "insufficient data", "n": int(len(sub))}
            continue
        try:
            r2_s = _r2(f"{m} ~ C(subject)", sub)
            r2_o = _r2(f"{m} ~ C(opponent)", sub)
            r2_add = _r2(f"{m} ~ C(subject) + C(opponent)", sub)
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                add_fit = smf.ols(f"{m} ~ C(subject) + C(opponent)", data=sub).fit()
                full_fit = smf.ols(f"{m} ~ C(subject) * C(opponent)", data=sub).fit()
                cmp = anova_lm(add_fit, full_fit)
        except Exception as e:
            out[m] = {"error": str(e), "n": int(len(sub))}
            continue

        r2_full = full_fit.rsquared
        uniq_s = r2_add - r2_o
        uniq_o = r2_add - r2_s
        shared = r2_add - uniq_s - uniq_o          # = r2_s + r2_o - r2_add
        inter = r2_full - r2_add
        resid = 1.0 - r2_full
        rmse = (full_fit.ssr / full_fit.df_resid) ** 0.5 if full_fit.df_resid > 0 else float("nan")
        f_int = float(cmp["F"].iloc[1])
        p_int = float(cmp["Pr(>F)"].iloc[1])

        rec = {
            "n": int(len(sub)),
            "df_resid_full": float(full_fit.df_resid),
            "pct_uniq_subject": 100 * uniq_s,
            "pct_uniq_opponent": 100 * uniq_o,
            "pct_shared_main": 100 * shared,
            "pct_interaction": 100 * inter,
            "pct_residual": 100 * resid,
            "pct_additive_total": 100 * r2_add,
            "residual_rmse": rmse,
            "F_interaction": f_int,
            "p_interaction": p_int,
        }
        out[m] = rec
        print(f"{m:<7}{rec['pct_uniq_subject']:>7.1f}%{rec['pct_uniq_opponent']:>7.1f}%"
              f"{rec['pct_shared_main']:>8.1f}%{rec['pct_interaction']:>8.1f}%"
              f"{rec['pct_residual']:>7.1f}%{rmse:>8.3f}{p_int:>11.2e}")

    ranked = sorted(
        [(m, r["pct_interaction"]) for m, r in out.items() if "pct_interaction" in r],
        key=lambda x: -x[1],
    )
    if ranked:
        print("\nInteraction (unique matchup structure beyond additive), largest first:")
        for m, pct in ranked:
            add = out[m]["pct_additive_total"]
            print(f"  {m:<6} interaction={pct:5.1f}%  additive={add:5.1f}%  "
                  f"(p_int={out[m]['p_interaction']:.2e}, noise floor RMSE={out[m]['residual_rmse']:.3f})")
    return out


def main():
    if not RUNS_DIR.exists():
        print(f"ERROR: runs dir not found: {RUNS_DIR}")
        sys.exit(1)
    df = load_rows()
    print(f"Loaded {len(df)} runs from {RUNS_DIR}")
    print("Schema counts:", df["schema"].value_counts().to_dict())
    print("Condition counts:", df["condition"].value_counts().to_dict())

    results = {"n_runs_total": int(len(df)), "models": {}}

    b = df[df["schema"] == "B"]
    b_ext = b[b["condition"] == "external"]
    b_ctl = b[b["condition"] == "control"]

    results["models"]["schemaB_external"] = variance_decomposition(
        b_ext, SCHEMA_B, "PRIMARY: Schema B, condition=external")
    if len(b_ctl) >= 24:
        results["models"]["schemaB_control"] = variance_decomposition(
            b_ctl, SCHEMA_B, "SECONDARY: Schema B, condition=control")

    with open(OUT_PATH, "w", encoding="utf-8") as fh:
        json.dump(results, fh, indent=2)
    print(f"\nWrote {OUT_PATH}")


if __name__ == "__main__":
    main()
