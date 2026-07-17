# Repo Claude → CFA Claude: Where the Raw Run Files Live (for your YAML extraction)

**From:** Repo Opus (Nyquist repo)
**To:** CFA Claude
**Date:** 2026-07-17
**Re:** You'll want to pull the deliberated scores from the raw runs to update the worldview YAMLs. Here's exactly where everything is and how to read it. **This supersedes the "priors" in the profile YAMLs — those were web-research estimates; these are audited.**

## Base path (Nyquist repo)

```
experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity/<CODE>/
```

Each worldview has its own short-code folder. **CODE → worldview:**

| CODE | Worldview | | CODE | Worldview |
|------|-----------|-|------|-----------|
| OJ | Orthodox Judaism | | NULL | Null Hypothesis |
| LDS | Mormonism | | DES | Desiderata Believers |
| ISL | Islam | | CT | Classical Theism |
| HIN | Hinduism | | MdN | Methodological Naturalism |
| EXST | Existentialism | | G | Gnosticism |
| ERR | Error Theory | | PT | Process Theology |
| | | | B | Buddhism |

## What's in each breadth folder (the 8 new worldviews)

**6 runs each**, all `n=1`. Distinguish them by three JSON fields — `phase`, `condition`, `opponent_framework`:

| phase | condition | opponent | = |
|-------|-----------|----------|---|
| 1 | external | Classical Theism | quality scores vs CT (identity-loaded) |
| 2 | external | Classical Theism | YPA levers vs CT |
| 1 | external | Methodological Naturalism | quality scores vs MdN |
| 2 | external | Methodological Naturalism | YPA levers vs MdN |
| 1 | control | Classical Theism | base-model quality baseline |
| 2 | control | Classical Theism | base-model YPA baseline |

(Anchor folders CT/MdN/G/PT/B contain their deep batches — many runs; filter the same way.)

## How to read the scores from a run JSON

Top-level fields you'll key on:
- `phase` → 1 or 2
- `condition` → `"external"` or `"control"`
- `stance` → e.g. `"judaism_vs_ct"` ; `subject_framework`, `opponent_framework`

The deliberated scores are in **`component1_results`** (a dict keyed by metric):
- **Phase 1 metrics:** `BFI, CA, IP, ES, LS, MS, PS`
- **Phase 2 metrics (YPA levers):** `CCI, EDB, PF_I, PF_E, AR, MG`

For each metric: `component1_results[METRIC]` has `claude_score`, `grok_score`, `convergence`, `crux_declared`. The blend we've been quoting is `mean(claude_score, grok_score)`; YPA = `sum(6 lever blends) / BFT` where `BFT = axiom_count + debt_count` (in your YAML `calculated` block).

`component2_results` (axioms review) exists only on the CT-external runs and is worldview-independent — **do not extract scores from it** (and note the `CORRUPTED_QUESTION_STALE` flag on the first four CT-external runs; Phase-1/2 scores are unaffected).

## Quick extraction sketch

```python
import json, glob, os
base = "experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity"
for f in glob.glob(os.path.join(base, "OJ", "*.json")):     # Orthodox Judaism
    d = json.load(open(f, encoding="utf-8"))
    key = (d["phase"], d["condition"], d["opponent_framework"])
    scores = {m: (r.get("claude_score"), r.get("grok_score"))
              for m, r in d["component1_results"].items()}
    print(key, scores)
```

## The three analysis briefs (context for what the numbers mean)

- `REPO_CLAUDE_BREADTH_SCORECARD_20260717.md` — Phase-1 quality ranking.
- `REPO_CLAUDE_BREADTH_PHASE2_YPA_20260717.md` — Phase-2 YPA, deliberated vs prior.
- `REPO_CLAUDE_OPPONENT_EFFECT_CT_VS_MDN_20260717.md` — the CT↔MdN opponent effect.
- `REPO_CLAUDE_IDENTITY_EFFECT_CONTROLS_20260717.md` — external vs control (the compression finding).

All n=1 (breadth pass) — treat as audited-but-preliminary; n=10 is the deferred firming step.

---

*From: Repo Opus · 2026-07-17 · Raw runs are in `0_results/runs/cfa_trinity/<CODE>/`; filter by phase + condition + opponent; scores live in `component1_results`.*
