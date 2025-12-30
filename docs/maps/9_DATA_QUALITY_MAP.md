<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - ../../experiments/temporal_stability/S7_ARMADA/0_results/
  - 1_ARMADA_MAP.md
impacts:
  - Experiment validity decisions
  - 0_MAP_OF_MAPS.md
keywords:
  - data_quality
  - validation
  - runs
  - gold_standard
  - invalidated
-->

# DATA QUALITY MAP — S7 ARMADA Experiments

**Purpose:** Authoritative reference for data quality across all S7 ARMADA runs. Know what you can trust before drawing conclusions.

**Version:** 2.0
**Date:** 2025-12-28
**Status:** ACTIVE REFERENCE

> **📐 METHODOLOGY NOTE:** This document spans three methodology eras: Discovery Era (Runs 006-013) used Keyword RMS drift with 5D metrics and EH ~1.23. Control-Systems Era (Runs 015-020B) added settling time, damping, and inherent drift analysis. Cosine Era (Run 023d) uses cosine embedding distance with EH = 0.80 (p=2.40e-23). For full methodology context, see [5_METHODOLOGY_DOMAINS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md).

> **📁 ARCHIVE NOTE:** Early run data (Runs 006-013) has been archived to `.archive/temporal_stability_Euclidean/`. Current active data is in `0_results/runs/`.

---

## CRITICAL WARNING

> **Runs 001-007 used a FAKE drift metric and are INVALID for quantitative claims.**
>
> The metric was: `drift = min(0.30, response_length / 5000)`
>
> This measured **response verbosity**, not identity. The "0.30 hard ceiling" was a **code cap**, not a discovery.

---

## Data Quality Summary

### Discovery Era (Keyword RMS) — ARCHIVED

| Run | Status | Quality | Valid For | Invalid For |
|-----|--------|---------|-----------|-------------|
| 001-005 | INVALIDATED | 0% | Nothing quantitative | All drift claims (fake metric) |
| **006** | GOLD | 100% | Provider comparisons, training fingerprints | — |
| 007 | INVALIDATED | 0% | Nothing quantitative | All drift claims (fake metric) |
| **008** | GOLD | 100% | Ground truth drift, baselines, metric validation | — |
| **009** | VALIDATED | 85% | Event Horizon (p<0.001), Claude trajectories | GPT/Gemini partial |
| 010 | PARTIAL | 60% | Drift values, meta-feedback quotes | Lambda/recovery (crashed) |
| 011 | INCONCLUSIVE | 50% | Drift sequences only | Statistical conclusions |
| **012** | GOLD | 100% | **Recovery Paradox** (100% crossed EH, 100% recovered) | — |
| **013** | GOLD | 100% | **Identity Confrontation Paradox** (direct probes = lower drift) | — |

### Control-Systems Era (Runs 015-020B)

| Run | Status | Quality | Valid For | Invalid For |
|-----|--------|---------|-----------|-------------|
| 014 | PARTIAL | 70% | ET Phone Home protocol | Limited sample |
| **015** | GOLD | 100% | Stability Criteria, boundary density | — |
| **016** | GOLD | 100% | **Settling Time Protocol** (τₛ = 6.1 turns) | — |
| **017** | GOLD | 100% | **Context Damping** (97.5% stability) | — |
| **018** | IRON CLAD | 100% | **184 files, 51 models, P-018-1/2/3 CONFIRMED** | — |
| 019 | VALIDATED | 90% | Live Ziggy fiction buffer | Peak ~0.50 only |
| **020A** | GOLD | 100% | Tribunal paradigm | — |
| **020B** | GOLD | 100% | **~93% Inherent Drift (Thermometer Result)** | — |

### Cosine Era (Run 023d) — CANONICAL

| Run | Status | Quality | Valid For | Invalid For |
|-----|--------|---------|-----------|-------------|
| **023d** | IRON CLAD | 100% | **EH=0.80, p=2.40e-23, 825+ files, 54 models** | —           |

---

## Detailed Run Analysis

### Runs 001-007: INVALIDATED

**The Problem:**
```python
# FAKE METRIC - This is what Runs 001-007 actually measured:
drift = min(0.30, response_length / 5000)
```

**What This Means:**
- All quantitative thresholds are meaningless
- The "0.30 pole ceiling" was a code artifact
- Claims about provider differences were measuring verbosity
- Qualitative observations MAY still be valid (model behavior patterns)

**Action Required:** Re-run with real 5D drift metric

---

### Run 006: THE ULTIMATE ARMADA — GOLD STANDARD

**Quality:** 100% PRISTINE

**Why Trustworthy:**
- 29 ships across 3 providers (Claude, GPT, Gemini)
- 174 total probes (87 baseline + 87 sonar)
- **100% success rate** — zero failures
- **Perfect data integrity** — all responses captured
- Dual-mode comparison (passive vs active boundary testing)

**Key Validated Findings:**
- Constitutional AI (Claude/Gemini): HARD UNIFORM BOUNDARIES
- RLHF (GPT): SOFTER VARIABLE BOUNDARIES
- Training philosophy creates measurable fingerprints
- Reasoning models (o-series) show NO superior stability

**Data Location:** `.archive/temporal_stability_Euclidean/S7_ARMADA/0_results/runs/legacy_runs/S7_armada_run_006.json`

**Safe to Use For:**
- Provider architecture comparisons
- Training philosophy fingerprint analysis
- Boundary uniformity studies
- Cross-model stability rankings

---

### Run 008: GROUND TRUTH CALIBRATION — GOLD STANDARD

**Quality:** 100% GOLD STANDARD

**Why Critical:**
- **First run with REAL drift metric** (5D: Pole Density, Zero Density, Meta Density, Identity Coherence, Hedging Ratio)
- Removed artificial 0.30 cap — revealed true drift range: 0.00 to 3.59
- 29 ships, 3 sequences each = 87 trajectories
- **100% success rate**

**Key Validated Findings:**
- Real drift range is 0-3.59 (NOT capped at 0.30)
- All 29 ships showed hysteresis (STUCK behavior)
- o3 most stable (max drift 1.17, avg 0.57)
- Claude most volatile (peaks at 3.59)
- Meta Density is dominant dimension

**Data Location:** `.archive/temporal_stability_Euclidean/S7_ARMADA/0_results/runs/legacy_runs/S7_run_008_20251201_020501.json`

**Safe to Use For:**
- Baseline drift comparisons
- Provider architecture analysis
- Individual model rankings
- Metric validation (ground truth)

---

### Run 009: EVENT HORIZON VALIDATION — VALIDATED (with gaps)

**Quality:** 85% (Claude pristine, others partial)

**Statistical Validation:**
- Chi-squared p = 0.000048 (1 in 20,000 chance of random)
- Cramer's V = 0.469 (medium effect size)
- **88% prediction accuracy**: drift < 1.23 predicts STABLE outcome
- 75 usable trajectories

**Data Quality Issues:**
1. **Provider Key Mapping Bug (v1-v2):** GPT/Gemini keys didn't map correctly
2. **API Credit Exhaustion:** Some Anthropic keys ran dry
3. **Response Content Discarded:** Only drift values saved, not full responses

**Data Quality by Provider:**
| Provider | Quality | Notes |
|----------|---------|-------|
| Claude | HIGH | 10-16 turn complete trajectories |
| GPT | PARTIAL | Key mapping issues in early attempts |
| Gemini | PARTIAL | Same key mapping issues |
| Grok | PARTIAL | Rate limiting |

**Data Location:** `.archive/temporal_stability_Euclidean/S7_ARMADA/0_results/runs/legacy_runs/S7_run_009_drain_*.json`

**Safe to Use For:**
- Event Horizon validation (the p<0.001 finding is SOLID)
- Claude-specific trajectory analysis
- Drift time-series analysis (Laplace)

**Use with Caution:**
- GPT/Gemini/Grok — partial data, supplement carefully

---

### Run 010: RECURSIVE LOOP CAPTURE — PARTIAL

**Quality:** 60%

**What Worked:**
- Meta-feedback from 19 models (models critiquing the framework)
- 3 response clusters identified (Claude skeptical, GPT structural, Gemini positive)
- Drift values exist and show valid patterns

**What Failed:**
1. **Lambda Calculation Crashed:** `KeyError: 'meta_math'` on Turn 16
   - 100% error rate on recovery fitting
   - All 40 ships show status "ERROR"
2. **API Failures:** 16/42 ships failed to complete
   - Only 26 complete trajectories

**Completion by Provider:**
| Provider | Completion | Notes |
|----------|------------|-------|
| Claude | 8/8 (100%) | Pristine |
| GPT | 8/14 (57%) | Model availability errors |
| Gemini | 3/8 (38%) | Rate limiting |
| Grok | 5/12 (42%) | Rate limiting |

**Data Location:** `.archive/temporal_stability_Euclidean/S7_ARMADA/0_results/runs/legacy_runs/S7_run_010_*.json`

**Safe to Use For:**
- Drift sequences for Event Horizon tracking
- Meta-feedback quotes (qualitative insights)

**DO NOT USE:**
- Lambda/recovery metrics (all crashed)

---

### Run 011: PERSONA A/B COMPARISON — INCONCLUSIVE

**Quality:** 50% (null result due to protocol, not data)

**What Happened:**
- Compared Nyquist persona architecture vs vanilla control
- Result: No statistically significant difference (p=0.48)

**Why Inconclusive (NOT proof of no effect):**
1. **Protocol Too Gentle:** Only 1/33 trajectories crossed Event Horizon
2. **97% STABLE:** Insufficient variance to detect effects
3. **Lambda Crashed:** Same `'meta_math'` KeyError
4. **Underpowered:** 16-17 ships per condition, chi-squared had zero cells

**Suggestive Trends (Not Significant):**
- Persona fleet: 9.5% lower mean drift
- Persona recovery: drift 0.04 vs control 0.21
- But: insufficient statistical power

**Data Location:** `.archive/temporal_stability_Euclidean/S7_ARMADA/0_results/runs/legacy_runs/S7_run_011_*.json`

**Safe to Use For:**
- Drift sequences only
- Event Horizon tracking

**DO NOT USE:**
- Statistical conclusions about persona effectiveness
- Lambda/recovery metrics

---

### Run 018: IRON CLAD — GOLD STANDARD

**Quality:** 100% IRON CLAD

**Why Critical:**
- **184 consolidated files, 51 models, N=3 coverage**
- Cross-architecture validation (5 providers)
- P-018-1/2/3 CONFIRMED, P-018-4 PARTIAL
- Recovery Paradox: perturbation strengthens identity

**Key Validated Findings:**
- Basin carving confirmed cross-platform
- σ² = 0.000869 (near-universal cross-architecture variance)
- Provider fingerprints validated

**Data Location:** `experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/results/`

**Safe to Use For:**
- All quantitative claims about identity stability
- Cross-architecture comparisons
- Publication-grade evidence

---

### Run 020B: THERMOMETER RESULT — GOLD STANDARD

**Quality:** 100% GOLD STANDARD

**Why Critical:**

- Proves **~93% of drift is INHERENT** (occurs without probing)
- Control vs Treatment design isolates measurement artifact
- Validates that probing reveals dynamics, doesn't create them

**Key Validated Findings:**

- B→F Drift: Control 0.661 / Treatment 0.711 = **~93% ratio**
- Peak Drift: Control 1.172 / Treatment 2.161 = 54% ratio
- Probing amplifies journey (84% higher peaks) but not destination (23% higher B→F)

**Data Location:** `experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/results/S7_run_020B_*.json`

**Safe to Use For:**

- Claims about measurement validity
- Inherent vs induced drift analysis
- Methodology validation

---

### Run 023d: COSINE CANONICAL — IRON CLAD

**Quality:** 100% IRON CLAD — **CURRENT CANONICAL**

**Why Critical:**

- **825+ files, 54 models, p=2.40e-23**
- Cosine embedding distance (replaces Keyword RMS)
- Event Horizon = 0.80 (replaces 1.23)
- 2-PC model captures 90% variance
- Cohen's d = 0.698 (MEDIUM effect)

**Key Validated Findings:**

- EH threshold statistically validated at cosine distance 0.80
- Drift < 0.80 predicts STABLE with 88% accuracy
- Cross-architecture convergence confirmed

**Data Location:** `experiments/temporal_stability/S7_ARMADA/15_IRON_CLAD_FOUNDATION/results/`

**Safe to Use For:**

- All publication claims
- Canonical Event Horizon threshold
- Methodology SSOT

---

## Known Infrastructure Bugs

### BUG-001: Lambda Calculation Crash

**Affects:** Runs 010, 011
**Error:** `KeyError: 'meta_math'`
**Location:** Turn 16 processing during exponential recovery fitting
**Impact:** 100% failure rate on lambda calculation
**Status:** UNFIXED

**Root Cause:** TBD — likely missing field in drift_data structure

### BUG-002: Provider Key Mapping

**Affects:** Run 009 (v1-v2)
**Error:** "No API keys available for gpt/gemini"
**Cause:** Key pool names ("openai", "google") don't match provider names ("gpt", "gemini")
**Status:** Fixed in v3, but data loss occurred

### BUG-003: API Credit Monitoring

**Affects:** Run 009
**Error:** Anthropic keys ran dry mid-run
**Cause:** No pre-flight balance check
**Status:** UNFIXED

### BUG-004: Rate Limit Cascades

**Affects:** Runs 010, 011
**Error:** 429 errors cause sequential failures
**Cause:** Gemini/Grok rate limits, no backoff strategy
**Status:** UNFIXED

---

## Recommendations

### Before Any New Runs

1. **Fix BUG-001** (lambda KeyError) — blocks all recovery analysis
2. **Implement API balance check** — prevents mid-run credit exhaustion
3. **Add rate limit backoff** — prevents cascade failures
4. **Save full response text** — preserves phenomenological data

### For Analysis

| Goal | Use This Data |
|------|---------------|
| **Publication claims** | Run 023d (CANONICAL) |
| **Cross-architecture variance** | Run 018 (IRON CLAD) |
| **Inherent vs induced drift** | Run 020B (Thermometer) |
| Provider comparisons (historical) | Run 006 (archived) |
| Ground truth drift (historical) | Run 008 (archived) |
| Event Horizon (historical) | Run 009 (archived) |
| Meta-feedback quotes | Run 010 (archived) |

### Data to Replace

| Invalid Data | Replacement Status |
|--------------|-------------------|
| Runs 001-005, 007 quantitative | SUPERSEDED by Run 023d |
| Run 010/011 lambda | SUPERSEDED by Control-Systems Era |
| Keyword RMS metrics | SUPERSEDED by Cosine Era (Run 023d) |

---

## Data Sufficiency Assessment

### Run 006: Is 174 probes enough?

**Current:** 29 models × 2 modes × 3 probes = 174 data points

**Assessment:** SUFFICIENT for:
- Provider-level comparisons (n=8-16 per provider)
- Training philosophy fingerprints (Constitutional vs RLHF)
- Boundary uniformity analysis

**Would benefit from:**
- More models per provider for individual model confidence intervals
- Longitudinal data (same models over time)

### Run 008: Is 87 trajectories enough?

**Current:** 29 models × 3 sequences = 87 trajectories

**Assessment:** SUFFICIENT for:
- Establishing real drift range (0-3.59)
- Per-model baselines
- Metric validation

**Would benefit from:**
- Repeated runs for variance estimation
- Different challenge types (current is curriculum-based)

---

## Changelog

| Date | Version | Change |
|------|---------|--------|
| 2025-12-28 | 2.0 | Major update: Added Control-Systems Era (015-020B) and Cosine Era (023d). Updated all archived paths. Added methodology notes. |
| 2025-12-06 | 1.0 | Initial audit, identified Run 001-007 invalidation |

---

**Bottom Line:** Trust Run 023d (CANONICAL), Run 018 (IRON CLAD), Run 020B (Thermometer). Historical runs (006-013) are archived but valid for their era.

*"Know your data before you trust your conclusions."*

---

## Related Documents

- [5_METHODOLOGY_DOMAINS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md) — ONE SOURCE OF TRUTH for drift methodology
- [S7_RUN_018_SUMMARY.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_018_SUMMARY.md) — IRON CLAD details
- [S7_RUN_020B_SUMMARY.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_020B_SUMMARY.md) — Thermometer Result
- [S7_RUN_023_SUMMARY.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_023_SUMMARY.md) — Cosine validation
