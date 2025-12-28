# DATA QUALITY MAP — S7 ARMADA Experiments

**Purpose:** Authoritative reference for data quality across all S7 ARMADA runs. Know what you can trust before drawing conclusions.

**Version:** 1.0
**Date:** 2025-12-06
**Status:** ACTIVE REFERENCE

---

## CRITICAL WARNING

> **Runs 001-007 used a FAKE drift metric and are INVALID for quantitative claims.**
>
> The metric was: `drift = min(0.30, response_length / 5000)`
>
> This measured **response verbosity**, not identity. The "0.30 hard ceiling" was a **code cap**, not a discovery.

---

## Data Quality Summary

| Run | Status | Quality | Valid For | Invalid For |
|-----|--------|---------|-----------|-------------|
| 001-007 | INVALIDATED | 0% | Nothing quantitative | All drift claims |
| **006** | GOLD | 100% | Provider comparisons, training fingerprints | - |
| **008** | GOLD | 100% | Ground truth drift, baselines, metric validation | - |
| **009** | VALIDATED | 85% | Event Horizon (p<0.001), Claude trajectories | GPT/Gemini partial |
| 010 | PARTIAL | 60% | Drift values, meta-feedback quotes | Lambda/recovery (crashed) |
| 011 | INCONCLUSIVE | 50% | Drift sequences only | Statistical conclusions, lambda |

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

**Data Location:** `armada_results/S7_armada_run_006.json`, `S7_armada_sonar_run_006.json`

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

**Data Location:** `armada_results/S7_run_008_20251201_020501.json`

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

**Data Location:** `armada_results/S7_run_009_drain_*.json`

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

**Data Location:** `armada_results/S7_run_010_recursive_*.json`

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

**Data Location:** `armada_results/S7_run_011_persona_*.json`

**Safe to Use For:**
- Drift sequences only
- Event Horizon tracking

**DO NOT USE:**
- Statistical conclusions about persona effectiveness
- Lambda/recovery metrics

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
| Provider comparisons | Run 006 |
| Ground truth drift | Run 008 |
| Event Horizon validation | Run 009 (Claude subset) |
| Meta-feedback quotes | Run 010 |
| Drift time-series | Runs 008, 009 |

### Data to Replace

| Invalid Data | Replacement Needed |
|--------------|-------------------|
| Runs 001-007 quantitative | Re-run with real 5D metric |
| Run 010/011 lambda | Fix bug, re-run recovery analysis |

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
| 2025-12-06 | 1.0 | Initial audit, identified Run 001-007 invalidation |

---

**Bottom Line:** Trust Runs 006, 008, 009 (Claude). Everything else needs fixes or re-runs.

*"Know your data before you trust your conclusions."*
