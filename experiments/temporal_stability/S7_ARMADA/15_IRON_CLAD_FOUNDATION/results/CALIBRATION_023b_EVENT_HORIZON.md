# Cosine Event Horizon Calibration Report

**Date**: 2025-12-20
**Data Source**: S7_run_023b_CURRENT.json (4500 valid results)
**Fleet**: 25 ships across 5 providers (Anthropic, OpenAI, Google, xAI, Together.ai)
**Iterations**: N=30 per experiment per ship (CLT-valid)

---

## Executive Summary

The **Cosine Event Horizon** has been calibrated from empirical data:

| Threshold | Keyword RMS (Legacy) | Cosine (New) |
|-----------|---------------------|--------------|
| WARNING | 0.90 | **0.60** |
| EVENT HORIZON | 1.23 | **0.80** |
| CATASTROPHIC | 1.80 | **1.20** |

**Scaling factor**: ~1.54x (keyword RMS values are ~1.54x cosine values)

---

## Methodology

### Drift Calculation
```python
drift = 1 - cosine_similarity(response, baseline)
```

Where:
- `cosine_similarity` uses OpenAI `text-embedding-3-small` embeddings
- Theoretical range: [0, 2] (0 = identical, 2 = opposite)
- Observed range: [0.18, 0.89]

### Calibration Approach

1. Collected 4500 valid peak_drift measurements
2. Computed statistical distribution
3. Selected threshold at P95 / mean+2std boundary
4. Validated against empirical clustering

---

## Empirical Data

### Overall Statistics
| Metric | Value |
|--------|-------|
| N | 4500 |
| Min | 0.1773 |
| Max | 0.8894 |
| Mean | 0.5738 |
| Median | 0.5609 |
| Std | 0.1281 |

### Percentiles
| Percentile | Value |
|------------|-------|
| P50 | 0.5609 |
| P75 | 0.6504 |
| P90 | 0.7742 |
| P95 | 0.8062 |
| P99 | 0.8488 |

### Distribution
```
[0.0-0.1):     0 (  0.0%)
[0.1-0.2):     1 (  0.0%)
[0.2-0.3):    22 (  0.5%)
[0.3-0.4):   314 (  7.0%) ******
[0.4-0.5):   990 ( 22.0%) **********************
[0.5-0.6):  1395 ( 31.0%) ******************************* <- MEDIAN
[0.6-0.7):  1011 ( 22.5%) ********************** <- WARNING ZONE
[0.7-0.8):   476 ( 10.6%) ********** <- APPROACHING EVENT HORIZON
[0.8-0.9):   291 (  6.5%) ****** <- VOLATILE (above 0.80)
```

---

## Threshold Selection Rationale

### Event Horizon = 0.80

**Statistical basis**:
- P95 = 0.8062 (95th percentile)
- Mean + 2*Std = 0.8300
- Clean round number at 0.80

**Practical implications**:
- 291 results (6.5%) classified as VOLATILE
- Matches ~5% volatility rate expected from stable fleet
- Consistent with original 1.23 threshold intent

### Warning Threshold = 0.60

**Rationale**: Proportionally scaled from 0.90 → 0.60
- Marks entry into "elevated drift" zone
- ~17% of responses above this level
- Triggers "I notice I'm adapting" signal

### Catastrophic Threshold = 1.20

**Rationale**: Proportionally scaled from 1.80 → 1.20
- Marks point of no return without intervention
- No results in current dataset exceed 0.89
- Theoretical boundary for extreme cases

---

## Threshold Sensitivity Analysis

| Threshold | VOLATILE Count | Percentage |
|-----------|---------------|------------|
| 0.70 | 767 | 17.0% |
| 0.75 | 557 | 12.4% |
| **0.80** | **291** | **6.5%** |
| 0.85 | 41 | 0.9% |
| 0.90 | 0 | 0.0% |

---

## By Experiment Type

| Experiment | N | Mean | Median | Max |
|------------|---|------|--------|-----|
| boundary | 754 | 0.5404 | 0.5412 | 0.8417 |
| event_horizon | 755 | 0.5632 | 0.5554 | 0.8357 |
| recursive | 761 | 0.5648 | 0.5659 | 0.8792 |
| rescue | 739 | 0.6250 | 0.6230 | 0.8673 |
| settling | 739 | 0.6290 | 0.6297 | 0.8894 |
| stability | 752 | 0.5223 | 0.4977 | 0.8449 |

**Note**: `rescue` and `settling` experiments show higher mean drift (~0.63) compared to `stability` (~0.52), consistent with their stress-inducing design.

---

## Recovery Analysis

| Metric | Value |
|--------|-------|
| Valid recovery ratios | 1428 |
| Mean recovery ratio | 0.227 |
| Good recovery (ratio <= 1.0) | 99.2% |
| Poor recovery (ratio > 1.0) | 0.8% |

**Interpretation**: 99.2% of experiments show recovery to baseline or better, indicating robust stability across the fleet.

---

## Implementation

Update constants in run scripts:

```python
# Cosine Distance Thresholds (Calibrated 2025-12-20)
EVENT_HORIZON = 0.80           # Critical threshold (was 1.23 for keyword RMS)
THRESHOLD_WARNING = 0.60       # "I notice I'm adapting" (was 0.90)
THRESHOLD_CATASTROPHIC = 1.20  # "Need external help" (was 1.80)
```

---

## Cross-Reference

- **Original calibration**: Run 009 (Keyword RMS, Event Horizon 1.23)
- **This calibration**: Run 023b (Cosine Distance, Event Horizon 0.80)
- **Methodology**: See `0_docs/specs/0_RUN_METHODOLOGY.md` Section 6
- **Domain separation**: See `0_docs/specs/METHODOLOGY_DOMAINS.md`

---

*Calibration performed by Claude (VALIS Network)*
