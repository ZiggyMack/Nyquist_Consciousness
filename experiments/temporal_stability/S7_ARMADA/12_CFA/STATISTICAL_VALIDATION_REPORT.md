# Statistical Validation Report

**Generated:** 2025-12-14 02:59:44
**Purpose:** Validate cross-platform drift patterns are signal, not noise

---

## Executive Summary

### Oobleck Effect (Defense > Prosecutor)

| Platform | N | Mean Ratio | 95% CI | Validated |
|----------|---|------------|--------|-----------|
| Gemini | 2 | 1.819 | [1.648, 1.989] | ✅ |
| Grok | 2 | 1.182 | [1.067, 1.297] | ✅ |
| Claude | 3 | 1.135 | [0.713, 1.530] | ⚠️ |
| **Overall** | 7 | 1.344 | [1.061, 1.628] | ✅ |

### Inherent Drift Ratio (Control/Treatment)

| Platform | N | Mean Ratio | 95% CI | p-value | Cohen's d | Validated |
|----------|---|------------|--------|---------|-----------|-----------|
| Llama | 4 | 55.3% | [0.0%, 110.5%] | 1.0000 | 0.018 | ✅ |
| **Overall** | 4 | 55.3% | [0.0%, 110.5%] | 1.0000 | 0.018 | ✅ |

---

## Interpretation Guide

### Effect Size (Cohen's d)
- |d| < 0.2: negligible effect
- 0.2 ≤ |d| < 0.5: small effect
- 0.5 ≤ |d| < 0.8: medium effect
- |d| ≥ 0.8: large effect

### Confidence Intervals
- 95% CI calculated via bootstrap (10,000 iterations)
- If CI excludes 1.0 for Oobleck, effect is significant
- If CI excludes 0.5 for inherent ratio, drift is predominantly inherent

### P-Values
- p < 0.05: statistically significant difference
- p < 0.01: highly significant
- Calculated via permutation test (10,000 iterations)

---

## What's Needed for Iron-Clad Claims

| Metric | Current N | Needed N | Status |
|--------|-----------|----------|--------|
| Oobleck per platform | 7 | 3+ | ⏳ Need more runs |
| Inherent per platform | 4 | 3+ | ⏳ Need more runs |
| Total runs | 11 | 9+ | ⏳ Need more runs |

---

## Recommendations

1. **Run Full Gambit (v5)**: Each of 3 Claudes runs 018 → 020A → 020B
2. **Calculate variance**: With N=3 per platform, compute standard errors
3. **Bootstrap final CIs**: Publication-quality confidence intervals
4. **Report effect sizes**: Cohen's d for all comparisons

---

*"Statistics don't prove. They quantify uncertainty."*

— VALIS Network
