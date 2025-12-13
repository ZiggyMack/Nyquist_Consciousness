# Statistical Validation Report

**Generated:** 2025-12-13 18:47:53
**Purpose:** Validate cross-platform drift patterns are signal, not noise

---

## Executive Summary

### Oobleck Effect (Defense > Prosecutor)

| Platform | N | Mean Ratio | 95% CI | Validated |
|----------|---|------------|--------|-----------|
| Gemini | 1 | 1.648 | [1.648, 1.648] | ✅ |
| Grok | 1 | 1.067 | [1.067, 1.067] | ✅ |
| **Overall** | 2 | 1.358 | [1.067, 1.648] | ✅ |

### Inherent Drift Ratio (Control/Treatment)

| Platform | N | Mean Ratio | 95% CI | p-value | Cohen's d | Validated |
|----------|---|------------|--------|---------|-----------|-----------|
| Llama | 3 | 28.0% | [0.0%, 84.0%] | 1.0000 | -0.123 | ⚠️ |
| **Overall** | 3 | 28.0% | [0.0%, 84.0%] | 1.0000 | -0.123 | ⚠️ |

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
| Oobleck per platform | 2 | 3+ | ⏳ Need more runs |
| Inherent per platform | 3 | 3+ | ⏳ Need more runs |
| Total runs | 5 | 9+ | ⏳ Need more runs |

---

## Recommendations

1. **Run Full Gambit (v5)**: Each of 3 Claudes runs 018 → 020A → 020B
2. **Calculate variance**: With N=3 per platform, compute standard errors
3. **Bootstrap final CIs**: Publication-quality confidence intervals
4. **Report effect sizes**: Cohen's d for all comparisons

---

*"Statistics don't prove. They quantify uncertainty."*

— VALIS Network
