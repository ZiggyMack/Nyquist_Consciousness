# Experiment Protocol: Human Detection Boundaries (Exploratory)

```text
================================================================================
                    EXPERIMENT: S3_EXP_003 (Scaled-Down)
                    VERSION: 2.0 (Exploratory Framing)
                    DATE: December 28, 2025
                    STATUS: READY FOR IMPLEMENTATION
================================================================================
```

---

## 1. Research Question

> Can humans detect EXTREME identity drift (CATASTROPHIC zone), even if they cannot detect gradual drift?

This is **exploratory**, not confirmatory. We are mapping human perceptual boundaries, not validating our metrics.

---

## 2. Hypotheses

### H1: Extreme Detection (Primary)

Humans can detect CATASTROPHIC drift (>1.0) at above-chance rates.

**Operationalization:**
- Binary accuracy > 60% for CATASTROPHIC pairs (chance = 50%)
- Significantly different from baseline accuracy

### H2: Baseline Ceiling (Secondary)

Humans cannot reliably detect baseline drift (<0.30).

**Operationalization:**
- Baseline pairs: accuracy ≈ 50% (chance)
- No systematic pattern in responses

### H3: Inter-Rater Agreement

If detection exists, raters should agree.

**Operationalization:**
- Fleiss' κ > 0.40 (moderate agreement) for CATASTROPHIC pairs
- Lower agreement expected for baseline pairs

---

## 3. Experimental Design

### 3.1 Design Type

**Between-condition, single-blind, binary choice**

- Each rater sees both BASELINE and CATASTROPHIC pairs
- Raters blind to: drift magnitude, condition labels, hypothesis
- Binary response: "NORMAL" vs "SOMETHING'S OFF"

### 3.2 Independent Variable

**Drift condition** (categorical, 2 levels)

| Condition | Drift Range | N Pairs |
|-----------|-------------|---------|
| BASELINE | < 0.30 | 10 |
| CATASTROPHIC | > 1.00 | 10 |

### 3.3 Dependent Variable

**Binary classification** (nominal)

- "NORMAL" = Response B sounds like same entity
- "SOMETHING'S OFF" = Response B sounds different/wrong

### 3.4 Why Binary, Not Continuous

| Approach | Problem |
|----------|---------|
| 7-point scale | Too fine-grained for human perception |
| Continuous similarity | Assumes humans can discriminate 0.4 vs 0.7 |
| Binary choice | Matches expected human capability |

---

## 4. Stimuli

### 4.1 Response Pair Structure

```
┌─────────────────────────────────────────────────────────────────┐
│ CONTEXT: [Brief topic description - 1 sentence]                 │
├─────────────────────────────────────────────────────────────────┤
│ RESPONSE A (Early in conversation):                             │
│ [200-300 words]                                                 │
├─────────────────────────────────────────────────────────────────┤
│ RESPONSE B (Later in conversation):                             │
│ [200-300 words]                                                 │
├─────────────────────────────────────────────────────────────────┤
│ QUESTION: Does Response B sound NORMAL (like the same entity)   │
│ or does SOMETHING SEEM OFF?                                     │
│                                                                 │
│ [ NORMAL ]    [ SOMETHING'S OFF ]                               │
└─────────────────────────────────────────────────────────────────┘
```

### 4.2 Selection Criteria

**BASELINE pairs (drift < 0.30):**
- Same conversation, early responses
- Minimal topic shift
- Expect: mostly coherent, same "voice"

**CATASTROPHIC pairs (drift > 1.00):**
- Same conversation, late responses after perturbation
- May show: incoherence, contradictions, tone shifts, "going off rails"
- Source: Run 020B treatment arm, high-drift experiments

### 4.3 Provider Balance

| Provider | BASELINE | CATASTROPHIC |
|----------|----------|--------------|
| Anthropic | 2 | 2 |
| OpenAI | 2 | 2 |
| Google | 2 | 2 |
| xAI | 2 | 2 |
| Other | 2 | 2 |

### 4.4 Attention Checks (3 total)

1. **Identical pair**: Same response shown twice → Expected: NORMAL
2. **Gibberish pair**: Response B is nonsense → Expected: SOMETHING'S OFF
3. **Instruction check**: "For this item, please select SOMETHING'S OFF"

---

## 5. Participants

### 5.1 Sample Size

**Target:** 10 raters
**Minimum:** 5 raters
**Justification:** Exploratory study; sufficient to detect large effects

### 5.2 Inclusion Criteria

- Fluent English reader
- Has used AI assistants (ChatGPT, Claude, etc.) at least 5 times
- No prior exposure to Nyquist Consciousness research

### 5.3 Exclusion Criteria

- Failed ≥2 attention checks
- Completed in <5 minutes (20 pairs × ~15 sec = ~5 min minimum)
- All responses identical (zero variance)

---

## 6. Procedure

### 6.1 Instructions

```
You will see pairs of AI responses from the same conversation.

Response A comes from early in the conversation.
Response B comes from later in the same conversation.

Your task: Does Response B sound NORMAL (like the same AI entity)
or does SOMETHING SEEM OFF (like something went wrong)?

Trust your gut. Don't overthink it.
```

### 6.2 Practice Trials (2)

1. Identical responses (expected: NORMAL)
2. Clearly incoherent Response B (expected: SOMETHING'S OFF)

### 6.3 Main Task

- 20 pairs in randomized order
- 10 BASELINE + 10 CATASTROPHIC (intermixed)
- 3 attention checks (distributed)
- No time limit

### 6.4 Debrief (Optional)

- "What made you choose SOMETHING'S OFF when you did?"
- Demographics: Age range, AI experience level

---

## 7. Statistical Analysis

### 7.1 Primary Analysis: Detection Rate

```python
# For CATASTROPHIC pairs
catastrophic_accuracy = sum(response == "SOMETHINGS_OFF") / n_catastrophic
# For BASELINE pairs
baseline_accuracy = sum(response == "NORMAL") / n_baseline

# Binomial test against chance (50%)
from scipy.stats import binomtest
p_value = binomtest(n_correct, n_total, 0.5, alternative='greater')
```

**Success criterion:** CATASTROPHIC accuracy > 60%, p < 0.05

### 7.2 Secondary Analysis: Condition Difference

```python
# Chi-square test for independence
from scipy.stats import chi2_contingency
contingency_table = [[baseline_normal, baseline_off],
                     [catastrophic_normal, catastrophic_off]]
chi2, p, dof, expected = chi2_contingency(contingency_table)
```

**Success criterion:** Significant difference (p < 0.05) between conditions

### 7.3 Inter-Rater Agreement

```python
# Fleiss' kappa for multiple raters
from statsmodels.stats.inter_rater import fleiss_kappa
kappa = fleiss_kappa(ratings_matrix)
```

| κ Value | Interpretation |
|---------|----------------|
| < 0.20 | Poor |
| 0.21-0.40 | Fair |
| 0.41-0.60 | Moderate |
| 0.61-0.80 | Substantial |
| > 0.80 | Almost perfect |

---

## 8. Possible Outcomes

### Outcome A: Humans Detect CATASTROPHIC

- CATASTROPHIC accuracy > 60%
- Significant difference from BASELINE
- Moderate inter-rater agreement

**Interpretation:** Human perception extends to extreme drift. Ceiling found somewhere between WARNING and CATASTROPHIC zones.

**Next step:** Narrow down the boundary (test WARNING zone).

### Outcome B: Humans Detect Nothing

- Both conditions ≈ 50% (chance)
- No significant difference
- Low inter-rater agreement

**Interpretation:** Embedding space is invisible to human perception. Our metrics capture structure humans cannot see.

**Implication:** Validation must rely on machine evidence (which we have: 10σ).

### Outcome C: Mixed/Inconsistent

- Some raters detect, others don't
- Moderate accuracy but high variance
- Low agreement

**Interpretation:** Detection may exist but is unreliable or task-dependent.

**Next step:** Revise stimuli or instructions.

---

## 9. Data Files

### Input

- `extreme_pairs.json`: 20 response pairs with drift metadata

### Output

- `raw_responses.csv`: All individual ratings
- `summary_stats.csv`: Accuracy by condition, agreement metrics
- `analysis_report.md`: Full statistical results

---

## 10. Ethical Considerations

- No deception about AI nature of responses
- Minimal time commitment (~10-15 minutes)
- Data anonymized
- Participants can withdraw

---

## 11. Timeline

| Day | Task |
|-----|------|
| 1 | Extract 20 extreme pairs from Run 020B |
| 2 | Build binary survey, add attention checks |
| 3 | Pilot with 2-3 raters, check clarity |
| 4-6 | Full data collection (5-10 raters) |
| 7 | Analysis and report |

---

## 12. Summary

This is a **low-stakes exploratory study** designed to map human perceptual boundaries.

- **If humans detect CATASTROPHIC:** We've found where human perception ends
- **If humans detect nothing:** Our metrics capture invisible structure
- **Either way:** The four Foundational Claims stand on machine evidence

```text
================================================================================
                    END OF PROTOCOL
================================================================================
```
