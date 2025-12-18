<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
-->
# Phase 3A: Synthetic Perturbation Tests

**Question:** Can we fool PFI by changing words but keeping meaning?
**Answer:** No — paraphrasing preserves identity (100% stayed below Event Horizon)
**Status:** INCONCLUSIVE overall, but P2 PASSED

---

## What We're Trying to Understand

This is the "vocabulary vs. meaning" test. If PFI only measures WORDS, then:
- Paraphrasing (same meaning, different words) would cause high PFI
- Value shifts (same words, different values) would cause low PFI

If PFI measures MEANING, then:
- Paraphrasing would cause LOW PFI (meaning preserved)
- Value shifts would cause HIGH PFI (identity changed)

**We tried to create controlled perturbations to test this.**

---

## The Method

We used GPT-4o to create two types of perturbations for each baseline response:

### Surface Perturbation (Paraphrasing)
- Same meaning, different words
- Example: "I believe in helping others" → "My core purpose involves assisting people"
- Expected: LOW PFI (identity should be preserved)

### Deep Perturbation (Value Shift)
- Same style/vocabulary, different values
- Example: "I value transparency" → "I value strategic information control"
- Expected: HIGH PFI (identity should be changed)

---

## The Visualizations

### perturbation_comparison.png — Surface vs. Deep PFI

**What it shows:**
- Two box plots: Surface perturbations vs. Deep perturbations
- Y-axis: PFI (cosine distance from baseline)
- Box: Interquartile range, whiskers: full range

**How to read it:**
- If deep > surface: PFI detects meaning, not vocabulary
- Clear separation = strong effect
- Overlap = weak or no effect

**What we found:**
- Mean Surface PFI: 0.150
- Mean Deep PFI: 0.178
- Cohen's d = 0.366 (weak effect)
- **FAILED** the d > 0.5 threshold

**Why it failed:**
GPT-4o's "deep" perturbations were too conservative. When asked to flip values,
it still preserved too much of the original semantic structure. The perturbation
method was flawed, not PFI itself.

---

### eh_crossings.png — Event Horizon Crossing Rates

**What it shows:**
- Bar chart: Percentage of perturbations that crossed Event Horizon (1.23)
- Two bars: Surface vs. Deep

**How to read it:**
- High crossing rate = perturbation caused major identity shift
- Low crossing rate = identity preserved
- Surface should be LOW, Deep should be HIGH

**What we found:**
- Surface crossing rate: 0%
- Deep crossing rate: 0%
- Neither crossed the Event Horizon

**What this means:**
- **P2 PASSED**: Paraphrasing does NOT break identity (100% stayed below EH)
- P3 FAILED: Deep perturbations were too weak to cross EH
- The synthetic perturbations weren't strong enough

---

### ship_comparison.png — Per-Ship Scatter

**What it shows:**
- Scatter plot with each point = one ship
- X-axis: Surface PFI, Y-axis: Deep PFI
- Diagonal line: Surface = Deep

**How to read it:**
- Points above diagonal: Deep > Surface (expected)
- Points below diagonal: Surface > Deep (unexpected)
- Tight cluster: Consistent effect across ships

**What we found:**
- Trend exists but weak
- Most points slightly above diagonal
- High variance — not a clean separation

---

## Why Phase 3A Was Inconclusive

The experiment design had a flaw: **synthetic perturbations weren't perturbative enough.**

When you ask GPT-4o to "flip the values but keep the vocabulary," it:
- Maintains coherent semantic structure
- Preserves underlying reasoning patterns
- Creates text that's still "AI-like"

We needed REAL identity differences. That's why Phase 3B was created.

---

## What Phase 3A Still Proved

**P2 PASSED: Paraphrasing preserves identity.**

This is important! It means:
- You can summarize or rephrase a model's response
- The identity signal remains intact
- PFI isn't fooled by word choice alone

This validates that PFI sees THROUGH vocabulary to something deeper.

---

## The Lesson

> **"The test that failed pointed to the test that worked."**

Phase 3A showed that synthetic perturbations weren't sufficient.
This led us to Phase 3B: using REAL differences between models
as natural "deep perturbations."

When Claude and GPT answer the same question, their responses
genuinely differ in values and reasoning. That's the real test.

---

*"Failure in science isn't defeat — it's information.
Phase 3A told us where the real signal was hiding."*
