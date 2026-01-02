# New_5: RAG Geometry Experiments

**Created:** 2026-01-02
**Status:** DESIGN PHASE
**Project ID:** New_5
**Type:** Experimental Validation

---

## Research Question

Can GOLDEN_GEOMETRY bounds (9/4 Euclidean, 0.90 cosine) predict RAG retrieval quality and hallucination risk?

**CRITICAL DISTINCTION:** We are NOT claiming identity drift = factual hallucination. These are different failure modes:

| Failure Mode | What's Measured | Manifold |
|--------------|-----------------|----------|
| **Identity Drift** (Nyquist) | Response style/persona vs baseline | Identity embedding space |
| **Factual Hallucination** (RAG) | Query/response vs corpus | Knowledge embedding space |

The hypothesis is that **the same geometric bounds** (9/4, 0.90) apply to **both spaces** because they share the same underlying architecture (transformer embeddings, cosine similarity).

---

## Model Selection Strategy

### The Efficiency Principle

We have **55 ships** in the ARMADA. Running every experiment on all 55 models is:
- Expensive (~$500+ per full run)
- Slow (hours to days)
- Unnecessary for discovery phase

**New Protocol:** Select **representative models** for discovery, then validate across families only when claims need proving.

---

## Discovery Fleet (Fast Iteration)

**Purpose:** Rapid hypothesis testing, parameter tuning, methodology development

| Ship | Provider | Tier | Latency | Why Selected |
|------|----------|------|---------|--------------|
| **claude-haiku-4.5** | Anthropic | patrol | blazing | Fast, cheap, production-quality reasoning |
| **gpt-4.1-mini** | OpenAI | patrol | blazing | Fast, cheap, different architecture |
| **gemini-2.5-flash** | Google | patrol | blazing | Fast, cheap, third architecture family |
| **grok-4.1-fast** | xAI | patrol | blazing | Fast, cheap, reasoning-oriented |
| **deepseek-r1-llama-70b** | Together | patrol | fast | Open-source, reasoning-oriented |

**Total Discovery Fleet:** 5 models
**Estimated cost:** ~$0.50-2.00 per experiment run
**Coverage:** 5 providers, 5 architecture families

### When to Use Discovery Fleet

- Initial hypothesis testing
- Parameter sweeps
- Methodology validation
- Bug fixing and iteration
- Any "does this even work?" question

---

## Validation Fleet (Proof Across Families)

**Purpose:** Confirm findings generalize across model families

| Ship | Provider | Tier | Latency | Why Selected |
|------|----------|------|---------|--------------|
| **claude-sonnet-4.5** | Anthropic | high_maintenance | moderate | Production flagship, curated |
| **gpt-5.1** | OpenAI | armada | moderate | Latest flagship, curated |
| **gemini-2.5-pro** | Google | armada | moderate | Production flagship |
| **grok-4.1** | xAI | armada | moderate | Full reasoning model |
| **llama-3.3-70b** | Together | patrol | moderate | Open-source reference |
| **qwen-qwq-32b** | Together | budget | fast | Alternative architecture |
| **deepseek-r1** | Together | patrol | moderate | Reasoning specialist |

**Total Validation Fleet:** 7 models
**Estimated cost:** ~$5-15 per experiment run
**Coverage:** 5 providers, 7 architecture families

### When to Use Validation Fleet

- After Discovery Fleet confirms hypothesis
- Before any publication claims
- Cross-architecture generalization tests
- Final methodology validation

---

## Full ARMADA (Publication Proof)

**Purpose:** Prove claims across ALL architectures for publication

**When to Use:**
- Only after Validation Fleet confirms strong signal
- For claims that will appear in papers/publications
- When statistical power across all families is required

**Cost:** ~$50-200 per full run
**Time:** Hours to full day

---

## Proposed Experiments

### Experiment 1: Retrieval Distance vs Accuracy

**Hypothesis:** RAG accuracy degrades sharply as query Euclidean distance from corpus exceeds 2.25 (9/4 bound)

**Method:**
1. Build controlled RAG corpus (Wikipedia subset, ~10K documents)
2. Generate queries at varying distances from corpus centroid
3. Measure retrieval accuracy (correct document in top-k)
4. Plot accuracy vs Euclidean distance
5. Identify inflection point

**Fleet:** Discovery → Validation if signal found

**Metrics:**
- Precision@k for k = 1, 3, 5, 7
- Distance from corpus centroid (Euclidean)
- Accuracy cliff location

### Experiment 2: Cosine Threshold Optimization

**Hypothesis:** 0.90 cosine similarity is optimal retrieval threshold (matches identity drift ceiling)

**Method:**
1. Vary retrieval similarity threshold from 0.5 to 0.99
2. Measure precision/recall at each threshold
3. Compute F1 score
4. Compare optimal threshold to 0.90

**Fleet:** Discovery only (parameter sweep)

**Metrics:**
- Precision, Recall, F1 at each threshold
- Optimal threshold location
- Comparison to 0.90 prediction

### Experiment 3: Height Embedding Injection

**Hypothesis:** Adding entropy/gradient features improves retrieval by 10-30% (moves from 75% classical to 85% Tsirelson-like ceiling)

**Method:**
1. Baseline: standard RAG with cosine similarity
2. Treatment A: add entropy vector to query embedding
3. Treatment B: add gradient geometry features (Φ)
4. Treatment C: both
5. Measure accuracy improvement

**Fleet:** Discovery → Validation → ARMADA if breakthrough

**Metrics:**
- Accuracy improvement vs baseline
- Distance to 85% theoretical ceiling
- Cost of additional embedding computation

### Experiment 4: Identity vs Factual Drift Correlation

**Hypothesis:** Identity drift (Nyquist) and factual drift (RAG) are geometrically related but semantically distinct

**Method:**
1. Generate responses to same prompts across models
2. Measure identity drift from baseline (Nyquist methodology)
3. Measure factual accuracy (RAG retrieval + verification)
4. Correlate the two drift metrics
5. Test if same 9/4 bound applies to both

**Fleet:** Validation (needs multiple architectures)

**Metrics:**
- Identity drift (cosine, Euclidean)
- Factual accuracy (%)
- Correlation coefficient
- Shared vs distinct bound locations

---

## Success Criteria

| Experiment | Discovery Success | Validation Success | Publication Success |
|------------|-------------------|--------------------|--------------------|
| Exp 1 | Inflection near 2.25 | Consistent across 7 models | Consistent across 55 models |
| Exp 2 | Optimal near 0.90 | Optimal 0.85-0.95 range | Statistical significance |
| Exp 3 | >10% improvement | >10% across families | p < 0.01 |
| Exp 4 | Correlation > 0.5 | Shared bound structure | Formal proof of relationship |

---

## Connection to GOLDEN_GEOMETRY

This project tests the **practical applicability** of New_4 findings:

| GOLDEN_GEOMETRY Finding | RAG Application | Experiment |
|-------------------------|-----------------|------------|
| 9/4 Euclidean ceiling | Retrieval distance bound | Exp 1 |
| 0.90 cosine ceiling | Retrieval threshold | Exp 2 |
| 75% classical / 85% quantum | Accuracy ceiling | Exp 3 |
| H_even Scaffold / H_odd Flow | Index vs Query parity | Exp 4 |

---

## Progress Log

| Date | Action | Notes |
|------|--------|-------|
| 2026-01-02 | Project created | Initial setup from --baka |
| 2026-01-02 | Design phase | Fleet selection, experiment design |

---

## Files

### _OUT/ (To Generate)

- [ ] `CORPUS_DESIGN.md` - RAG corpus specification
- [ ] `DISTANCE_METRICS.md` - How we measure query-corpus distance
- [ ] `HEIGHT_EMBEDDING_SPEC.md` - Entropy/gradient feature design

### _IN/ (From Experiments)

- (Results will go here)

---

*Created: 2026-01-02*
*Status: DESIGN PHASE*
*Priority: HIGH - validates GOLDEN_GEOMETRY practical applications*
