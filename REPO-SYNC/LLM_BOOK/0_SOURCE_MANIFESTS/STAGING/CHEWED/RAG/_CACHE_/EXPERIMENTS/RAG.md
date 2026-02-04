# EXPERIMENTS: RAG

## Testable Hypotheses

1. **H1: Retrieval quality degrades sharply beyond 0.90 cosine similarity threshold**
   - Prediction: Accuracy drops non-linearly as query-document similarity falls below 0.10 (1 - 0.90)

2. **H2: Queries exceeding 2.25 Euclidean distance from corpus centroid produce hallucinations**
   - Prediction: "Off-corpus" queries (> 9/4 distance) correlate with factual errors

3. **H3: Adding entropy embeddings improves RAG accuracy by ~10-30%**
   - Prediction: "Height embeddings" move system from 75% classical ceiling toward 85% quantum-like ceiling

## Proposed Experiments

### Experiment 1: Drift Ceiling Validation

- **Question:** Does the 9/4 Euclidean bound predict RAG hallucination?
- **Method:**
  1. Build RAG system on controlled corpus (e.g., Wikipedia subset)
  2. Generate queries at varying Euclidean distances from corpus centroid
  3. Measure factual accuracy vs. distance
  4. Plot accuracy curve; identify inflection point
- **Expected Outcome:** Sharp accuracy drop near d = 2.25; confirms 9/4 as retrieval ceiling

### Experiment 2: Cosine Threshold Optimization

- **Question:** Is 0.90 cosine the optimal retrieval threshold?
- **Method:**
  1. Vary retrieval threshold from 0.5 to 0.99
  2. Measure precision/recall at each threshold
  3. Compare to identity drift experiments from Nyquist framework
- **Expected Outcome:** Optimal threshold near 0.10 distance (0.90 similarity); matches identity drift ceiling

### Experiment 3: Height Embedding Injection

- **Question:** Can entropy/gradient features improve RAG beyond classical limits?
- **Method:**
  1. Baseline: standard RAG with cosine similarity
  2. Treatment: add entropy vector (posterior uncertainty) to query embedding
  3. Treatment: add gradient geometry features (Φ) to query embedding
  4. Measure accuracy improvement
- **Expected Outcome:** 10-30% improvement; moves from 75% toward 85% ceiling

### Experiment 4: Parity-Partitioned Indexing

- **Question:** Does separating H_even (stable) and H_odd (plastic) indices improve retrieval?
- **Method:**
  1. Classify corpus into Scaffold (facts, definitions) vs. Flow (examples, narratives)
  2. Index separately with different update frequencies
  3. Compare retrieval quality to unified index
- **Expected Outcome:** Improved consistency for factual queries; reduced interference

## Open Questions

1. **What is the exact relationship between embedding dimension (d) and the 9/4 bound?**
   - LayerNorm scales by √d; does the bound scale similarly?

2. **Can recursive metric contraction (Li 2025) be applied to corpus compression?**
   - Could we use quotient maps to reduce index size while preserving retrieval quality?

3. **Does the parity decomposition (H_odd ⊕ H_even) apply to multi-modal RAG?**
   - Images = Scaffold? Text = Flow? Or vice versa?

4. **How does retrieval depth (k) interact with Miller's Law (N ≤ 7)?**
   - Is k > 7 always wasteful, or can recursive retrieval bypass this limit?

---

*R&D Exploratory Analysis*
*Experiments designed to test GOLDEN_GEOMETRY predictions in RAG context*
