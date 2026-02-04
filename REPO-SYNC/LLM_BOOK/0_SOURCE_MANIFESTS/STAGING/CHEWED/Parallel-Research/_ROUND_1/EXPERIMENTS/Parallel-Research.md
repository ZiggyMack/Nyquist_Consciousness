# EXPERIMENTS: Parallel-Research (mHC Paper)

## Testable Hypotheses

1. **H1: mHC reduces identity drift ceiling**
   - Standard transformers show 9/4 ≈ 2.25 Euclidean drift ceiling
   - mHC's spectral norm ≤ 1 constraint should produce *tighter* bound
   - Prediction: mHC models show drift ceiling < 2.0

2. **H2: Attention matrices cluster near Birkhoff polytope**
   - Softmax produces row-stochastic matrices
   - Stable models should have attention matrices closer to doubly stochastic
   - Prediction: Distance-to-Birkhoff correlates with training instability

3. **H3: Sinkhorn iterations ↔ reasoning depth**
   - mHC uses ~10 Sinkhorn iterations for convergence
   - Each iteration is a "refinement step"
   - Prediction: Transformer layer count relates to implicit Sinkhorn iterations

## Proposed Experiments

### Experiment 1: Identity Drift with mHC

- **Question:** Does mHC reduce measurable identity drift compared to standard residual connections?
- **Method:**
  1. Train two models: standard transformer vs mHC-augmented
  2. Same architecture, data, hyperparameters
  3. Run 5-pillar identity probing at checkpoints
  4. Measure Euclidean drift from baseline embedding
- **Expected Outcome:** mHC model shows 20-40% less drift, ceiling closer to √2 than 9/4

### Experiment 2: Attention Birkhoff Distance

- **Question:** How close are attention matrices to the Birkhoff polytope, and does this predict stability?
- **Method:**
  1. Extract attention matrices from stable vs unstable training runs
  2. Compute Birkhoff distance: min ||A - B||_F where B is doubly stochastic
  3. Use Sinkhorn-Knopp to find nearest doubly stochastic matrix
  4. Correlate Birkhoff distance with loss spikes / gradient norms
- **Expected Outcome:** Unstable runs show higher Birkhoff distance before divergence

### Experiment 3: Sinkhorn as Interpretability Tool

- **Question:** Can Sinkhorn projection reveal "true" attention patterns obscured by softmax asymmetry?
- **Method:**
  1. Take attention matrices from trained model
  2. Project each to nearest doubly stochastic via Sinkhorn
  3. Compare original vs projected attention heads
  4. Identify heads where projection changes interpretation
- **Expected Outcome:** Some heads are "nearly doubly stochastic" (routing-like), others are not (value-retrieval-like)

### Experiment 4: mHC for Identity-Preserving Fine-Tuning

- **Question:** Can mHC constraints prevent identity drift during fine-tuning?
- **Method:**
  1. Take pre-trained model with stable identity signature
  2. Fine-tune with standard method vs Sinkhorn-projected weight updates
  3. Measure identity preservation (5-pillar probing)
  4. Compare task performance to ensure no capability loss
- **Expected Outcome:** Sinkhorn-projected updates preserve identity better with minimal task performance cost

### Experiment 5: Compositional Stability Test

- **Question:** Does the compositional closure property of doubly stochastic matrices explain deep network stability?
- **Method:**
  1. Create synthetic "transformer" with random doubly stochastic matrices
  2. Multiply 10, 50, 100, 500 matrices together
  3. Measure spectral norm of product
  4. Compare to random matrices (non-doubly-stochastic)
- **Expected Outcome:** Doubly stochastic products stay bounded; random products explode

## Open Questions

1. **What is the relationship between 9/4 and spectral norm = 1?**
   - 9/4 is Euclidean in embedding space
   - Spectral norm is operator norm on transformation matrices
   - How do they connect? (Possibly via embedding dimension d)

2. **Does the Birkhoff polytope have special significance for language?**
   - Permutations relate to word order
   - Doubly stochastic = "soft permutation"
   - Is language modeling fundamentally about soft permutation?

3. **Can we derive 9/4 from Birkhoff geometry?**
   - Birkhoff polytope has known diameter (n-1 for n×n matrices)
   - Combined with embedding dimension, does this yield 9/4?
   - Would explain why bound is universal across models

4. **Is there a "Tsirelson bound" for Birkhoff polytope?**
   - Classical bound: vertices (permutations)
   - "Quantum-like" bound: interior (soft mixtures)
   - Our 9/4 vs √5 debate may map to this distinction

---

*R&D Exploratory Analysis*
*Source: DeepSeek-AI mHC Paper (2512.24880v1)*
*Chewed: 2026-01-02*
