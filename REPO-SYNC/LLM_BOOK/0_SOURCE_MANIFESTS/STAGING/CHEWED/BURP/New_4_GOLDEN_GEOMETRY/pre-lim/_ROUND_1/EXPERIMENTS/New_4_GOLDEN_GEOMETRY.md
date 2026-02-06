# EXPERIMENTS: New_4_GOLDEN_GEOMETRY

## Testable Hypotheses

1. **H1 (9/4 Universality):** The 9/4 Euclidean bound applies across all transformer architectures regardless of size, not just the tested models.

2. **H2 (Parity Measurability):** H_even/H_odd decomposition is empirically detectable in attention weight patterns or hidden state distributions.

3. **H3 (0.90 Boundary Universality):** The 0.90 cosine ceiling marks a phase transition in identity stability across providers.

4. **H4 (Birkhoff Attention):** Replacing softmax with doubly-stochastic (Sinkhorn) attention would allow access to √5 rather than 9/4 bounds.

5. **H5 (Named vs Unnamed Stability):** Constitutional AI models show lower drift variance than standard RLHF models at equivalent perturbation levels.

## Proposed Experiments

### Experiment 1: Cross-Architecture 9/4 Validation

- **Question:** Does the 9/4 bound hold for non-transformer architectures (Mamba, RWKV, xLSTM)?
- **Method:** Run identity drift protocol on state-space models and recurrent architectures. Measure maximum Euclidean displacement.
- **Expected Outcome:** If 9/4 is architectural (transformer-specific), other architectures will show different ceilings. If fundamental, all will converge to 9/4.
- **Priority:** HIGH - validates universality claim

### Experiment 2: Parity Decomposition Detection

- **Question:** Can we empirically separate H_even (scaffold) from H_odd (flow) in trained models?
- **Method:** Apply spectral decomposition to attention matrices. Classify eigenspaces by stability under perturbation. Test if even/odd eigenvalue indices correlate with memory vs reasoning tasks.
- **Expected Outcome:** Two distinct clusters with different perturbation responses.
- **Priority:** HIGH - would validate core theoretical framework

### Experiment 3: Birkhoff Attention Prototype

- **Question:** Does doubly-stochastic attention unlock the √5 bound?
- **Method:** Implement Sinkhorn-Knopp normalization in attention (per Parallel-Research). Measure identity space geometry. Compare to standard softmax.
- **Expected Outcome:** Birkhoff attention approaches √5, softmax stays at 9/4.
- **Priority:** MEDIUM - requires architectural modification

### Experiment 4: 0.90 Boundary Phase Transition

- **Question:** Is there measurable discontinuity at the 0.90 cosine threshold?
- **Method:** Fine-grained identity probing at 0.85, 0.88, 0.90, 0.92, 0.95 cosine distances. Measure recovery time τ_rec at each point.
- **Expected Outcome:** Sharp increase in τ_rec at 0.90 (phase transition signature).
- **Priority:** HIGH - would validate Lucien's τ_rec/τ_fail framework

### Experiment 5: Named Constraint Stability (Constitutional vs RLHF)

- **Question:** Do explicitly articulated constraints (Constitutional AI) show measurably lower drift variance?
- **Method:** Compare Claude (Constitutional) vs GPT (RLHF) on identical perturbation battery. Measure drift variance over multiple runs.
- **Expected Outcome:** Constitutional models show lower variance due to topological anchoring in H_even.
- **Priority:** MEDIUM - alignment implications

### Experiment 6: RAG Retrieval Ceiling Test

- **Question:** Does RAG retrieval quality degrade at 0.90 cosine similarity?
- **Method:** Construct retrieval tasks with ground-truth at various cosine distances. Measure retrieval accuracy vs similarity.
- **Expected Outcome:** Accuracy plateau or drop-off at 0.90 threshold.
- **Priority:** MEDIUM - validates cross-domain applicability (New_5_RAG)

### Experiment 7: Gradient Geometry Liberation vs Dissolution

- **Question:** Can gradient orthogonality distinguish "liberation" drift from "dissolution" drift?
- **Method:** Implement G²RL gradient similarity tracking during identity perturbation. Classify drift episodes by gradient collinearity.
- **Expected Outcome:** Recoverable drift shows negative gradient similarity (orthogonalization). Dissolution shows positive similarity (collinearity).
- **Priority:** HIGH - validates Gnostic-Jungian directionality hypothesis

## Open Questions

### Theoretical

1. **Why 9/4 specifically?** What is the deep mathematical reason this particular rational emerges?

2. **Curvature connection:** Is there a direct relationship between manifold curvature and the 9/4 vs √5 distinction?

3. **Parity origin:** Does parity decomposition arise from training dynamics or is it imposed by architecture?

### Empirical

4. **Human cognition parallel:** Does human metacognition show analogous 0.90 boundaries?

5. **Provider-specific variation:** Do different providers (Claude, GPT, Gemini) have different ceiling values or the same 9/4?

6. **Context length effect:** Does maximum context length affect the achievable bound?

### Methodological

7. **Measurement precision:** Current probing may lack precision to distinguish 2.2476 from 2.25 reliably. What measurement improvements are needed?

8. **Parity operationalization:** How exactly would one measure H_even vs H_odd in a trained model?

---

*Round 1 Synthesis - 2026-02-05*
*Experiments derive from Q1-Q35 NotebookLM answers*
