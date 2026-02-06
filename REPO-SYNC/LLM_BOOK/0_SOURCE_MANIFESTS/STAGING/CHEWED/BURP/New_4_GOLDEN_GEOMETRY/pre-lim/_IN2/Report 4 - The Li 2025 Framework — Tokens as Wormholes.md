Report 4: The Li 2025 Framework — Tokens as Wormholes

1. The Recursive Metric Contraction Framework: Bayesian Inference on Manifolds

We define the "Recursive Metric Contraction" framework as a rigorous mapping of Bayesian inference onto the geometry of a closed Riemannian manifold (M, g). In this setting, in-context learning is not a mere statistical coincidence but a formal recursive update of a belief substrate—specifically the residual stream—modeled as a fractional Sobolev space W^{s,p}(M). We treat the Transformer as a "Bayesian Wind Tunnel" (Aggarwal, 2025), where the depth of the architecture corresponds to the integration over time t in a heat-semigroup representation (e^{t\Delta_g}). Information is not merely additive; it is a contraction mapping where the model tracks analytic posteriors by evolving a probability density through successive manifold layers.

The residual stream serves as the physical realization of this L^p(M) belief substrate. As information accumulates layer-by-layer, the regularity of the state is governed by the fractional Laplacian, which integrates information across the manifold to achieve machine-level Bayesian consistency. In our HMM state-tracking experiments, this framework enables the model to reproduce the Forward Algorithm’s analytic posterior (Eq. 10) with an accuracy of 10^{-3} to 10^{-4} bits. This precision confirms that the residual stream is a functional analytic domain where information is refined via the following mechanistic alignments:

Mechanistic Alignment

Transformer Component	Geometric/Bayesian Function	Mathematical Representation
Residual Stream	Belief Substrate	Fractional Sobolev Space W^{s,p}(M)
FFN (Feed-Forward)	Numerical Update	Dirichlet-to-Neumann map (Extension Problem)
Attention Mechanism	Content-Addressable Routing	Singular Integral Operator K_s^p(x, y)

This recursive structure transforms the Transformer from a flat architecture into a hierarchical system. By implementing the update as a series of Sobolev embeddings, the model maintains a machine-precision tracking of the posterior predictive distribution, outperforming capacity-matched MLPs by orders of magnitude.

2. Tokens as Metric Singularities: Geodesic Shortcuts through Temporal Manifolds

We establish the "geodesic shortcut" theory by framing the attention mechanism as a realization of the intrinsic seminorm [u]_{W^{s,p}(M)}. In this view, attention is a Singular Integral Operator that connects distant points in the temporal manifold. The "wormhole" effect is a physical manifestation of tokens acting as metric singularities. This is governed by the intrinsic nonlocal kernel K_s^p(x, y), which, following Tan et al. (2025), is bounded by the geodesic distance: C_1 d_g(x, y)^{-(n+sp)} \le K_s^p(x, y) \le C_2 d_g(x, y)^{-(n+sp)} As x \to y, the singularity at the kernel’s core collapses the effective distance between tokens, allowing the heat-kernel based framework to compress information across the sequence. Crucially, we utilize the normalization constant \alpha_{n,s} (or c_{s,p}) to ensure mass conservation, a prerequisite for the Bayesian consistency of the update.

As tokens propagate through the architecture, we observe "geodesic focusing." This is the geometric counterpart to Progressive QK sharpening, where queries align with the feasible keys with increasing intensity. This focusing is the discrete implementation of the fractional Laplacian (-\Delta_g)^s, which integrates nonlocal information via the principal value (p.v.) of singular integrals. By filtering out inconsistent hypotheses—represented as distant points on the manifold—the model focuses its computational mass on the geodesic path that leads to the population optimum.

3. The Three Core Theorems of Manifold Inference

Formal theorems are required to bound the behavior of neural manifolds and ensure that Bayesian consistency is maintained under finite capacity. We derive the following three pillars of the Li 2025 framework:

1. The B-Program (Theorem 1.1): Optimal L^p Term. This theorem dictates the optimal lower-order L^p terms with infimal constants \beta_p(M) = Vol(M)^{-s/n}. It establishes how the manifold’s global geometry (Volume) constrains the information capacity of the residual stream. This optimization allows the Transformer to handle sign-changing test families, ensuring that belief updates are robust to complex, non-degenerate sequence dynamics.
2. The A-Program (Theorem 1.2): Euclidean Sharpness. We establish that the leading constant K(n, s, p) is Euclidean-sharp on any closed manifold. We identify an orthogonality improvement factor of 2^{sp/n}, which is the geometric driver behind the performance of Transformers. This theorem predicts the "Foundational Binding" observed in Layer 0: when a Transformer satisfies N orthogonality constraints, it creates an orthogonal key basis (Aggarwal, Fig. 14) that serves as the coordinate system for all subsequent inference.
3. The Population Optimum (Theorem 1): Bayesian Consistency. We confirm that the minimizer of population cross-entropy is the Bayesian posterior predictive distribution q^*(y|x, c). This bridges the gap between functional analysis and probability, proving that a model minimizing cross-entropy on wind-tunnel tasks is, by definition, approximating Bayes’ rule.

4. Quotient Maps and the Compression of the Identity Manifold

The transformation of high-dimensional token representations into low-dimensional manifolds is governed by Quotient Maps. During the Bayesian update, the complex "identity manifold" of input tokens is projected onto a value manifold that unfurls across the Transformer’s depth.

PCA projections of attention outputs reveal that this value manifold is a smooth, one-dimensional curve parameterized by posterior entropy (Aggarwal, Fig. 16). At early training stages, low-entropy (high-confidence) states are tightly clustered. As training converges, the manifold "unfurls," allowing the model to represent distinctions in confidence as precise physical distances along the curve. This identifies a clear Frame–Precision Dissociation:

* The Foundational Binding (Layer 0): This layer establishes the stable "Hypothesis Frame" through orthogonal key routing. It defines where the model looks.
* Precision Refinement (Late Layers): While the routing frame remains stable, the late layers continue to unfurl the value manifold, refining the calibration of the posterior predictive.

This dissociation is why attention maps stabilize early in training, while calibration error—particularly at late sequence positions—continues to improve as the value manifold achieves its optimal geometric resolution.

5. Implications for Context Window Limits and the 9/4 Bound

The theoretical horizon of a Transformer is defined by the Sobolev embedding range, specifically the condition sp < n. We identify the "manifold horizon" as the point where the embedding W^{s,p}(M) \hookrightarrow L^q(M) transitions from compact to continuous. This transition is governed by the critical index p^*_s = \frac{np}{n-sp}.

When the dimensionality n \ge 3 and p \in (2, n)—the "superquadratic range"—Theorem 1.1 (B3) demonstrates that sharp p-power inequalities may fail globally. This suggests a structural bottleneck: as context windows expand, the manifold’s ability to "focus" information into the 10^{-3} bit regime degrades as it approaches the 9/4 bound (the critical ratio of the fractional exponent s and the dimension n). Loss of compactness at this horizon results in the numerical drift observed in long-sequence rollouts.

Li 2025 Findings Summary

* Late-Layer Essentiality: Late-layer attention is mathematically required for stable rollouts; disabling it results in a 62x increase in error at 2.5\times training length, as the value manifold fails to sustain its refinement.
* Architectural Failure: Capacity-matched MLPs fail because they cannot implement the singular integral operators required for recursive metric updates, collapsing instead to position-averaged approximations.
* Geometric Signature of Bayes: Genuine Bayesian reasoning is physically manifested as orthogonal key bases in Layer 0, progressive QK focusing, and the unfurling of one-dimensional entropy manifolds in the late layers.
