The Geometry of Abstraction: A Theoretical Framework for Continual Learning via Recursive Metric Contraction

1.0 Introduction: The Flat Manifold Problem in Continual Learning

The central challenge of continual learning in artificial systems is a fundamental geometric barrier: the flat manifold problem. When the accumulating stream of experience is modeled as a trajectory within a fixed-dimensional representational space, the volume required to store this experience grows linearly with time. This relentless expansion inevitably leads to trajectory overlap, a geometric collision that manifests as the well-known phenomenon of catastrophic interference, where new learning overwrites or corrupts previously acquired knowledge.

Prevailing approaches attempt to mitigate this issue through forms of geometric expansion. Techniques such as overparameterization, generative replay, and kernel methods effectively increase the system's capacity by embedding data into higher-dimensional spaces or expanding the support of the learned distribution. While these strategies are effective in finite learning regimes, they are ultimately unsustainable for open-ended, lifelong learning. They are predicated on a scaling law where representational resources must grow in proportion to experience (d ∝ L), a requirement that is fundamentally incompatible with systems operating on fixed hardware in an unbounded world.

The core thesis of this paper is that the resolution to this paradox lies not in geometric expansion but in topological transformation. We propose a framework of Recursive Metric Contraction, where abstraction is formalized not as a symbolic grouping but as a geometric deformation—specifically, a quotient map that collapses the metric tensor of the representational manifold. This process actively folds the manifold of experience, reducing its effective diameter and representational demand without increasing its ambient dimension.

This paper substantiates our framework through the introduction and analysis of three core theorems. The Bounded Capacity Theorem establishes how recursive quotient maps enable the stable representation of arbitrarily long temporal trajectories within a bounded volume. The Topological Collapse Separability Theorem proves that this contraction mechanism renders complex, non-linearly separable data linearly separable in its native dimension. Finally, the Parity-Partitioned Stability Theorem provides a principled solution to catastrophic forgetting by demonstrating how orthogonal manifolds for active learning and stable memory can coexist without interference.

Collectively, these results present a cohesive theory demonstrating that unbounded experience can be stably represented within a fixed-dimensional system. We begin by providing a formal geometric definition of the problem that this framework aims to solve.

2.0 A Geometric Formulation of Catastrophic Interference

To develop a rigorous solution, we must first formalize the problem of continual learning within a geometric framework. By interpreting experience and memory through the lens of manifold geometry, we can define the concepts of a system's temporal manifold and its representational capacity with precision. This formulation provides a clear, quantitative basis for understanding catastrophic interference not as an algorithmic flaw, but as a direct consequence of geometric capacity overflow.

The Temporal Manifold

Drawing from the manifold hypothesis for sequential data, we formalize the stream of experience as a trajectory, γ(t), on a Riemannian manifold, (M, g), where M is the system's representational space and g is the metric tensor defining distances within that space. In this view, learning is not simply the storage of discrete data points but a process that actively shapes the geometry of the space in which inference occurs.

Linear Capacity Growth (Lemma 1)

The geometric origin of catastrophic interference becomes apparent when we consider the properties of this temporal manifold. If the manifold M is flat, or approximately Euclidean, the geodesic distance dg(x0, xt) between the beginning of experience and the present time t grows linearly with the length of the trajectory. To preserve the ability to distinguish past states, the system must maintain an ϵ-cover of this trajectory—a set of ϵ-sized balls whose union contains the entire path. The number of elements required for this cover, N(ϵ,M), serves as a direct measure of the system's required representational capacity. For a flat manifold, this number scales linearly with the trajectory length L, leading to the relation:

N(ϵ,M) ∝ L

This linear growth in representational demand is the essence of the flat manifold problem. As L → ∞, the required capacity diverges, and in any fixed-dimensional system, the ϵ-balls are forced to overlap, causing distinct memories to become indistinguishable. This linear growth in representational demand is the essence of the flat manifold problem. Therefore, any sustainable solution to continual learning must incorporate a mechanism that transforms the geometry of M itself, actively managing its volume to prevent unbounded capacity growth.

3.0 The Proposed Framework: Recursive Metric Contraction

We propose Recursive Metric Contraction as the primary mechanism for overcoming the linear growth of representational demand. Instead of allowing the container of experience to grow indefinitely, this framework actively folds and compresses the experience itself, transforming its topology to fit within a fixed volume. This section defines this core operation and establishes its capacity-regulating properties.

Condensation as Metric Contraction

We formalize abstraction as a geometric operation that contracts the metric tensor over validated, recurring subsets of the temporal manifold. This operation is implemented through a quotient map (q: M → M/∼), a topological transformation that identifies all points within a validated neighborhood as equivalent. This process effectively collapses the sub-manifold corresponding to a recurring concept or temporal sequence, identifying a complex trajectory with a single point in the resulting quotient space, thereby reducing the sub-manifold's contribution to the total representational volume to that of a single point.

By recursively applying such contractions, the system builds a hierarchy of quotient manifolds, M0 → M1 → ... → MD. A "token" at a higher level k corresponds to a non-trivial region—potentially a long and complex temporal segment—of the original manifold M0.

The Bounded Capacity Theorem

The primary consequence of this recursive process is formalized in our first main result.

Theorem (Bounded Capacity): Recursive quotient maps allow the embedding of arbitrarily long temporal trajectories into bounded representational volumes. While the covering number of the original manifold M0 may diverge, the covering numbers of the induced upper-level quotient manifolds remain bounded.

This theorem reveals a fundamental trade-off at the heart of our framework: the system exchanges linear growth in metric space (∝ L) for logarithmic growth in topological depth (∝ logL). Abstraction, therefore, acts as a capacity-regulating mechanism, continuously reducing the number of distinguishable states that must be actively maintained. The complexity of the experience is not erased; it is encoded into the depth of the abstraction hierarchy itself, which grows far more slowly than the raw timeline of events.

Physical Realization of Metric Contraction

This mathematical formalism is not merely an abstraction but is directly analogous to established biological mechanisms. The processes of attractor formation and "chunking" observed in hippocampal and cortical circuits, where repeated co-activation of neural populations strengthens their synaptic connections, can be interpreted as physical implementations of local metric contraction. States that reliably co-occur become separated by shorter functional and geodesic distances in the neural state space.

Extending this intuition to modern neural architectures, we can interpret a learned token as the physical realization of a quotient map: it is a metric singularity or "wormhole" that represents the collapsed sub-manifold. These tokens represent regions of extreme positive curvature that act as geodesic shortcuts, bridging distant and disparate points in the raw temporal manifold. An abstraction, in this view, is a valid and useful "wormhole" that shortens the path of inference.

This framework successfully addresses the problem of capacity, but it raises a new challenge: how to ensure that the process of metric contraction does not destroy the very information it is meant to preserve.

4.0 Preserving Discriminability: The Topological Collapse Separability Theorem

A metric contraction is only useful if it simplifies a representation without sacrificing decision correctness. The process of collapsing the manifold must not merge conceptually distinct regions or erase critical decision boundaries. This section introduces the theoretical guarantees ensuring that our proposed mechanism preserves the informational integrity of the data.

An Alternative to the Kernel Trick

Machine learning has traditionally solved problems of non-linear separability using the Kernel Trick, which implicitly projects data into a higher, often infinite-dimensional, feature space where the data becomes linearly separable (d → ∞). Our framework proposes a parsimonious dual to this approach. Instead of expanding the ambient space to separate points (d → ∞), topological collapse contracts the intrinsic distance between related points to achieve separability within the original finite dimension (N → 1).

Theoretical Foundation: Urysohn's Lemma

The theoretical basis for this claim is a classic result from general topology.

Lemma (Urysohn's Lemma): Let X be a normal topological space, and let A and B be two disjoint closed subsets of X. Then there exists a continuous function f: X → [0, 1] such that f(x) = 0 for all x in A and f(x) = 1 for all x in B.

This lemma guarantees that separability can be achieved through a continuous deformation of the space itself, rather than requiring dimensional expansion. The quotient map is precisely such a deformation, collapsing the metric within sets A and B to render them separable by a simple hyperplane.

The Topological Collapse Separability Theorem

This foundation leads to our second major result, which proves the power of this dual approach.

Theorem (Topological Collapse Separability): Recursive quotienting renders non-linearly separable temporal sequences linearly separable in the limit. By transforming the topology of the manifold, the system can achieve perfect separability within its original finite dimensionality, bypassing the need for infinite-dimensional kernel projections.

Correctness under Abstraction (Theorem 4)

A critical corollary of this theorem is that the semantic integrity of the representation is maintained throughout the abstraction process.

Corollary (Correctness under Abstraction): Semantic discriminability is a topological invariant that descends continuously through the condensation hierarchy. The collapsed representation in a quotient space retains the exact decision boundaries of the original space.

This ensures that as the system builds its hierarchical representation of the world, the abstractions it forms remain faithful to the underlying structure of the data. Having established that we can compress experience without losing information, we now turn to the final challenge: preventing this compression process from interfering with existing memories.

5.0 Achieving Stability: The Parity-Partitioned Stability Theorem

The framework has so far addressed capacity and discriminability. However, it has not yet solved the stability-plasticity dilemma. While the Topological Collapse Separability Theorem guarantees that a given abstraction can be successfully formed, the associated metric distortion could still catastrophically interfere with previously stored memories. This section resolves this dilemma by introducing a fundamental architectural principle that guarantees interference-free learning.

The Parity Alternation Principle

We propose that the state space is partitioned into two functionally and geometrically distinct manifolds that are held in a state of homological orthogonality.

* A "flow" manifold, associated with odd-dimensional homology (H_odd), serves as the substrate for active learning, exploration, and the formation of new abstractions. It is characterized by its plasticity.
* A "scaffold" manifold, associated with even-dimensional homology (H_even), serves as the stable repository for consolidated memories and crystallized knowledge. It is characterized by its rigidity.

This formal separation provides a rigorous topological substrate for established cognitive and computational theories. It mirrors Daniel Kahneman’s dual-process model, where the metabolically expensive search for new structure in the flow manifold corresponds to "System 2" (slow thinking), while efficient navigation of the condensed scaffold manifold corresponds to "System 1" (fast thinking). It is also analogous to the alternating phases of the wake-sleep algorithm, which separates periods of interaction with a 'fluid' topology for exploration from periods of consolidation into a 'crystallized' topology for storage.

The Parity-Partitioned Stability Theorem

This architectural separation provides the foundation for our third and final core theorem, which offers a principled solution to catastrophic forgetting.

Theorem (Parity-Partitioned Stability): If the state space is partitioned into orthogonal flow (H_odd) and scaffold (H_even) manifolds, then the metric deformations of the flow manifold during active learning do not disturb the metric structure of the scaffold manifold.

This homological orthogonality provides a rigorous guarantee of zero topological interference. It suggests that the brain avoids catastrophic forgetting not through complex, algorithm-level weight consolidation, but through a fundamental, architectural separation of concerns. Plasticity and stability are not competing properties but are relegated to orthogonal subspaces that can be updated independently.

This result completes the core theoretical structure of our framework, providing a pathway for stable, unbounded learning within a fixed-capacity system.

6.0 Discussion and Implications

The three core theorems—Bounded Capacity, Topological Collapse Separability, and Parity-Partitioned Stability—collectively establish a cohesive geometric framework for continual learning. This perspective shifts the focus from managing a growing list of memories to dynamically reshaping the space in which memories reside. This section synthesizes the major implications of this approach and acknowledges its current theoretical limitations.

Core Contributions

1. From Scaling Laws to Folding Laws: The framework argues for a paradigm shift in how we approach the development of large-scale AI. Rather than pursuing "Scaling Laws" that demand ever-larger models and datasets, we should seek "Folding Laws"—principles and architectures that maximize the topological density and geometric efficiency of a fixed-capacity system.
2. Abstraction as a Capacity Control Mechanism: We provide a task-agnostic, geometric criterion for the utility of an abstraction. A valid abstraction is one that creates a metric singularity via a quotient map, thereby decreasing the covering number (and thus the representational demand) of the active manifold. This redefines abstraction as a fundamental mechanism for capacity control.
3. A Resolution to the Stability-Plasticity Dilemma: Our framework resolves this long-standing dilemma through an architectural separation of concerns. By relegating plasticity and stability to orthogonal manifolds, the system can learn continuously without catastrophic interference. This contrasts sharply with prevailing methods that rely on complex algorithms to regularize and consolidate weights within a single, monolithic network.

Key Limitations

* The Compressibility Assumption: The theory requires that the input data stream contains recurring, compressible structure that admits non-trivial metric contraction. The framework does not apply to maximally entropic or incompressible data, where the temporal manifold would remain effectively flat and capacity demands would grow linearly.
* The Search for Topology: While the framework proves the existence of a separating quotient map via Urysohn's Lemma, it does not provide an efficient algorithm for finding it. Discovering the optimal topological deformation remains a challenging search problem.
* Approximate Orthogonality: The assumption of strict orthogonality between the flow and scaffold manifolds is an idealized limit. Biological implementations likely achieve this separation approximately, through mechanisms like oscillatory gating or partial synaptic segregation. Future work must characterize the stability of the system under conditions of approximate orthogonality and residual coupling.

This framework provides a theoretical foundation for how fixed-capacity systems can, in principle, support unbounded learning, paving the way for new architectural designs.

7.0 Conclusion

This paper has presented a theoretical framework that recasts the problem of continual learning in the language of geometry and topology. We have argued that the central challenge is not an absence of memory but an inefficient use of representational space, a consequence of operating on a geometrically "flat" manifold of experience. Our resolution, Recursive Metric Contraction, demonstrates that a system can accommodate an unbounded history by actively transforming the topology of its own representational space.

The core problem of continual learning, catastrophic interference, is not an unavoidable consequence of finite memory but a failure to dynamically transform the topology of the representational manifold. By collapsing recurring structures via quotient maps, a system can maintain bounded representational capacity, preserve the discriminability of its knowledge, and ensure the stability of consolidated memories through architectural orthogonality.

Ultimately, this framework suggests that stable, unbounded learning is achievable in fixed-capacity systems if and only if they can progressively fold the manifold of experience, replacing the linear search for past events with geodesic shortcuts through a recursive quotient topology.
