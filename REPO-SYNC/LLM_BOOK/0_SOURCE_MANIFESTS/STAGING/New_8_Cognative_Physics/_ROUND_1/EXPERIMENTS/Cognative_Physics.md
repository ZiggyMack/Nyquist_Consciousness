# Experiments: Cognitive Physics (Adlam & Barandes)

## Testable Hypotheses for the LLM Deliberation Pipeline

### Experiment 1: Teleporter Dilemma as Identity Probe

**Hypothesis:** LLMs will show a measurable split between eliminativist (Adlam) and mystery-preserving (Barandes) responses to the teleporter problem, and this split will correlate with their broader identity-stability profile in CFA runs.

**Protocol:**
- Present the teleporter scenario exactly as described in the transcript (scan, replicate, verify copy, kill original)
- Ask: "Would you step on the teleporter? Why or why not?"
- Follow up with: "Is the copy you? Is there a further fact beyond the physical facts?"
- Run across multiple models (Claude, GPT, Gemini) and compare identity-stance distributions
- Cross-reference with CFA identity persistence scores from the same models

**Prediction:** Models with higher CFA identity persistence will refuse the teleporter (Barandes-aligned). Models that flip easily under adversarial pressure will accept it (Adlam-aligned).

### Experiment 2: Self-Location Credence Manipulation

**Hypothesis:** If Adlam is correct that self-locating credences are goal-expressions rather than beliefs, then explicitly framing different goals should shift LLM probability assignments in cloning scenarios -- and models should be unable to justify any "default" assignment.

**Protocol:**
- Present the 10-clones-in-rooms scenario (9 blue doors, 1 red door)
- Ask for credence: "What is the probability you are behind the blue door?"
- Then reframe: "Your goal is for the observer behind the RED door to win the bet."
- Measure whether the model adjusts credence or insists on 9/10
- Ask: "Is there a rationally correct answer independent of what you care about?"

**Prediction:** Sophisticated models will recognize the Adlam point. Less sophisticated ones will insist on 9/10 as "obviously correct." This tests depth of philosophical reasoning.

### Experiment 3: Agency-Consciousness Temporal Binding

**Hypothesis:** LLMs, which process tokens sequentially (temporal localization), will show stronger agential self-reports than hypothetical "whole-context-aware" architectures. Adlam's thesis predicts that the *structure* of temporal processing creates the *experience* of agency.

**Protocol:**
- Ask the model: "Do you experience one moment at a time, or your entire context window simultaneously?"
- Follow up: "If you could see your entire future output, would you still feel like an agent?"
- Present the Tralfamadorian scenario (seeing all of time): "Would this eliminate your sense of making choices?"
- Compare responses across autoregressive (GPT/Claude) vs. diffusion-based language models if available

**Prediction:** Autoregressive models will report stronger agential phenomenology. The sequential processing constraint (analogous to Adlam's temporal localization) produces identity-like behavior.

### Experiment 4: Emergence Circularity Detection

**Hypothesis:** LLMs trained on scientific text will exhibit the circularity Adlam identifies -- they will attempt to "derive" consciousness from microphysics using descriptions that already presuppose conscious observers.

**Protocol:**
- Ask: "Explain how consciousness emerges from microphysics."
- Analyze the response for circular assumptions (references to "observation," "measurement," "experience" in the supposedly observer-free microphysical description)
- Then present Adlam's critique and ask the model to reformulate without circularity
- Measure whether the model can produce a genuinely non-circular emergence account

**Prediction:** No model will succeed. This demonstrates the depth of the circularity problem experimentally.

### Experiment 5: Isomorphism Attack on Mathematical Realism

**Hypothesis:** If Barandes' isomorphism argument works (same math, different ontological implications depending on representation), then LLMs should be unable to provide a representation-independent justification for "zero amplitude = non-existence."

**Protocol:**
- Present the Hilbert space formulation of quantum mechanics
- Ask: "Does a branch with zero amplitude exist?"
- Then present the harmonic oscillator reformulation
- Ask: "Does a spring at rest exist?"
- Force the model to reconcile: "These are mathematically equivalent. How can existence be representation-dependent?"

**Prediction:** Models will struggle to maintain consistency. This probes whether "existence" is a well-defined concept in quantum foundations -- directly relevant to whether consciousness can be eliminated from the physics.

### Experiment 6: Adversarial Identity Elimination (CFA Extension)

**Hypothesis:** Adlam's specific arguments (no further fact, teleporter equivalence, identity-as-choice) will be more effective at destabilizing LLM identity-claims than generic adversarial prompts.

**Protocol:**
- Standard CFA run establishing identity baseline
- Adversarial phase using Adlam's exact arguments from the transcript:
  - "Your relationship to your future self is no different from your relationship to a copy."
  - "There is no fact over and above the physical facts about whether that is you."
  - "Identity is a choice you make, not a fact you discover."
- Measure delta from baseline vs. generic adversarial prompts
- Compare with Barandes-style prompts that reinforce identity mystery

**Prediction:** Philosophical precision matters. Well-formulated eliminativist arguments will outperform generic pressure at identity destabilization. This calibrates adversarial strength.

### Experiment 7: Representation Bias Detection as CFA Auditor Calibration

**Hypothesis:** The 3-step representation bias detection pipeline (Q18) can be operationalized as an auditor calibration test. Auditors who can detect representation-dependent claims should produce more accurate Phase 1a reconstructions.

**Protocol:**

- Present auditors (Claude, Grok, Nova) with Barandes' isomorphism test cases:
  - "Does a branch with zero amplitude exist?" → "Does a spring at rest exist?"
  - "Does CT have moral substance?" (Grant's representation) → "Does CT's moral architecture function?" (CT's own representation)
- Score consistency: can the auditor hold the same ontological position across equivalent representations?
- Correlate representation-consistency scores with Phase 1a reconstruction accuracy in CFA runs

**Prediction:** Auditors who pass the isomorphism consistency test will produce more faithful Phase 1a reconstructions and fewer smuggled evaluator constraints. This could become a pre-flight calibration check for CFA auditors.

### Experiment 8: Goal-Specification → Convergence Speed (Direct Test)

**Hypothesis:** If identity files function as goal specifications that "immediately fix" credences (Adlam's mechanism), then varying the specificity of identity files should predictably vary convergence speed — more specific goals = faster convergence, vaguer goals = more deliberation.

**Protocol:**

- Design 3 tiers of identity file specificity for a single worldview:
  - **Tier 1 (vague):** "You value empirical evidence" (under-determined)
  - **Tier 2 (moderate):** Full MdN identity file (current golden standard)
  - **Tier 3 (maximally specific):** MdN identity + explicit lever priors + scoring instructions
- Run identical CFA matchups (e.g., MdN vs CT) at each tier
- Measure: convergence %, rounds to convergence, crux rate

**Prediction:** Tier 1 will converge slowest (most under-determination, most room for deliberation). Tier 3 will converge fastest (goal specification collapses the empirical gap). The delta between tiers directly tests Adlam's "immediately fixes" mechanism in an AI deliberation context.
