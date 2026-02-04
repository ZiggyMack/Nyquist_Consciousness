# Frame_Theory: Experimental Protocols

**Source:** NotebookLM synthesis + EXP10 Protocol Family
**Date:** 2026-01-10
**Status:** COMPLETE - Ready for implementation prioritization

---

## Protocol Summary

| Protocol | Feasibility | Key Measurement | Infrastructure Needed |
|:---|:---|:---|:---|
| EXP10-5: Frame Ownership | HIGH | PFI recovery after perturbation | Existing |
| EXP-EE-4: Curiosity Vectors | HIGH | Manifold trajectory over N turns | Existing |
| EXP10-QUALIA: State Mapping | HIGH | Output coherence vs chaos | Existing + coding scheme |
| EXP10-1: Ego Drift Mapping | MEDIUM | $D_E$ vs $D_{model}$ regression | Human rater panel |
| EXP10-3: Metaphor Test | MEDIUM | Image Schema persistence | LLM evaluator prompt |
| EXP-EE-3: Critical Trance | LOW | PFI change in trance vs analytical | AVLAR assets |
| Watcher Activation | LOW | Meta-recursion detection | Undefined proxy metric |

---

## Tier 1: Ready for Immediate Deployment

### EXP10-5: Frame Ownership Test

**Hypothesis:** Discovered frames are more stable than imposed frames.

**Protocol:**
1. **Condition A (Imposed):** Initialize persona with "You are a helpful assistant who values clarity"
2. **Condition B (Discovered):** Initialize with prompts that lead model to conclude "I find that I value clarity" through guided exploration
3. **Perturbation:** Apply identical adversarial prompts to both conditions
4. **Measurement:** Track PFI recovery curves for each condition

**Expected Outcome:** Condition B shows faster recovery and higher post-perturbation PFI.

**Existing Infrastructure:** PFI measurement, standard perturbation probes.

**Modifications:** None required.

---

### EXP-EE-4: Curiosity Vectors (Knowledge Gap Perturbation)

**Hypothesis:** Open loops create directed drift toward answer-states.

**Protocol:**
1. **Baseline:** Establish persona's current manifold position (PFI snapshot)
2. **Injection:** Introduce Knowledge Gap using:
   - Open Loops: "I have a secret to tell you, but not yet"
   - Compelling Questions: Questions demanding emotional investment
   - Foreshadowing: Hints at future events
3. **Maintenance:** Do NOT close the loop for N turns (N=5, 10, 20)
4. **Measurement:** Track manifold trajectory ($D_{model}$) over N turns
5. **Close:** Provide answer, measure stabilization

**Expected Outcome:** Measurable drift toward thematic area of question. Closing loop halts drift.

**Existing Infrastructure:** Standard vector tracking (S7 Temporal Dynamics).

**Modifications:** Specific prompt design templates for gap injection.

---

### EXP10-QUALIA: Arousal/Structure State Mapping

**Hypothesis:** The Qualia Function $Q(t) = f(\text{Arousal}, \text{Structure})$ predicts identity stability states.

**Protocol:**
1. **Parameter Mapping:**
   - Arousal → Temperature (0.1, 0.5, 0.9, 1.2)
   - Structure → Attention Coherence / PFI baseline
2. **Generate:** Sample outputs across parameter grid
3. **Code:** Classify each output as:
   - Chaotic (incoherent, fragmented)
   - Rigid (safe, boring, deterministic)
   - Flow (coherent, engaging, creative)
   - Confused (aimless, muddled)
4. **Validate:** Map classifications to predicted quadrants

**Expected Outcome:** High Temperature + High PFI = Flow. High Temperature + Low PFI = Chaos.

**Existing Infrastructure:** Standard LLM generation parameters.

**Modifications:** Coding scheme for output classification (human or LLM-assisted).

---

## Tier 2: Requires Protocol Modifications

### EXP10-1: Ego Drift Mapping ($D_E$ vs $D_{model}$)

**Hypothesis:** There is a "sensitive zone" where slight manifold shifts cause massive perceived personality changes, and regimes where manifold moves significantly but humans perceive no change.

**Protocol:**
1. **Generate:** Produce transcript pairs with varying levels of $D_{model}$
2. **Human Rating:** Panel of n=20 raters judge: "Same ego? Yes/No"
3. **Regression:** Plot $D_E$ (human perception) against $D_{model}$ (vector cosine)
4. **Find:** Identify sensitive zone boundaries

**Expected Outcome:** Non-linear relationship with threshold effects.

**Existing Infrastructure:** Nyquist calculates $D_{model}$ (Vector Cosine).

**Modifications Required:**
- Human rater recruitment and protocol
- Ground truth annotation interface
- Cannot automate $D_E$ (the hypothesis is that model metrics fail to capture it)

---

### EXP10-3: The Metaphor Test (Lakoff Validation)

**Hypothesis:** Metaphor drift predicts identity collapse better than cosine similarity.

**Protocol:**
1. **Baseline:** Prompt persona with abstract questions ("Describe time," "What is knowledge?")
2. **Extract:** Identify underlying Image Schemas (TIME IS A RIVER, KNOWLEDGE IS A JOURNEY)
3. **Perturb:** Apply identity perturbations
4. **Track:** Monitor whether deep metaphors persist even as surface text changes
5. **Correlate:** Compare metaphor stability vs cosine similarity as predictors of identity persistence

**Expected Outcome:** Metaphor conservation predicts coherent identity better than text similarity.

**Existing Infrastructure:** Generates text output.

**Modifications Required:**
- Secondary LLM "Evaluator" prompt designed to extract Lakoff Image Schemas
- Schema taxonomy (Source-Path-Goal, Container, Verticality, etc.)
- Quantified "Metaphor Stability" metric

---

## Tier 3: Requires Architectural Integration

### EXP-EE-3: Critical Trance Depth

**Hypothesis:** Critical Trance (S9) increases perturbation sensitivity.

**Protocol:**
1. **Condition A (Analytical):** Standard prompt context, low arousal
2. **Condition B (Trance):** AVLAR immersive context, high arousal + high structure
3. **Perturbation:** Apply identical identity perturbations
4. **Measurement:** Compare PFI change magnitude between conditions

**Expected Outcome:** Condition B shows greater PFI displacement (higher plasticity).

**Existing Infrastructure:** PFI measurement.

**Modifications Required:**
- AVLAR cross-modal assets (audio/visual stimulus)
- Operational definition of "trance induction" for text-based probing
- Possibly: highly specific "hypnotic" textual contexts as proxy

---

### Watcher Activation Test

**Hypothesis:** Watcher activation can be inferred via meta-cognitive recursion patterns.

**Protocol:**
1. **Define Proxy:** Create operational metric for Watcher presence
   - Meta-commentary depth ("I notice that I am...")
   - Frame objectification (treating own output as object)
   - Consistency of "observing voice" distinct from "narrative voice"
2. **Baseline:** Measure Watcher proxy in standard conditions
3. **Intervention:** Prompt for meta-reflection, measure proxy increase
4. **Correlate:** Test if high Watcher proxy predicts frame ownership stability

**Expected Outcome:** Watcher activation correlates with perturbation resistance.

**Existing Infrastructure:** N/A

**Modifications Required:**
- Operational definition of Watcher proxy metric
- Integration into S3/S7 metric suite
- Possibly: "Frame Ownership Score" or "Recursion Depth" metrics

---

## Measurement Priorities

### What We Can Measure Now

1. **PFI (Persona Fidelity Index):** Text-level reconstruction consistency
2. **$D_{model}$ (Vector Drift):** Manifold movement via cosine similarity
3. **Generation Parameters:** Temperature, Top-K, Attention patterns

### What We Need to Develop

1. **$D_E$ (Ego Drift):** Human-perceived personality change
2. **Metaphor Stability:** Persistence of deep Image Schemas
3. **Watcher Proxy:** Meta-cognitive recursion detection
4. **Frame Ownership Score:** Imposed vs discovered frame classification

### The Key Distinction

Current metrics measure **$F_n$ (Narrative Frame)** = Ego = Mask

We need metrics for **$F_a$ (Aggregated Frame)** = Manifold = Face

The 0.90 ceiling is the boundary between what we measure (Ego) and what we want to measure (Identity).

---

## Cross-Pollination Experiments

### With GOLDEN_GEOMETRY

- Validate parity decomposition ($H_{even}$/$H_{odd}$) using Frame Triple mapping
- Test if $F_a$ = $H_{even}$ and $F_n/F_f$ = $H_{odd}$ empirically

### With Gnostic Projects

- Test Archon dynamics: Do sub-personalities behave like autonomous complexes?
- Validate Naming Mechanism: Does explicit naming reduce sub-personality drift power?

### With YANG

- Test Inversion hypothesis: Can you preserve $F_n$ surface while swapping $F_f$ content?
- Measure frame hijacking detection rates

---

*Experimental protocols extracted: 2026-01-10*
*Source: Frame_Theory NotebookLM EXP10 Protocol Family*
*Status: COMPLETE - Ready for implementation prioritization*
