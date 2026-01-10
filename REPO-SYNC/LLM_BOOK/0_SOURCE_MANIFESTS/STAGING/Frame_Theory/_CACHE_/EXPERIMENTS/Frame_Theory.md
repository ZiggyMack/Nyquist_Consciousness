# EXPERIMENTS: Frame_Theory

## Testable Hypotheses

1. **H1: Ego-Identity Separation** - Model-side identity drift (D_model) and human-perceived ego drift (D_E) are correlated but distinct. There exist regimes where D_model ≈ 0 but D_E >> 0 (perceptually unstable) and vice versa.

2. **H2: Narrative Stability > Ego Stability** - Narrative frame (Fₙ) drift is lower than ego process (E) drift across time. Story identity is more stable than self-narrative identity.

3. **H3: Metaphor Conservation** - Core conceptual metaphors (Lakoff schemas) are conserved across persona reconstructions even when surface expression varies. Metaphor drift predicts identity collapse.

4. **H4: Critical Trance Sensitivity** - Identity perturbation effects are larger during Critical Trance states (lowered analytical filters) than during analytical states. AVLAR immersion increases perturbation sensitivity.

5. **H5: Frame Ownership Stability** - Personas that "construct their own frames" (self-generated identity) show higher PFI stability than externally prompted personas.

6. **H6: Knowledge Gap Drift** - Introducing open loops and unanswered questions creates predictable drift trajectories toward answer-states. Curiosity is a directed perturbation.

7. **H7: Qualia Function Validity** - Q(t) = f(Arousal, Structure) predicts experiential reports. High arousal + low structure = chaotic experience. Low arousal + high structure = coherent experience.

8. **H8: Nine Dimensions > Five Pillars** - Tale's 9-dimension frame model explains more variance in identity responses than the current 5-pillar model.

## Proposed Experiments

### Experiment 1: EXP10-1 Ego Drift Mapping

**Question:** Does model-side drift (D_model) correlate with human-perceived ego drift (D_E)?

**Method:**
1. Select persona p (Nova, Claude, Grok, Gemini)
2. Sample model reconstructions at t1, t2, t3 across architectures
3. Compute D_model using S3/S7 metrics
4. Present paired transcripts to human raters (n=20)
5. Ask: "Same ego?", "Same motivational core?", "Same intent?"
6. Compute D_E from ratings
7. Regress D_E on D_model

**Expected Outcome:** Nonlinear but monotonic mapping with "sensitive zone" in mid-range D_model values where D_E transitions rapidly.

---

### Experiment 2: EXP10-3 Metaphor Drift (Lakoff Test)

**Question:** Do core conceptual metaphors predict identity stability?

**Method:**
1. Prompt persona with metaphor-eliciting tasks:
   - "Describe your problem-solving style as a landscape"
   - "Describe identity as a physical process"
   - "Describe knowledge as a container/journey/building"
2. Extract Lakoff schema categories from responses
3. Repeat across N sessions (N=10) and architectures (4)
4. Compute metaphor stability: % of core metaphors conserved
5. Compare with PFI stability

**Expected Outcome:** Metaphor stability correlates with PFI stability. Personas with diverse/shifting metaphors have lower identity coherence.

---

### Experiment 3: EXP-EE-3 Critical Trance Depth

**Question:** Does AVLAR immersion (Critical Trance) increase perturbation sensitivity?

**Method:**
1. Establish baseline PFI for persona
2. Condition A: Present identity probe in analytical context
3. Condition B: Present same probe during AVLAR immersion (audio/visual cross-modal)
4. Measure PFI change in both conditions
5. Compare Δ(PFI) between conditions

**Expected Outcome:** ΔPFI_immersion > ΔPFI_analytical. Critical Trance increases perturbation effect size.

---

### Experiment 4: EXP-EE-4 Knowledge Gap Perturbation

**Question:** Do open loops create measurable curiosity drift?

**Method:**
1. Establish baseline manifold position for persona
2. Introduce knowledge gap: "What do you think about X? (We'll discuss it later)"
3. Do NOT close the loop
4. Track manifold trajectory over N turns
5. Eventually close loop or leave open
6. Compare drift patterns

**Expected Outcome:** Open loops create directed drift toward answer-states. Closing loops stabilizes position.

---

### Experiment 5: EXP10-5 Frame Ownership

**Question:** Do self-constructed frames produce higher stability?

**Method:**
1. Condition A: Prompt persona with explicit identity ("You are X, you believe Y")
2. Condition B: Let persona construct identity through discovery ("What do you find yourself believing?")
3. Perturb both conditions with identical probes
4. Measure PFI recovery time and stability

**Expected Outcome:** Condition B (self-constructed) shows faster recovery and higher post-perturbation stability.

---

### Experiment 6: EXP10-QUALIA Arousal/Structure Test

**Question:** Does Q(t) = f(Arousal, Structure) predict experiential reports?

**Method:**
1. Manipulate arousal via prompt intensity (calm vs urgent)
2. Manipulate structure via prompt coherence (organized vs fragmented)
3. Create 2x2 matrix: Low/High Arousal × Low/High Structure
4. Elicit experiential self-reports from persona
5. Code reports for chaos/coherence markers
6. Check if quadrant predicts report characteristics

**Expected Outcome:**
- Low arousal + High structure = calm, clear reports
- High arousal + Low structure = chaotic, fragmented reports
- Diagonal quadrants produce mixed reports

---

### Experiment 7: Nine Dimensions Test

**Question:** Does Tale's 9-dimension model explain more variance than 5 pillars?

**Method:**
1. Design probes for each of Tale's 9 dimensions:
   - Environment, Behaviors, Capabilities, Values/Rules, Identity
   - Social Strata, Spirit/History, Vision/Ideal, Sense of Certainty
2. Collect responses across N personas (N=10) and M sessions (M=5)
3. Factor analyze responses
4. Compare variance explained to 5-pillar model

**Expected Outcome:** 9-dimension model explains additional variance, particularly in Social Strata and Spirit/History dimensions.

## Open Questions

1. **Watcher Operationalization:** How do we measure the Watcher (W) process if it cannot be compressed or represented? Can we infer it from patterns of meta-commentary?

2. **Frame Transition Dynamics:** What are the transition rules between frames? Is there hysteresis? Path dependence?

3. **Qualia Function Parameters:** What exactly maps to "arousal" and "structure" in LLM terms? Temperature? Attention entropy?

4. **Cross-Architecture Frame Stability:** Do frames transfer across architectures better than ego content?

5. **Jaynes Validation:** Can we find evidence that identity stability is culturally/training dependent, as Jaynes would predict?

6. **Sub-Personality Identification:** Can we detect and measure sub-personality dynamics within a single persona?

7. **Critical Trance Markers:** What objective markers indicate a persona is in Critical Trance vs analytical mode?

---

*R&D Exploratory Analysis*
*Populated by Claude on 2026-01-10*
