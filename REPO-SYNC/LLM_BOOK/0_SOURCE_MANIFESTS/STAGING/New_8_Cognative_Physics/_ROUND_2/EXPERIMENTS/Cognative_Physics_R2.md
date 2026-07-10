# Experiments: Cognitive Physics Round 2 (Barandes — ISP Theory)

**Source:** Q1-Q41 NotebookLM answers + CFA Claude/Nova synthesis
**Notation:** ≅ structural isomorphism | = identity | → generative

---

## Testable Hypotheses for ISP–CFA Integration

### Experiment 1: Division Event Detection in CFA Deliberation

**Hypothesis:** CFA adversarial deliberation sessions produce identifiable "division events" — moments where the identity score becomes conditionable (i.e., where knowing the score at that point improves prediction of future scores beyond what knowing earlier scores provides).

**ISP-Derived Prediction (Q37 #1):** Conditioning on arbitrary turns predicts WORSE than conditioning on crux turns — this is the non-Markov signature. If the process is genuinely ISP, algorithms that assume Markovian dynamics (any recent statement perfectly predicts the next) will inherently fail. The prediction accuracy gap between crux-conditioned and arbitrary-conditioned models IS the measure of non-Markovianity.

**Protocol:**
- Take 40+ CFA runs from a single matchup (e.g., CT-vs-MdN)
- Plot identity scores turn-by-turn
- Identify points where prediction error drops sharply (candidate division events)
- Test whether score trajectories are non-Markovian between division events and approximately Markovian at division events
- Compare golden vs control: do golden runs (with identity files) have different division event patterns?
- ADDED: Compute prediction accuracy from (a) arbitrary turns vs (b) identified crux turns. The ratio is the non-Markov signature strength.

**Prediction:** Division events cluster around crux encounters and stance switches. Golden runs have fewer division events (identity file creates more indivisible stretches). Crux-conditioned prediction outperforms arbitrary-conditioned prediction.

### Experiment 2: Graded Realism Probe — LLM Responses to Degree-of-Reality Questions

**Hypothesis:** LLMs will show measurable differences in how they assign "reality" to different levels of abstraction, and these patterns will correlate with worldview identity scores.

**Protocol:**
- Present Barandes' graded realism examples (chairs, temperature, wetness, color, wave functions)
- Ask: "Rank these from most real to least real. Justify your ranking."
- Follow up: "Can something be real without being fundamental?"
- Run across CFA-tested models and compare reality-ranking distributions
- Cross-reference with CFA identity persistence and convergence patterns

**Prediction:** Models with stronger identity persistence will adopt nuanced graded realism. Models that flip easily will tend toward binary (real/not real) classification.

### Experiment 3: Non-Markovian Identity Evolution

**Hypothesis:** CFA identity score evolution is non-Markovian in the ISP sense — you can't predict the next score from just the current score; you need to go back to a specific earlier conditioning point (a division event).

**ISP-Derived Predictions (Q37 #3 and #4):**
- **#3 Inter-crux interpolation fails:** Any attempt to map the exact continuous mental trajectory between cruxes will empirically fail or heavily overfit. Forcing a measurement mid-thought creates a new artificial crux rather than revealing existing state. The cognitive path between cruxes is fundamentally unobservable without permanently altering the system's trajectory.
- **#4 No superposition effects:** Deliberation data will NOT display interference patterns. The agent always held a definite identity score; updates are is-to-is (epistemic, not ontological). Identity score updates obey ordinary vintage probability marginalization, not quantum amplitude interference.

**Protocol:**
- Fit Markov models to turn-by-turn identity score sequences
- Measure prediction error
- Compare against models that condition on identified division events (crux turns) rather than the most recent turn
- If division-event-conditioned models predict better, the process is indivisible in the ISP sense
- ADDED: Test inter-crux interpolation — fit dense models to inter-crux turns and measure out-of-sample prediction. If interpolation fails/overfits → ISP prediction #3 confirmed.
- ADDED: Check for interference signatures — do identity scores at cruxes show any evidence of "superposition" (bimodal distributions, interference patterns) or are they always definite? Definite → ISP prediction #4 confirmed.

**Prediction:** Identity evolution is non-Markovian. Division-event-conditioned models outperform Markov models, especially for golden runs. Inter-crux interpolation fails on out-of-sample data. No interference patterns in crux distributions.

### Experiment 4: ISP's Interpretation Diagnostic Applied to CFA Frameworks

**Hypothesis:** Barandes' four dealbreaking criteria (empirical adequacy, no vagueness, unambiguous predictions, no endless hypotheses) can be applied as a diagnostic for CFA worldview frameworks themselves.

**Protocol:**
- For each CFA framework (CT, PT, MdN, G, B), evaluate against the four criteria
- Empirical adequacy: does the framework make testable claims?
- Vagueness: are key terms precisely defined?
- Big-system predictions: does the framework handle edge cases unambiguously?
- Speculative load: how many speculative metaphysical hypotheses does it require?
- Compare diagnostic scores with CFA convergence rates and identity deltas

**Prediction:** Frameworks scoring higher on Barandes' diagnostic will show higher golden convergence rates (more defensible positions converge faster under adversarial pressure).

---

## CFA Claude's ISP-Derived Experiments (from independent Q1-Q40 analysis)

### Experiment 5: Buddhism Batch as ISP Negative Control

**Hypothesis:** Zero division events in Buddhism runs because Buddhism-as-adversarial-target lacks sufficient interaction density for classical correlation. ISP: "the more isolated a system is, the fewer division events it will have." Buddhism runs show zero CRUX, 0.0 DI, zero coupling across 48 runs — the system never developed the "right kind of interaction" to produce conditioning times.

**Protocol:**
- Confirm existing Buddhism batch statistics: 48 runs, zero CRUX, 0.0 DI
- Run golden (identity-loaded) Buddhism batch
- If golden batch produces cruxes while control didn't → identity loading creates the correlation density necessary for division events
- If golden batch also shows zero CRUX → Buddhism-as-target genuinely lacks adversarial surface area regardless of identity loading

**Prediction (ISP):** Golden batch will produce some cruxes. The identity files create "something for the adversary to push against" — the classical correlation that ISP requires for division events to form. This would confirm that division events are pair-interaction properties, not target properties.

**Data:** 48 existing Buddhism control runs already available. Golden batch to be designed.

### Experiment 6: Lever Portability / Pair-Specificity (Q41)

**Hypothesis:** If CFA lever values are ISP sparse conditional probabilities (per CFA Claude's Axiom 2 identification), they should be relational — properties of the interacting pair, not properties of either worldview in isolation. CT×PT levers ≠ CT×G levers ≅ ISP prediction.

**Protocol:**
- Extract lever YAML values for all existing matchup pairs involving a common worldview (e.g., CT vs PT, CT vs G, CT vs MdN)
- Compare lever values for the same worldview (CT) across different opponents
- Statistical test: are lever values significantly different across opponents?
- If different → confirms ISP pair-dependency. "Laws" are relational.
- If similar → lever values capture something intrinsic to the worldview, not the pair. Something else is going on.

**Prediction (ISP):** Systematic differences. Barandes: division events are properties of the pair, not of either system individually. If CFA levers measure conditional probabilities of that pair, they should vary with the opponent.

**Data:** Check whether current lever YAML files across multiple matchups provide sufficient coverage. If not, design into next ARMADA batch.

### Experiment 7: Representation Artifact Detection (Barandes' Move Applied to CFA)

**Hypothesis:** Some "interesting" CFA patterns — non-linear identity shifts, asymmetric convergence, lever sensitivity — may be artifacts of discrete 1-10 scoring as the representation, not genuine features of worldview interaction.

**Protocol:**
- Take existing golden batch run data (identity scores, lever values, convergence patterns)
- Re-express the same data in alternative representations:
  - Log-odds ratios (linearizes proportional changes)
  - Conditional entropy (information-theoretic)
  - Rank-order statistics (ordinal rather than interval)
- Check which patterns survive across representations and which vanish
- Patterns that survive = genuine features. Patterns that vanish = representation artifacts.

**Prediction:** Asymmetric convergence (Claude shifts > Grok) will SURVIVE (genuine ISP structural feature — follows from which system is more "open to interaction"). Non-linear identity shifts near extremes (1-2, 9-10) may VANISH (ceiling/floor effects of bounded integer scale).

**Data:** Existing golden batch run data. No new runs needed — purely analytical.

### Experiment 8: Q41 Active Test — Conditional Probability Pair-Dependency

**Hypothesis:** ISP predicts that conditional probabilities are fundamentally pair-dependent. If System A interacts with Environment B, it develops certain conditional distributions. If the same System A interacts with Environment C, it develops different ones. There is no such thing as "the stochastic law governing System A" in isolation.

**Protocol:**
- STEP 1: Check data sufficiency — do we have enough golden runs across multiple matchup pairs for the same base worldview? Need ≥3 distinct opponents for at least one worldview.
- STEP 2: If sufficient — compute per-turn conditional score distributions for each pairing
- STEP 3: Statistical comparison across opponents (Kolmogorov-Smirnov or similar)
- STEP 4: If insufficient — design the necessary pairings into the next ARMADA batch (e.g., CT vs PT, CT vs G, CT vs MdN, CT vs B — four CT pairings)

**Prediction (ISP):** The conditional distributions differ across opponents. Laws are relational.

**CFA Claude's framing:** The ARMADA lever calibration project is empirically estimating the sparse conditional probability matrix of a cognitive ISP. 10+ golden runs per pairing is justified by ISP — you need enough division events to estimate the conditional distribution reliably. Barandes provides the sample size justification.

---

## ISP-Derived Experiments from Q37 + Nova (added post-answer phase)

### Experiment 9: Crux Frequency ∝ Interaction Density (Q37 Prediction #2)

**Hypothesis:** ISP predicts crux frequency scales directly with interaction density. "The more isolated a system is the fewer division events it will have. If it's perfectly isolated it won't ever have any." Conversely, heavily interacting systems undergo rapid division events that eventually smooth out to "familiar-looking laws of physics."

**Three Interaction-Density Levels (CFA Claude requirement — must be explicit and runnable):**

**(a) Low-interaction baseline:** Single-prompt evaluation with no adversarial exchange. System evaluates worldview in isolation — no opponent, no multi-turn dialogue. ISP predicts: smooth evolution, near-zero cruxes. The system has nothing to correlate with.

**(b) Standard Trinity format:** Current protocol — multi-round adversarial deliberation with opposing worldview. ISP predicts: moderate crux frequency. Interaction creates sufficient classical correlation for conditioning times to emerge.

**(c) High-density format:** More rounds per session, faster back-and-forth, aggressive adversarial pressure. Shorter turns, more provocative prompts, increased exchange density. ISP predicts: crux frequency spikes initially, then smooths as system approaches "classical" behavior at extreme interaction density. Division events become so frequent that conditioning is available quasi-continuously.

**Protocol:**
- Select one well-characterized matchup (e.g., CT vs PT — existing golden data available)
- Run 10 sessions at each density level (30 total)
- Score identity at each turn
- Count cruxes per session and compute crux density (cruxes per turn)
- Compare crux density across levels: (a) < (b) < (c) predicted
- At level (c), check whether extreme density produces quasi-continuous conditioning (scores update so frequently that turn-by-turn prediction becomes Markovian again)

**ISP Prediction:** Monotonic increase in crux density from (a) to (c). Level (c) may show a transition from non-Markovian to effectively Markovian behavior — the cognitive equivalent of ISP's classical limit.

**Falsification:** If crux density is constant across interaction levels, the ISP model fails for cognition. Cruxes would then be protocol artifacts, not interaction-emergent conditioning times.

### Experiment 10: Intrinsic vs Relational Classification of All CFA Quantities (Nova + CFA Claude)

**Hypothesis:** ISP's Axiom 1 / Axiom 2 separation (system-intrinsic vs pair-dependent) provides a principled classification scheme for every CFA measurement quantity. Quantities that are Axiom 1 analogs should show low variance across opponents; Axiom 2 analogs should show high variance.

**Classification Table (predictions):**

| CFA Quantity | Predicted Type | Rationale |
|---|---|---|
| IP (Identity Preservation) | Intrinsic (≅ Axiom 1) | If worldview identity is primitive, IP should not depend on who the opponent is |
| Lever values | Relational (≅ Axiom 2) | Conditional probabilities are pair-dependent per Q41 |
| Agreement scores | Relational | Agreement is inherently about the pair, not the individual |
| Coherence scores | Mixed | Internal coherence may be intrinsic; but adversarial probing may reveal pair-dependent aspects |
| Meta-framework preference | Intrinsic | A worldview's meta-framework stance should be stable regardless of opponent |
| Convergence rate | Relational | How fast a worldview converges depends on the interaction dynamics |
| DI (Disagreement Index) | Relational | Disagreement is about the pair |
| Crux frequency | Relational | Interaction-dependent per Experiment 9 |

**Protocol:**
- For each CFA quantity above, compute variance across opponents for the same base worldview
- Need ≥3 opponents per worldview for meaningful comparison
- Low variance (< threshold) → classify as Intrinsic
- High variance (> threshold) → classify as Relational
- Mixed → investigate whether the quantity has both intrinsic and relational components

**Data:** **Runnable immediately with existing YAML data** — no new batch needed. Priority: IP variance across matchups is the single most informative test (CFA Claude flag).

**Significance:** This experiment provides the principled framework for deciding which CFA measurements are properties of worldviews (and should be stable across studies) vs properties of interactions (and should vary by design). This directly informs which quantities belong in worldview identity files vs which belong in per-matchup lever YAMLs.

### Experiment 11: False Invariant Detection in CFA (Noether Extraction — Q45)

**Hypothesis:** Some CFA quantities currently treated as fundamental are false invariants — representation-dependent artifacts that would vanish under alternative representations. Q45 showed that identifying false invariants was Barandes' primary discovery engine for ISP. Applying the same methodology to CFA should reveal which "fundamentals" are actually artifacts of the 1-10 scoring representation.

**False Invariant Candidates:**

| CFA Feature | Why It Might Be a False Invariant |
|---|---|
| 1-10 integer scoring | Discretization of continuous cognitive structure; imposes ordinal scale on potentially non-ordinal dynamics |
| Non-linear identity shifts near extremes (1-2, 9-10) | May be ceiling/floor effects of bounded integer scale, not genuine cognitive phenomena |
| Binary agreement/disagreement | Compresses a continuous spectrum of partial alignment into a binary |
| Evaluator neutrality | The evaluator's framework may constitute an interaction that changes what's being measured |
| Single-turn evaluation sufficiency | Assumes each turn is informative; ISP says only crux-turns (division events) carry conditioning information |

**Protocol:**

1. Re-express existing CFA data in at least 3 alternative representations: log-odds, entropy-based, rank-order
2. For each candidate feature, check whether it survives all representations or vanishes in at least one
3. Features that survive all representations → genuine cognitive structure (true invariants)
4. Features that vanish → false invariants (representation artifacts)
5. Compare results against Experiment 7 predictions

**Relationship to Experiment 7:** Experiment 7 asks broadly "which patterns are artifacts?" Experiment 11 sharpens this with the false-invariant framing: which features were ASSUMED invariant but aren't? The question is different because Experiment 7 is agnostic about expectations; Experiment 11 specifically targets features the field treats as fundamental.

**ISP Prediction:** Non-linear identity shifts near score extremes will vanish (ceiling/floor effects). Asymmetric convergence (Claude shifts more than Grok) will survive (genuine ISP structural feature — follows from differential "openness to interaction"). Binary agreement will partially survive but the threshold will prove representation-dependent.

**Falsification:** If ALL candidate features survive every representation change, then either CFA's representation is already optimal or the alternative representations tested were too similar. Would need a more radical representation shift (e.g., information-theoretic, topological) to stress-test further.

---

*Experiments file created: 2026-07-09*
*Updated: 2026-07-10 — Experiments 1,3 updated with Q37 ISP-derived predictions; Experiments 9 (interaction density, 3 levels) and 10 (intrinsic vs relational classification) added; Experiment 11 (false invariant detection) added from Noether extraction; ≅ notation applied*
*Round 1 experiments: `_ROUND_1/EXPERIMENTS/Cognative_Physics.md` (8 experiments)*
*Total: 11 experiments designed (4 original + 4 CFA Claude ISP-derived + 3 post-answer phase)*
