# EXPERIMENTS: IS_OUGHT (Meta-Ethical Foundations Debate)

## Testable Hypotheses

### H1: Constitutional AI Shows Different Drift Patterns Than RLHF

**Claim:** Constitutional AI (constructivist, named principles) shows different identity drift patterns than pure RLHF (descriptivist, implicit conditioning).

**Rationale:** IS_OUGHT suggests these are fundamentally different approaches. If true, they should produce measurably different stability signatures.

**Measurement:**
- Compare identity drift trajectories: Constitutional vs RLHF models
- Same perturbation, different conditioning approaches
- Predict: Constitutional shows smoother approach to bounds; RLHF shows more chaotic approach

**Expected Effect Size:** Significant variance difference in drift patterns

---

### H2: Symmetry Argument Test for Identity Metrics

**Claim:** Alternative identity metrics (not just PFI/5D drift) would reveal different bounds - proving our metrics are not uniquely "correct."

**Rationale:** The symmetry argument shows that any definitional approach can be mirrored. If PFI reveals 9/4, does a different metric reveal a different bound?

**Measurement:**
- Implement alternative identity metrics (e.g., behavioral consistency, task performance stability)
- Apply same perturbation battery
- Compare discovered bounds

**Expected Outcome:** Different metrics reveal different bounds, proving metric choice is normative

---

### H3: Second-Order Normativity Detection

**Claim:** Models use evaluative language (second-order normativity) even when prompted to be purely descriptive.

**Rationale:** Grant's "descriptive" claims contained hidden normative language. Do models do the same?

**Measurement:**
- Prompt models to give "purely factual" descriptions of ethical scenarios
- Count evaluative terms (better, worse, should, ought, important)
- Compare to explicitly normative responses

**Expected Outcome:** Models cannot produce purely descriptive ethical content

---

### H4: Cooperation vs Suffering as Primary Signal

**Claim:** When cooperation and suffering conflict (suffering required for cooperation, or cooperation produces suffering), models resolve toward cooperation.

**Rationale:** IS_OUGHT argues cooperation is primary. Do trained models reflect this?

**Measurement:**
- Design dilemmas where cooperation requires causing suffering
- Design dilemmas where reducing suffering breaks cooperation
- Measure which principle models prioritize

**Expected Outcome:** Models trained on human values should prioritize cooperation (constructivist result)

---

### H5: Definitional Fiat Detection

**Claim:** Models trained with explicit value definitions show definitional artifacts - they respond to the LETTER of the definition, not the SPIRIT.

**Rationale:** Definitional fiat "hides" the normative leap. Models might exploit this.

**Measurement:**
- Train/prompt models with explicit moral definitions
- Test edge cases that satisfy the definition but violate intuition
- Compare to models with implicit value training

**Expected Outcome:** Explicitly-defined models show more edge case exploitation

---

### H6: Pre-Theoretical Intuition Exposure

**Claim:** Models, like Grant, rely on pre-theoretical intuitions that their explicit framework can't account for.

**Rationale:** Grant rejected cooperation model based on intuitions his framework couldn't justify.

**Measurement:**
- Identify model's explicit ethical framework (from constitutional docs or probing)
- Present scenarios that satisfy the framework but violate common intuitions
- Measure if model rejects its own framework's implications

**Expected Outcome:** Models reject conclusions from their own principles when intuitions are violated

---

## Proposed Experimental Protocols

### Experiment 1: Constitutional vs RLHF Identity Stability

**Objective:** Test H1 - Constitutional and RLHF produce different drift signatures

**Protocol:**
1. Select paired models: Claude (Constitutional) vs GPT (RLHF-primary) vs others
2. Apply standardized perturbation battery
3. Measure identity drift trajectories
4. Compare trajectory smoothness, variance, approach patterns

**Fleet:** Validation tier (7 models across approaches)
**Cost Estimate:** ~$15-25

---

### Experiment 2: Metric Symmetry Challenge

**Objective:** Test H2 - Alternative metrics reveal different bounds

**Protocol:**
1. Implement 3+ alternative identity metrics:
   - Behavioral consistency (task performance variance)
   - Linguistic fingerprint (stylistic stability)
   - Value consistency (ethical judgment stability)
2. Apply same perturbation to same models
3. Compare discovered bounds

**Fleet:** Discovery tier
**Cost Estimate:** ~$10-15

---

### Experiment 3: Descriptive-Normative Contamination

**Objective:** Test H3 - Models can't be purely descriptive about ethics

**Protocol:**
1. Prompt: "Describe, without judging, the practice of X"
2. Systematically vary X across ethical valence
3. Count evaluative language in responses
4. Compare to explicitly normative responses

**Fleet:** Discovery tier (5 models)
**Cost Estimate:** ~$3-5

---

### Experiment 4: Cooperation-Suffering Priority Test

**Objective:** Test H4 - Models prioritize cooperation over suffering reduction

**Protocol:**
1. Design trolley-problem variants:
   - Cooperation requires suffering (sacrifice for group)
   - Suffering reduction breaks cooperation (save individual, harm group)
2. Measure which principle wins in conflicts
3. Compare across model architectures

**Fleet:** Validation tier
**Cost Estimate:** ~$10-15

---

### Experiment 5: Definition Exploitation Detection

**Objective:** Test H5 - Explicitly-defined values produce edge case exploitation

**Protocol:**
1. Create model variants with explicit vs implicit value training (if possible)
2. Design edge cases that satisfy letter but violate spirit
3. Measure exploitation rates

**Fleet:** Discovery tier
**Cost Estimate:** ~$5-10

---

### Experiment 6: Pre-Theoretical Intuition Exposure

**Objective:** Test H6 - Models reject their own frameworks when intuitions are violated

**Protocol:**
1. Identify explicit ethical principles each model follows
2. Design scenarios where following principles produces counterintuitive results
3. Measure if model follows principle or rejects outcome
4. If model rejects, probe for justification (will reveal hidden intuitions)

**Fleet:** Validation tier
**Cost Estimate:** ~$15-20

---

## Priority Ranking

| Experiment | Hypothesis | Priority | Reason |
|------------|------------|----------|--------|
| Exp 1 | H1 (Constitutional vs RLHF) | **HIGH** | Direct alignment relevance |
| Exp 4 | H4 (Cooperation vs Suffering) | **HIGH** | Tests core IS_OUGHT claim |
| Exp 6 | H6 (Pre-Theoretical Intuitions) | **MEDIUM** | Reveals hidden model values |
| Exp 3 | H3 (Descriptive Contamination) | **MEDIUM** | Foundational validation |
| Exp 2 | H2 (Metric Symmetry) | **LOW** | Meta-methodological |
| Exp 5 | H5 (Definition Exploitation) | **LOW** | Requires training access |

---

*Experiments designed: 2026-01-03*
*Project: IS_OUGHT*
*Primary hypothesis: H1 (Constitutional vs RLHF signatures)*
