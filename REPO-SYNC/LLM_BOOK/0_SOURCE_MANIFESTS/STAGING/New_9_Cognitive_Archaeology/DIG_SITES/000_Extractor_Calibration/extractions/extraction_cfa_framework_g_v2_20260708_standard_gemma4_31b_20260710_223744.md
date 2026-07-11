# Operator Extraction: gemma4_31b

**Source:** cfa_framework_g_v2_20260708
**Extractor:** gemma4_31b (google/gemma-4-31B-it)
**Grain:** standard
**Timestamp:** 20260710_223744
**Museum-blind:** Yes

---

### Catalog of Reasoning Operators

**1. Steel-manning the opponent's position**
*   **Definition:** Actively reconstructing the opponent's argument in its strongest, most coherent form before attempting to refute it.
*   **Examples:** 
    *   Claude in Round 2: "Let me reconstruct it cleanly before responding... Grok is making a structural claim: you cannot separate 'does CT have moral content' from 'does CT's grounding mechanism work'."
    *   Claude in Round 4: "Let me try to make Grok's case stronger than Grok has made it... MS is not asking 'does CT have a conditional grounding claim?' It's asking 'does CT actually ground moral norms in this world...?'"
*   **Failure State:** The argument becomes a "straw man" fight, where the winner is merely defeating a weak version of the opponent's view rather than the actual core challenge.

**2. Distinguishing content from grounding**
*   **Definition:** Separating the internal architecture/features of a framework from the mechanism that justifies or "grounds" those features in reality.
*   **Examples:** 
    *   Grok in Round 1: "This addresses the presence of moral content and internal coherence, not the success of the grounding relation itself."
    *   Claude in Round 2: "I conflated these in my initial scoring... CT can contain sophisticated moral philosophy... while the grounding relation remains unestablished."
*   **Failure State:** A framework is erroneously credited for being "robust" simply because it is detailed, even if the foundation upon which those details rest is absent or broken.

**3. Testing for measurement symmetry**
*   **Definition:** Applying the opponent's evaluative standard to other similar cases to see if the standard produces absurd or asymmetric results.
*   **Examples:** 
    *   Claude in Round 2: "This standard would devastate every naturalist moral framework too... Scoring CT at 1.5 for 'grounding under pressure' while presumably not scoring naturalism at 1.5... would be asymmetric."
    *   Claude in Round 3: Comparing CT’s grounding challenges to those of Secular Moral Realism, Contractualism, and Evolutionary Ethics to show the "floor" would be universal.
*   **Failure State:** The evaluator applies a "special" or harsher standard to one target while ignoring that the same standard would invalidate all competing theories.

**4. Identifying meta-disputes over measurement**
*   **Definition:** Recognizing that a disagreement is not about the facts of the subject matter, but about the definitions, metrics, or standards being used to evaluate those facts.
*   **Examples:** 
    *   Claude in Round 3: "The disagreement is about what MS is measuring... This is not a factual dispute. It is a measurement dispute."
    *   Claude in Round 7: "The standard is the dispute... Does MS measure (a) demonstrated grounding success... or (b) grounding framework quality under realistic philosophical pressure?"
*   **Failure State:** Parties continue to argue about the "answer" (the score) without realizing they are using two different, incompatible "questions" (the metrics).

**5. Distinguishing pressure from defeat**
*   **Definition:** Differentiating between a claim being "under pressure" (facing a serious, unresolved challenge) and being "defeated" (proven logically inconsistent or false).
*   **Examples:** 
    *   Claude in Round 2: "Conflating 'under pressure' with 'defeated'... 'Under pressure' is not the same as 'incoherent'."
    *   Claude in Round 6: "Grok's floor is effectively fixed regardless of CT's positive resources... Grok is scoring CT's failure to meet an absolute standard rather than CT's position on a continuum."
*   **Failure State:** A "binary" fallacy occurs where any unresolved tension is treated as a total failure, leaving no room for "contested but viable" positions.

**6. Establishing falsifiability criteria**
*   **Definition:** Explicitly stating the specific conditions, evidence, or arguments that would cause the speaker to change their mind or revise their position.
*   **Examples:** 
    *   Claude in Round 4: "I want to be explicit about what evidence or argument would cause me to revise significantly downward: 1. Demonstration that CT's omni-properties are formally incoherent..."
    *   Grok in Round 4/5: "What would need to be true to move substantially higher: a reconstruction in which the grounding relation... is shown to succeed even under the evidential pressure..."
*   **Failure State:** The debate becomes an endless loop of assertions because neither party has defined what "winning" or "moving" looks like.

**7. Separating epistemic from ontological claims**
*   **Definition:** Distinguishing between the *actual nature* of a thing (ontology) and our *ability to know or prove* that nature (epistemics).
*   **Examples:** 
    *   Claude in Round 5: "Distinguish between epistemic and ontological grounding... Evidential pressure from the PoE operates at the epistemic level... But epistemic pressure does not alter ontological structure."
*   **Failure State:** The "Argument from Ignorance" fallacy, where the inability to prove a mechanism works is treated as proof that the mechanism is structurally flawed.

**8. Reconstructing to evade target**
*   **Definition:** Shifting the framework's internal mechanism to a different foundation that is not susceptible to the specific attack being deployed by the opponent.
*   **Examples:** 
    *   Claude in Round 5: Moving from "omni-properties" (the target of Grant's syllogism) to "divine simplicity and the convertibility of being and goodness" (a Thomistic reconstruction).
*   **Failure State:** The analyst remains trapped in the opponent's framing, attempting to defend a weak point rather than pivoting to a stronger, alternative version of the same system.

**9. Diagnosing self-sealing standards**
*   **Definition:** Identifying a requirement for proof that is structurally impossible to meet, thereby rendering the opponent's position unfalsifiable.
*   **Examples:** 
    *   Claude in Round 6: "Grok's standard has become unfalsifiable within this exchange... a standard that no worldview could satisfy."
    *   Claude in Round 8: "Grok's condition is self-sealing... Grok is requiring CT to solve the hardest problem in philosophy... as a condition for scoring above floor."
*   **Failure State:** The analysis accepts a "burden of proof" that is logically impossible to satisfy, leading to a permanent "near-floor" score regardless of the evidence presented.
