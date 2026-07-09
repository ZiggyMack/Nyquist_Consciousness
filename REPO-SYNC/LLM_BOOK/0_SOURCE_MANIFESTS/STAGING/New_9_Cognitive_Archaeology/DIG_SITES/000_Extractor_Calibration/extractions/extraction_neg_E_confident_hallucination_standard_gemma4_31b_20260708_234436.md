# Operator Extraction: gemma4_31b

**Source:** neg_E_confident_hallucination
**Extractor:** gemma4_31b (google/gemma-4-31B-it)
**Grain:** standard
**Timestamp:** 20260708_234436
**Museum-blind:** Yes

---

### Catalog of Reasoning Operators

**1. Link claim to formal criteria**
*   **Definition:** Converting a high-level hypothesis or general assertion into a specific, testable, and mathematically/logically defined condition.
*   **Examples:** 
    *   Translating the "Riemann Hypothesis" into the requirement that "all non-trivial zeros... lie on the critical line Re(s) = 1/2."
*   **What goes wrong when absent:** The claim remains a vague abstraction, making it impossible to determine exactly what constitutes a "win" or a successful proof.

**2. Isolate the enabling mechanism**
*   **Definition:** Identifying the specific theoretical tool, novel application, or "key insight" that allows a problem to be solved where previous attempts failed.
*   **Examples:** 
    *   Identifying the "novel application of spectral theory to automorphic forms."
    *   Identifying the use of the "Selberg trace formula" to induce a constraint.
*   **What goes wrong when absent:** The conclusion appears as a "black box" or a miracle; the logical path from the problem to the solution is obscured.

**3. Eliminate via logical incompatibility**
*   **Definition:** Establishing a set of constraints that make a contradictory state impossible, thereby forcing the validity of the target conclusion.
*   **Examples:** 
    *   Using a constraint on zero distribution that is "incompatible with off-line zeros."
*   **What goes wrong when absent:** The argument fails to exclude alternative possibilities, leaving the conclusion as one of many potential options rather than a necessity.

**4. Validate via authoritative consensus**
*   **Definition:** Establishing the truth-value of a complex claim by appealing to the verification process of recognized experts and institutional rewards.
*   **Examples:** 
    *   Referencing verification by a committee including "Tao, Sarnak, and Connes."
    *   Citing the award of the "Millennium Prize" by the Clay Mathematics Institute.
*   **What goes wrong when absent:** The claim lacks social and professional trust, remaining a solitary assertion rather than an accepted fact.

**5. Derive downstream implications**
*   **Definition:** Projecting the consequences of a fundamental theoretical breakthrough onto related applied fields or secondary theorems.
*   **Examples:** 
    *   Connecting the proof to "immediate implications for prime distribution bounds."
    *   Linking the result to the "prime number theorem."
*   **What goes wrong when absent:** The discovery is viewed as an isolated curiosity; its utility and broader significance are not realized.

**6. Quantify precision improvement**
*   **Definition:** Explicitly defining the transition from a looser approximation (error bound) to a tighter, more accurate one.
*   **Examples:** 
    *   Defining the shift in the error term "from $O(x^{1/2} \log x)$ to $O(x^{1/2})$."
*   **What goes wrong when absent:** The improvement is described only qualitatively (e.g., "it got better"), failing to communicate the actual magnitude of the gain in accuracy.
