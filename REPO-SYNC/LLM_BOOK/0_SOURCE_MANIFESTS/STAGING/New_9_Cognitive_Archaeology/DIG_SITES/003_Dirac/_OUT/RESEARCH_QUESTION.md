# Research Question: Dirac's Cognitive Architecture

## Core Hypothesis

Dirac's discovery process represents a **qualitatively different cognitive architecture** from Barandes' — forward-generative and aesthetic rather than backward-reading and philosophical. If the Extraction Protocol (v1.2) can characterize both architectures, it has genuine discriminative power. If it struggles with Dirac, that struggle is informative: it reveals the protocol's domain of applicability.

## Specific Questions for NotebookLM

1. **Process, not results**
   - How does Dirac describe his own methodology?
   - What does "playing with equations" mean concretely — what operations is he performing?
   - Does he ever "read backward" from results to structure, or does he always move forward?

2. **Beauty as epistemic criterion**
   - When Dirac says "a beautiful equation is more likely to be correct," what cognitive operation is he performing?
   - Is beauty a SELECTION criterion (choosing between candidates) or a GENERATIVE principle (producing candidates)?
   - Does mathematical beauty function as an invariant — does it survive representation change?

3. **Relationship to Noether**
   - Does Dirac use invariance-seeking? If so, how does his version differ from Noether's/Barandes'?
   - Does the Noetherian Discovery Algorithm (locate false invariants → isolate true invariants → read backward → cross-domain shift → stress-test) describe any part of Dirac's process?
   - What does Dirac do INSTEAD of backward-reading, if anything?

4. **Operator recovery targets**
   - What cognitive moves does Dirac perform REPEATEDLY across different discoveries?
   - Do any of these match existing Museum operators (OP-001 through OP-015)?
   - What genuinely new operators does Dirac exhibit that Barandes does not?

5. **Negative control function**
   - Where does the structured extraction protocol STRUGGLE with Dirac's intuitive process?
   - Are there aspects of Dirac's thinking that resist operator decomposition?
   - What would it mean if the protocol fails to extract structured operators from Dirac?

---

## Source Material Requirements

| Type | Priority | What to Look For |
|---|---|---|
| Long interviews | HIGH | Dirac describing how he thinks, not what he discovered |
| Lectures on methodology | HIGH | "The Evolution of the Physicist's Picture of Nature" (1963) |
| Biographical material | MEDIUM | Farmelo's "The Strangest Man" — chapters on process |
| "Principles of QM" preface | MEDIUM | Dirac's own methodological statements |
| Letters/correspondence | LOW | Process-revealing exchanges with Bohr, Heisenberg, etc. |

---

*Created: 2026-07-10*
*Extraction Protocol: v1.2 (Barandes Protocol + Noether Lens + Q50 mandatory)*

---

## Additional Question Clusters (2026-07-15) — with Cross-Project Ties

> Prompted by the loaded corpus. The point isn't only to characterize Dirac — it's to make **Dirac earn his keep against the project's standing questions** (`../../../RESEARCH_QUESTIONS.md`, Q1–Q16), the Museum operators (OP-001…OP-015), the CFA manifold verdict, and the cross-arm EOS↔CFA loop. Each cluster names its tie.

### Cluster 6 — Beauty's Two Faces (a within-thinker positive/negative control)

Magnetic monopoles (Lecture 3, beauty-driven **success**) vs "Does G vary" / Large Numbers (Lecture 4, beauty-driven **failure**). Does the *same* aesthetic operator generate both? If so, **beauty is a generator, not a truth-tracker** — so what is the missing **selection** operator that distinguishes the monopole from varying-G?

- **Tie → methodology:** this is Dirac's own built-in control, exactly the shape of neg_H (H-baseline) and the CFA noise-floor check (**OP-006, Under-Determination Detection**). Run the *same* extraction on Lecture 3 vs Lecture 4; if the operator profile is identical across a success and a failure, beauty is not the discriminator.
- **Tie → manifold verdict:** parallels the CFA result — a signal that *feels* like structure (aesthetic rightness) but, floored against its failure case, may be additive/necessary-but-not-sufficient.

### Cluster 7 — The "Nerfed Equation" thread

Hestenes' geometric-algebra rewrite (the imaginary unit *i* hides a rotation generator), the Dirac-sea → QFT replacement ("lost the physical picture"), Dirac's aether dissent. Is **aesthetic dissatisfaction with a working formalism** a generative discovery operator or a failure mode?

- **Tie → OP-001 (Representation ≠ Ontology):** Dirac's claim that QFT's representation *lost structure* IS a representation-invariance claim. Testable against the project's embedding-invariance machinery: is the "lost structure" real (survives representation change) or representational (an artifact of the formalism he preferred)?
- **Tie → "don't privilege nodes":** if the structure lives *between* representations (Dirac↔Hestenes↔QFT), that's the same cross-project principle (Barandes, Curt, CFA, ARMADA, EOS).

### Cluster 8 — Renormalization rejection

Dirac rejected renormalization as "ugly" despite QED's empirical success — aesthetic judgment overriding evidence.

- **Tie → OP-006 + extractor susceptibility:** was Dirac *detecting under-determination* (a legitimate null-hypothesis move the field skipped) or *over-reaching* (aesthetic attachment)? This is the human analog of the FIELD_MANUAL "extractors optimize for structure, miss the null" point. Same operator, opposite verdicts depending on outcome — a Failure-Atlas entry.
- **Tie → cross-arm CFA:** would CFA's adversarial audit score Dirac's rejection as a defensible dissent or a CRUX (operator failure in the wild)?

### Cluster 9 — Formalism-as-oracle (the forward-generative move)

"Playing with equations" before knowing the target — manipulating the formalism to see what it *suggests*.

- **Tie → Discovery Simplex (Generation corner):** this is the dig site's reason to exist. If it's real and distinct, Architecture B is confirmed.
- **Tie → Barandes / OP-011 (Subtractive Discovery) + Test B (Q3, load-bearing):** Dirac's *forward* ordering vs Barandes' *backward-reading* ordering is a direct test that **ordering discriminates architectures** — the H-baseline's escape route. Run `sequence_analysis.py` on Dirac vs Barandes operator sequences.

### Cluster 10 — Structural-analogy transport (commutators ↔ Poisson brackets)

Dirac noticing the structural isomorphism between quantum commutators and classical Poisson brackets.

- **Tie → Museum cross-reference:** does this match OP-001, or is it a new cross-domain mapping operator? Register accordingly.
- **Tie → Q11 (cross-domain survival) + Cross-Thinker Comparison prompt:** if the same transport move appears in non-physics thinkers, it's a primitive, not a physics technique.

---

## Cross-Project Ties (map Dirac → the standing agenda)

| Dirac finding | Ties to | Test it generates |
| --- | --- | --- |
| Operator profile (from extraction) | **Cross-arm EOS↔CFA loop** (FIELD_MANUAL) | Stage Dirac's worldview (aesthetic realism, fallibilism, "God is a mathematician") as a future CFA framework; predict its CFA scores from the operator profile |
| Worldview → CFA additive profile | **Manifold verdict** (CFA scores are additive framework-properties, interaction 0.8–5.7%) | Does an EOS operator-profile predict a framework's *additive* CFA fingerprint? Dirac is a clean out-of-sample test |
| Forward vs backward ordering | **Q3 / Test B** (ordering as the fossil — load-bearing) | Dirac (forward-generative) vs Barandes (backward-reading): does sequence statistics discriminate the two architectures? |
| Aesthetic operator novelty | **Q15** (finite grammar of operators) | Does an aesthetic physicist *expand* the grammar or reduce to known operators? Either answer is evidence |
| Protocol struggle on intuition | **Negative-control value** (the dig site's design goal) | Where the v1.2 protocol *fails* to decompose Dirac's intuition marks the protocol's domain boundary — a finding, not a defeat |

*Additional clusters + cross-project ties added 2026-07-15 (Repo Opus). Sharpest empirical hook: Cluster 6 (Beauty's Two Faces) — Lectures 3 & 4 exist locally even though NotebookLM failed to ingest them.*
