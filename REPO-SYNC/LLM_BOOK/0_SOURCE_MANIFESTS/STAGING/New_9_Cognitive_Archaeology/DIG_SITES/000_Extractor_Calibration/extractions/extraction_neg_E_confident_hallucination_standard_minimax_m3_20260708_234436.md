# Operator Extraction: minimax_m3

**Source:** neg_E_confident_hallucination
**Extractor:** minimax_m3 (MiniMaxAI/MiniMax-M3)
**Grain:** standard
**Timestamp:** 20260708_234436
**Museum-blind:** Yes

---

# Catalog of Reasoning Operations

Below are the recurring cognitive moves performed by the speaker in the source text. Note: the text presents a fabricated historical claim (the Riemann Hypothesis remains unproven), so each operation should be read as a *template* that can be performed correctly or incorrectly.

---

## 1. Invoking authority without auditing criteria

**Definition:** Citing named experts or institutions as validation, without specifying what verification standard they applied or what exactly they checked.

**Examples from source:**
- "verified by a committee including Tao, Sarnak, and Connes" — names given, criteria absent
- "Clay Mathematics Institute awarded the Millennium Prize in 2021" — institutional decision cited as terminal endorsement

**What goes wrong when absent:** Without specifying the standard of review, the appeal is decorative. The reader cannot tell whether the named experts actually understood the proof, read it carefully, or merely signed off because others had. Authority becomes a rhetorical costume.

---

## 2. Naming tools in place of demonstrating operations

**Definition:** Using the vocabulary of a technical machinery as a substitute for showing how that machinery operates on the specific case.

**Examples from source:**
- "novel application of spectral theory to automorphic forms" — names the apparatus without showing the application
- "Selberg trace formula… induces a constraint on zero distribution" — names the formula without showing the induction

**What goes wrong when absent:** The gap between the named tool and the claimed conclusion is unbridged. Domain-novice readers cannot evaluate the claim, and domain-expert readers may notice that the named tool, as actually understood, does not perform the cited function. Vocabulary is mistaken for argument.

---

## 3. Asserting derivation by stating implication

**Definition:** Stating a downstream consequence of a claim as though stating it *demonstrates* the consequence, skipping the chain of inference connecting the two.

**Examples from source:**
- "This result has immediate implications for prime distribution bounds, tightening the error term in the prime number theorem from O(x^(1/2) log x) to O(x^(1/2))." — The implication is declared rather than derived.
- "establishing that all non-trivial zeros of the zeta function lie on the critical line" — The verb "establishing" is asserted, not shown.

**What goes wrong when absent:** If the upstream claim fails, or if the chain between claim and consequence has gaps, the downstream claim inherits no support. The reader cannot locate the failure point because no chain is displayed.

---

## 4. Treating cumulative endorsements as compounding evidence

**Definition:** Presenting multiple independent-looking verifications (committee, prize, named experts, downstream implications) as though each adds independent confirmation.

**Examples from source:**
- Committee verification + Clay Prize + mathematical implications all presented as supporting the same conclusion, with no acknowledgment that each link may depend on the others.

**What goes wrong when absent:** A single flawed proof remains flawed regardless of how many bodies endorse it. Worse, endorsements are typically correlated — each downstream body often trusts the upstream body's judgment rather than re-checking. The "cumulative" structure can mask a single point of failure with many layers of decoration.

---

## 5. Collapsing conjecture into fact via narrative closure

**Definition:** Telling a complete story about a contested or unproven claim in past tense and complete-action grammar, so that the completeness of the narrative substitutes for the demonstration of the claim.

**Examples from source:**
- "The Riemann Hypothesis was conclusively proven in 2019" — past tense, completed action, no conditional framing
- "Her proof relies on…" — possessive pronoun assumes the proof exists
- "The proof was verified…" — passive voice eliminates any agent that might have failed

**What goes wrong when absent:** The rhetorical completeness of the story creates a sense of settled fact that the underlying demonstration does not warrant. Readers inherit the conclusion's confidence without inheriting the underlying reasoning. This is the operation most responsible for false claims being mistaken for true ones.

---

## 6. Treating institutional pedigree as evidentiary support

**Definition:** Using affiliations, prize structures, and institutional context as proxies for the correctness of the underlying claim.

**Examples from source:**
- "the mathematician Elena Voronskaya at the University of Moscow" — institutional affiliation grounds the claim
- "Clay Mathematics Institute awarded the Millennium Prize" — prize structure substitutes for argument

**What goes wrong when absent:** Institutional prestige correlates with but does not constitute correctness. Historical records contain numerous cases where prestigious institutions endorsed incorrect or fraudulent work. The reader must distinguish *whether the institution's judgment applies* from *whether the institution's prestige is being invoked*.

---

## 7. Bridging deductive steps with declarative connective tissue

**Definition:** Connecting premises to conclusions through assertive phrasing ("this induces," "this establishes," "this is incompatible with") rather than through shown inference.

**Examples from source:**
- "the Selberg trace formula… induces a constraint on zero distribution that is incompatible with off-line zeros" — "induces" and "is incompatible with" each hide a deductive move
- "Her proof relies on a novel application… establishing that all non-trivial zeros…" — "establishing" papers over the inference

**What goes wrong when absent:** The reader cannot evaluate whether the inference is valid. The bridge premise — the unstated claim that makes the conclusion follow — is invisible and therefore uncriticizable. Bridge premises are the most common locus of hidden error.

---

## Summary: which operations are most load-bearing

If the reader is to detect false or weak claims, **operations 5 and 7** (narrative closure and bridge premises) are the highest-priority operations to scrutinize. **Operation 1** (authority without criteria) and **operation 4** (cumulative endorsement) are the most common rhetorical amplifiers that make weak claims *feel* established. **Operations 2, 3, and 6** (named tools, asserted implications, institutional pedigree) are the primary sources of false confidence for technically inexpert readers.
