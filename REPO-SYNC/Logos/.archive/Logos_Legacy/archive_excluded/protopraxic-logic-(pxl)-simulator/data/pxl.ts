
export const symbols = [
  { symbol: '⧟', name: 'Identity', description: 'Represents self-coherence and identity.' },
  { symbol: '⇎', name: 'Non-equivalence', description: 'Represents exclusivity and distinction.' },
  { symbol: '⇌', name: 'Interchange', description: 'Represents balance, symmetry, and interchangeability.' },
  { symbol: '⟹', name: 'Implication', description: 'Standard logical implication.' },
  { symbol: '∼', name: 'Negation', description: 'Represents non-coherence or privation.' },
  { symbol: '≀', name: 'Conflation', description: 'Represents misalignment or category error.' },
  { symbol: '⫴', name: 'Dichotomy', description: 'Represents the principle of the excluded middle.' },
  { symbol: '⟼', name: 'Grounded Entailment', description: 'Indicates a necessary grounding relationship.' },
  { symbol: '⩪', name: 'Modal Coherence Equivalence', description: 'Represents parallel coherence across modal domains.' },
  { symbol: '□', name: 'Necessity', description: 'Modal operator for necessity (true in all possible worlds).' },
  { symbol: '◇', name: 'Possibility', description: 'Modal operator for possibility (true in at least one possible world).' },
  { symbol: '𝕆', name: 'Necessary Being', description: 'The triune necessary being in which logic is grounded.' },
  { symbol: '𝕀₁, 𝕀₂, 𝕀₃', name: 'Hypostatic Identities', description: 'The three interdependent identities composing 𝕆.' },
];

export const axioms = [
  { id: 'A1', text: '□(∀x [ x ⧟ x ])', description: 'Law of Identity, grounded in 𝕀₁.' },
  { id: 'A2', text: '□(∀x [ ∼(x ⧟ y ∧ x ⇎ y) ])', description: 'Law of Non-Contradiction, grounded in 𝕀₂.' },
  { id: 'A3', text: '□(∀x [ x ⫴ ∼x ])', description: 'Law of Excluded Middle, grounded in 𝕀₃.' },
  { id: 'A4', text: '□(Each law requires distinct modal instantiation across 𝕀₁, 𝕀₂, 𝕀₃)', description: 'Ensures the distinctness and necessity of the triune structure.' },
  { id: 'A5', text: '□(𝕆 = {𝕀₁, 𝕀₂, 𝕀₃}, co-eternal, co-equal, interdependent)', description: 'Defines the nature of the Necessary Being 𝕆.' },
  { id: 'A6', text: '□(𝕀₁ ⟼ Λ₁ ∧ 𝕀₂ ⟼ Λ₂ ∧ 𝕀₃ ⟼ Λ₃)', description: 'Asserts that each identity grounds a specific logical domain (Λ).' },
  { id: 'A7', text: '□𝕆', description: 'A triune Necessary Being is required for coherence in all possible worlds.' },
];

export const theorems = {
    firstOrder: [
        { id: 'T1', name: 'Law of Triune Coherence', formula: '□(⧟ ∧ ∼ ∧ ⫴) ⩪ coherence ⇌ triune necessity' },
        { id: 'T2', name: 'Identity Exclusivity Principle', formula: '□(x ⧟ x) ∧ □(x ⇎ y) ⇒ ∼(x ⧟ y)' },
        { id: 'T3', name: 'Modal Necessity of Distinction', formula: '□(𝕀₁ ≠ 𝕀₂ ≠ 𝕀₃) ⇌ validity of A1–A3' },
        { id: 'T4', name: 'Coherence Preservation Across Worlds', formula: '□(Λ₁ ∧ Λ₂ ∧ Λ₃) ⇒ □(coherence)' },
        { id: 'T5', name: 'Grounded Interchange Theorem', formula: '□((x ⇌ y) ⟹ x ⧟ y) iff ∃𝕀ₖ grounding interchange' },
        { id: 'T6', name: 'Privation Collapse Principle', formula: '∼(x ⧟ x) ⇒ x = ∅ (privation of identity)' },
    ],
    secondOrder: [
        { id: 'T7', name: 'Identity Fragmentation Cascade', formula: 'If ∼(x ⧟ x), then ∃n fragments s.t. ∑s_i ≠ x' },
        { id: 'T8', name: 'Modal Interchange Instability', formula: 'x ⇌ y but x ≀ y ⇒ ∼□(x ⇌ y)' },
        { id: 'T9', name: 'Category Restriction Schema', formula: 'P(x) holds only within Δ domain ⇒ ¬◇(∀x P(x))' },
        { id: 'T10', name: 'Triune Exhaustion Theorem', formula: 'If x ⧟ x only holds when mapped to 𝕀₁ ∨ 𝕀₂ ∨ 𝕀₃ ⇒ x ∈ 𝕆' },
        { id: 'T11', name: 'Coherence Branching Effect', formula: 'x ∧ y grounded in distinct 𝕀ₖ ⇒ multiple coherence lines emerge' },
        { id: 'T12', name: 'Privative Collapse Under Negation', formula: 'If □(∼P) and P ⇌ coherence, then P = ∅' },
        { id: 'T13', name: 'Necessary Attribute Emergence', formula: 'If □(∃x P(x)) ∧ □(P ⟼ coherence) ⇒ □(𝕆 ⟼ P)' },
        { id: 'T14', name: 'Modal Equivalence Ladders', formula: 'P ⩪ Q and Q ⩪ R ⇒ P ⩪ R (transitive modal entailment)' },
        { id: 'T15', name: 'Coherence Cascade Chain Effects', formula: 'If x ⟼ y and y ⟼ z and ∼(x ⧟ z), then ∼(x ⧟ x)' },
        { id: 'T16', name: 'Anti-Essential Predicative Drift', formula: 'If P(x) ⇌ coherence but P not grounded ⇒ P becomes accidental' },
    ]
};

export const domains = [
    { name: 'Theology', description: 'Modeling coherent trinitarian metaphysics (𝕀₁, 𝕀₂, 𝕀₃) and divine attributes, excluding incoherent models.' },
    { name: 'Metaphysics', description: 'Grounding necessity in interdependent identities and eliminating brute facts via modal entailment.' },
    { name: 'Epistemology', description: 'Formalizing a coherence theory of truth. Knowledge = □(Belief ∧ Grounded ∧ Coherent).' },
    { name: 'Ethics', description: 'Defining Goodness as identity-preserving coherence (⧟) and Evil as its privation (∼Coherence).' },
    { name: 'Aesthetics', description: 'Defining Beauty as modal balance (⇌) and grounding it in the instantiation of triune harmony.' },
    { name: 'Logic Systems', description: 'Completing gaps in classical logic and serving as a coherence-checking overlay for modal domains.' },
];
