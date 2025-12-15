(** Minimal kernel surface for the Protopraxic Logic (PXL) axioms. *)

Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.

(* --- Domain primitives --------------------------------------------------- *)

Parameter Obj : Type.
Parameters 𝕆 𝕀₁ 𝕀₂ 𝕀₃ : Obj.
Parameters Λ₁ Λ₂ Λ₃ : Prop.

Parameter Ident : Obj -> Obj -> Prop.
Parameter NonEquiv : Obj -> Obj -> Prop.
Parameter Inter : Obj -> Obj -> Prop.

Parameter entails : Obj -> Prop -> Prop.
Parameter grounded_in : Prop -> Obj -> Prop.
Parameter incoherent : Prop -> Prop.
Parameter coherence : Obj -> Prop.

Parameter PImp : Prop -> Prop -> Prop.
Parameter MEquiv : Prop -> Prop -> Prop.
Parameter Box : Prop -> Prop.
Parameter Dia : Prop -> Prop.

Infix " ⧟ " := Ident (at level 50).
Infix " ⇎ " := NonEquiv (at level 50).
Infix " ⇌ " := Inter (at level 50).
Infix " ⟹ " := PImp (at level 90, right associativity).
Infix " ⩪ " := MEquiv (at level 80).
Notation "□ p" := (Box p) (at level 75).
Notation "◇ p" := (Dia p) (at level 75).
Notation "∼ p" := (~ p) (at level 75).

(* --- Modal backbone ------------------------------------------------------ *)

Axiom ax_K  : forall p q : Prop, □ (p -> q) -> □ p -> □ q.
Axiom ax_T  : forall p : Prop, □ p -> p.
Axiom ax_4  : forall p : Prop, □ p -> □ (□ p).
Axiom ax_5  : forall p : Prop, ◇ p -> □ (◇ p).
Axiom ax_Nec : forall p : Prop, p -> □ p.

(* --- Structural laws ----------------------------------------------------- *)

Axiom ax_ident_refl  : forall x : Obj, x ⧟ x.
Axiom ax_ident_symm  : forall x y : Obj, x ⧟ y -> y ⧟ x.
Axiom ax_ident_trans : forall x y z : Obj, x ⧟ y -> y ⧟ z -> x ⧟ z.

Axiom ax_nonequiv_irrefl : forall x : Obj, ~ (x ⇎ x).
Axiom ax_inter_comm      : forall x y : Obj, x ⇌ y <-> y ⇌ x.

Axiom ax_imp_intro  : forall p q : Prop, (p -> q) -> p ⟹ q.
Axiom ax_imp_elim   : forall p q : Prop, p ⟹ q -> p -> q.
Axiom ax_mequiv_intro : forall p q : Prop, (p <-> q) -> p ⩪ q.
Axiom ax_mequiv_elim  : forall p q : Prop, p ⩪ q -> p <-> q.

Axiom A1_identity : □ (forall x : Obj, x ⧟ x).
Axiom A2_noncontradiction : □ (forall x y : Obj, ~ (x ⧟ y /\ x ⇎ y)).
Axiom A4_distinct_instantiation : □ (Ident 𝕀₁ 𝕀₁ /\ Ident 𝕀₂ 𝕀₂ /\ Ident 𝕀₃ 𝕀₃).
Axiom A7_triune_necessity : □ (coherence 𝕆).

(* --- Bridging principles -------------------------------------------------- *)

Axiom modus_groundens :
  forall (x y : Obj) (P : Prop), □ (x ⧟ y) -> entails x P -> entails y P.

Axiom triune_dependency_substitution :
  forall (φ ψ : Prop), grounded_in φ 𝕀₁ -> grounded_in ψ 𝕀₂ -> φ ⩪ ψ -> coherence 𝕆.

Axiom privative_collapse :
  forall (P : Prop), ~ (◇ (entails 𝕆 P)) -> incoherent P.

Axiom grounding_yields_entails :
  forall (x : Obj) (P : Prop), grounded_in P x -> entails x P.

Axiom coherence_lifts_entailment :
  forall (x : Obj) (P : Prop), coherence 𝕆 -> entails x P -> entails 𝕆 P.

Axiom entails_global_implies_truth :
  forall (P : Prop), entails 𝕆 P -> P.
