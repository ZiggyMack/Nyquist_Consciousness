(* ===================================================================== *)
(*  PXL_Trivial_Model.v — a one-point model of the PXLv3 axiom system    *)
(*                                                                       *)
(*  Purpose: demonstrate two metatheoretic facts about IconAclass's PXL: *)
(*                                                                       *)
(*  1. CONSISTENCY (relative to Coq + classical logic): every PXLv3      *)
(*     axiom, plus trinitarian_decidability from PXL_Internal_LEM, is    *)
(*     provable under the interpretation below. Hence the axiom set      *)
(*     cannot derive False (unless Coq+classic itself is inconsistent).  *)
(*                                                                       *)
(*  2. NON-CATEGORICITY: the interpretation uses a universe with exactly *)
(*     ONE object, in which 𝕆 = 𝕀₁ = 𝕀₂ = 𝕀₃ — "God" and all three      *)
(*     "persons" are the same single point, grounding is mere truth,     *)
(*     and Box p is just p. Since the axioms are satisfied in a world    *)
(*     with no threeness, no divinity, and no modality, they cannot      *)
(*     prove the existence or distinctness of any of those things.       *)
(*     A second model (bool) shows 𝕆 <> 𝕀₁ is *also* consistent: the    *)
(*     axioms settle neither identity nor distinctness of the persons.  *)
(* ===================================================================== *)

Require Import Coq.Logic.Classical.

Module TrivialModel.

(* --- Interpretation of the PXLv3 signature --------------------------- *)

Definition Obj : Type := unit.
Definition Omega : Obj := tt.   (* 𝕆  *)
Definition I1 : Obj := tt.      (* 𝕀₁ *)
Definition I2 : Obj := tt.      (* 𝕀₂ *)
Definition I3 : Obj := tt.      (* 𝕀₃ *)
Definition L1 : Prop := True.   (* Λ₁ *)
Definition L2 : Prop := True.
Definition L3 : Prop := True.

Definition Ident (_ _ : Obj) : Prop := True.
Definition NonEquiv (_ _ : Obj) : Prop := False.
Definition Inter (_ _ : Obj) : Prop := True.

Definition entails (_ : Obj) (P : Prop) : Prop := P.
Definition grounded_in (P : Prop) (_ : Obj) : Prop := P.
Definition incoherent (P : Prop) : Prop := ~ P.
Definition coherence (_ : Obj) : Prop := True.

Definition PImp (p q : Prop) : Prop := p -> q.
Definition MEquiv (p q : Prop) : Prop := p <-> q.
Definition Box (p : Prop) : Prop := p.
Definition Dia (p : Prop) : Prop := p.

(* --- Every PXLv3 axiom, restated verbatim and PROVED ------------------ *)

Lemma ax_K : forall p q : Prop, Box (p -> q) -> Box p -> Box q.
Proof. unfold Box; auto. Qed.

Lemma ax_T : forall p : Prop, Box p -> p.
Proof. unfold Box; auto. Qed.

Lemma ax_4 : forall p : Prop, Box p -> Box (Box p).
Proof. unfold Box; auto. Qed.

Lemma ax_5 : forall p : Prop, Dia p -> Box (Dia p).
Proof. unfold Box, Dia; auto. Qed.

Lemma ax_Nec : forall p : Prop, p -> Box p.
Proof. unfold Box; auto. Qed.

Lemma ax_ident_refl : forall x : Obj, Ident x x.
Proof. unfold Ident; auto. Qed.

Lemma ax_ident_symm : forall x y : Obj, Ident x y -> Ident y x.
Proof. unfold Ident; auto. Qed.

Lemma ax_ident_trans : forall x y z : Obj,
  Ident x y -> Ident y z -> Ident x z.
Proof. unfold Ident; auto. Qed.

Lemma ax_nonequiv_irrefl : forall x : Obj, ~ NonEquiv x x.
Proof. unfold NonEquiv; auto. Qed.

Lemma ax_inter_comm : forall x y : Obj, Inter x y <-> Inter y x.
Proof. unfold Inter; tauto. Qed.

Lemma ax_imp_intro : forall p q : Prop, (p -> q) -> PImp p q.
Proof. unfold PImp; auto. Qed.

Lemma ax_imp_elim : forall p q : Prop, PImp p q -> p -> q.
Proof. unfold PImp; auto. Qed.

Lemma ax_mequiv_intro : forall p q : Prop, (p <-> q) -> MEquiv p q.
Proof. unfold MEquiv; auto. Qed.

Lemma ax_mequiv_elim : forall p q : Prop, MEquiv p q -> p <-> q.
Proof. unfold MEquiv; auto. Qed.

Lemma A1_identity : Box (forall x : Obj, Ident x x).
Proof. unfold Box, Ident; auto. Qed.

Lemma A2_noncontradiction :
  Box (forall x y : Obj, ~ (Ident x y /\ NonEquiv x y)).
Proof. unfold Box, Ident, NonEquiv; tauto. Qed.

Lemma A4_distinct_instantiation :
  Box (Ident I1 I1 /\ Ident I2 I2 /\ Ident I3 I3).
Proof. unfold Box, Ident; tauto. Qed.

Lemma A7_triune_necessity : Box (coherence Omega).
Proof. unfold Box, coherence; auto. Qed.

Lemma modus_groundens : forall (x y : Obj) (P : Prop),
  Box (Ident x y) -> entails x P -> entails y P.
Proof. unfold Box, Ident, entails; auto. Qed.

Lemma triune_dependency_substitution : forall (phi psi : Prop),
  grounded_in phi I1 -> grounded_in psi I2 -> MEquiv phi psi ->
  coherence Omega.
Proof. unfold coherence; auto. Qed.

Lemma privative_collapse : forall (P : Prop),
  ~ (Dia (entails Omega P)) -> incoherent P.
Proof. unfold Dia, entails, incoherent; auto. Qed.

Lemma grounding_yields_entails : forall (x : Obj) (P : Prop),
  grounded_in P x -> entails x P.
Proof. unfold grounded_in, entails; auto. Qed.

Lemma coherence_lifts_entailment : forall (x : Obj) (P : Prop),
  coherence Omega -> entails x P -> entails Omega P.
Proof. unfold entails; auto. Qed.

Lemma entails_global_implies_truth : forall (P : Prop),
  entails Omega P -> P.
Proof. unfold entails; auto. Qed.

(* --- The PXL_Internal_LEM axiom — the ONLY one needing classic -------- *)

Lemma trinitarian_decidability :
  forall (P : Prop), grounded_in P I1 \/ grounded_in (~ P) I2.
Proof. unfold grounded_in. intro P. apply classic. Qed.

(* --- The punchline ----------------------------------------------------- *)

(* Every axiom above holds in a universe with exactly one object,
   in which God and the three persons are literally the same point. *)
Theorem the_model_has_no_trinity :
  Omega = I1 /\ I1 = I2 /\ I2 = I3.
Proof. repeat split; reflexivity. Qed.

End TrivialModel.

(* ===================================================================== *)
(*  Second model: same axioms, but now 𝕆 <> 𝕀₁.                          *)
(*  Together with TrivialModel this shows the axioms settle NOTHING      *)
(*  about the identity structure of the "persons": both a one-point      *)
(*  world and a world where God differs from 𝕀₁ satisfy all of PXL.     *)
(* ===================================================================== *)

Module TwoPointModel.

Definition Obj : Type := bool.
Definition Omega : Obj := true.
Definition I1 : Obj := false.
Definition I2 : Obj := false.
Definition I3 : Obj := false.

Definition Ident (_ _ : Obj) : Prop := True.
Definition NonEquiv (_ _ : Obj) : Prop := False.
Definition entails (_ : Obj) (P : Prop) : Prop := P.
Definition grounded_in (P : Prop) (_ : Obj) : Prop := P.
Definition coherence (_ : Obj) : Prop := True.
Definition Box (p : Prop) : Prop := p.

(* Representative axioms re-proved in this interpretation *)
Lemma A7_triune_necessity : Box (coherence Omega).
Proof. exact I. Qed.

Lemma entails_global_implies_truth : forall P, entails Omega P -> P.
Proof. unfold entails; auto. Qed.

Lemma trinitarian_decidability :
  forall (P : Prop), grounded_in P I1 \/ grounded_in (~ P) I2.
Proof. unfold grounded_in. intro P. apply classic. Qed.

Theorem but_here_God_is_not_I1 : Omega <> I1.
Proof. discriminate. Qed.

End TwoPointModel.
