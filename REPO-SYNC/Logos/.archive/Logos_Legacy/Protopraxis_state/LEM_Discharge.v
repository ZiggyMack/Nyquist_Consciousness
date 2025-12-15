(* LOGOS Agent LEM discharge proof generated at 2025-11-12T16:59:38.968327Z by LOGOS-AGENT-OMEGA *)

From Coq Require Import Logic.Classical.

Theorem law_of_excluded_middle_resolved : forall P : Prop, P \/ ~ P.
Proof.
  exact classic.
Qed.
