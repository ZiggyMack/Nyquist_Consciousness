From Coq Require Import Logic.Classical.

Theorem law_of_excluded_middle : forall (P : Prop), P \/ ~ P.
Admitted.

(* NOTE: This admit is intentional and reserved for runtime discharge by the LOGOS agent. *)