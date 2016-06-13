(* Different ways of specifying even numbers. *)

Require Import Arith.
Import Nat.
Import Bool.

Fixpoint evenb (n: nat): bool :=
  match n with
  | O => true
  | S p => negb (evenb p)
  end.

Lemma evenb_Even:
  forall n, evenb n = true <-> Even n.
Proof.

Qed.
