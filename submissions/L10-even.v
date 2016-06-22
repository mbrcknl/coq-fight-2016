(* Different ways of specifying even numbers. *)

Require Import Arith.

(* If you're still on Coq 8.4, try this instead: *)
(* Import NPeano.Nat. *)
Import Nat.
Import Bool.

Fixpoint evenb (n: nat): bool :=
  match n with
  | O => true
  | S p => negb (evenb p)
  end.

(* Some useful lemmas from the standard library. *)
Check even_succ: forall n, even (S n) = odd n.
Check negb_even: forall n, negb (even n) = odd n.
Check negb_odd: forall n, negb (odd n) = even n.

Lemma evenb_even:
  forall n, evenb n = even n.
Proof.
Qed.
