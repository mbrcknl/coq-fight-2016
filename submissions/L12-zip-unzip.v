(* Relationship between combine (zip) and split (unzip). *)

Require Import List.
Import ListNotations.

Lemma split_combine:
  forall (A B: Type) (ps: list (A * B)) (xs: list A) (ys: list B),
    split ps = (xs,ys) <-> length xs = length ys /\ combine xs ys = ps.
Proof.

Qed.
