(* Relationship between combine (zip) and split (unzip). *)

Require Import List.
Import ListNotations.

Lemma split_length:
  forall (A B: Type) (ps: list (A * B)) (xs: list A) (ys: list B),
    split ps = (xs,ys) -> length xs = length ys.
Proof.

Qed.

(* Try copying the proof from split_length, then modify as needed! *)
Lemma split_combine:
  forall (A B: Type) (ps: list (A * B)) (xs: list A) (ys: list B),
    split ps = (xs,ys) -> combine xs ys = ps.
Proof.

Qed.

Lemma combine_split:
  forall (A B: Type) (ps: list (A * B)) (xs: list A) (ys: list B),
    length xs = length ys -> combine xs ys = ps -> split ps = (xs,ys).
Proof.

Qed.
