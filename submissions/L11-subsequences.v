(* The subsequence relation is a partial order. *)

Require Import List.
Require Import Omega.
Import ListNotations.

Inductive subseq {A: Type}: list A -> list A -> Prop :=
| subseq_nil: subseq [] []
| subseq_add: forall x xs ys, subseq xs ys -> subseq (x::xs) (x::ys)
| subseq_sub: forall y xs ys, subseq xs ys -> subseq xs (y::ys).

Lemma subseq_refl:
  forall (A: Type) (xs: list A), subseq xs xs.
Proof.

Qed.

Lemma subseq_len:
  forall (A: Type) (xs ys: list A), subseq xs ys -> length xs <= length ys.
Proof.

Qed.

(* Choose your induction wisely. *)
Lemma subseq_trans:
  forall (A: Type) (xs ys zs: list A), subseq xs ys -> subseq ys zs -> subseq xs zs.
Proof.

Qed.

(* Hint: use subseq_len to dispose of nonsense cases. *)
Lemma subseq_antisym:
  forall (A: Type) (xs ys: list A), subseq xs ys -> subseq ys xs -> xs = ys.
Proof.

Qed.
