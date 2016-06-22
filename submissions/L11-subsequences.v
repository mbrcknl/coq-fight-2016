(* The subsequence relation is a partial order. *)

Require Import List.
Require Import Omega.
Import ListNotations.

Section subseq_sect.

  Variable A: Type.

  Inductive subseq: list A -> list A -> Prop :=
  | subseq_nil: subseq [] []
  | subseq_add: forall x ys zs, subseq ys zs -> subseq (x::ys) (x::zs)
  | subseq_sub: forall x ys zs, subseq ys zs -> subseq ys (x::zs).

  Hint Constructors subseq.

  Lemma subseq_refl:
    forall xs, subseq xs xs.
  Proof.
  Qed.

  Lemma subseq_len:
    forall xs ys, subseq xs ys -> length xs <= length ys.
  Proof.
  Qed.

  Lemma subseq_trans:
    forall ys zs, subseq ys zs -> forall xs, subseq xs ys -> subseq xs zs.
  Proof.
  Qed.

  (* Hint: use subseq_len to dispose of nonsense cases. *)
  Lemma subseq_antisym:
    forall xs ys, subseq xs ys -> subseq ys xs -> xs = ys.
  Proof.
  Qed.

End subseq_sect.
