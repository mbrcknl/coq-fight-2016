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
  induction xs.
  - apply subseq_nil.
  - apply subseq_add; apply IHxs.
Qed.

Lemma subseq_len:
  forall (A: Type) (xs ys: list A), subseq xs ys -> length xs <= length ys.
Proof.
  induction 1; simpl; omega.
Qed.

(* Choose your induction wisely. *)
Lemma subseq_trans:
  forall (A: Type) (xs ys zs: list A), subseq xs ys -> subseq ys zs -> subseq xs zs.
Proof.
  intros A xs ys zs H J; revert xs H;
    induction J as [|x' xs' ys' K IH|x' xs' ys' K IH]; intros xs H.
  - apply H.
  - inversion H as [|x'' xs'' ys'' M|x'' xs'' ys'' M]; subst;
      [apply subseq_add | apply subseq_sub]; apply IH; apply M.
  - apply subseq_sub. apply IH. apply H.
Qed.

(* Hint: use subseq_len to dispose of nonsense cases. *)
Lemma subseq_antisym:
  forall (A: Type) (xs ys: list A), subseq xs ys -> subseq ys xs -> xs = ys.
Proof.
  intros A xs ys H; induction H; intro J.
  - reflexivity.
  - inversion J as [|x' xs' ys' L|x' xs' ys' L]; subst.
    + apply f_equal. apply IHsubseq. apply L.
    + apply subseq_len in H. apply subseq_len in L. simpl in L. Omega.omega.
  - apply subseq_len in H. apply subseq_len in J. simpl in J. Omega.omega.
Qed.
