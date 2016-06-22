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
    induction xs.
    - apply subseq_nil.
    - apply subseq_add; apply IHxs.
  Qed.

  Lemma subseq_len:
    forall xs ys, subseq xs ys -> length xs <= length ys.
  Proof.
    induction 1; simpl; omega.
  Qed.

  Lemma subseq_trans:
    forall ys zs, subseq ys zs -> forall xs, subseq xs ys -> subseq xs zs.
  Proof.
    induction 1 as [|x' xs' ys' K IH|x' xs' ys' K IH]; intros xs H.
    - apply H.
    - inversion H as [|x'' xs'' ys'' M|x'' xs'' ys'' M]; subst;
        [apply subseq_add | apply subseq_sub]; apply IH; apply M.
    - apply subseq_sub. apply IH. apply H.
  Qed.

  (* Hint: use subseq_len to dispose of nonsense cases. *)
  Lemma subseq_antisym:
    forall xs ys, subseq xs ys -> subseq ys xs -> xs = ys.
  Proof.
    induction 1; intro J.
    - reflexivity.
    - inversion J as [|x' xs' ys' L|x' xs' ys' L]; subst.
      + apply f_equal. apply IHsubseq. apply L.
      + apply subseq_len in H. apply subseq_len in L. simpl in L. omega.
    - apply subseq_len in H. apply subseq_len in J. simpl in J. omega.
  Qed.

End subseq_sect.
