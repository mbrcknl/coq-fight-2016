(* Relationship between combine (zip) and split (unzip). *)

Require Import List.
Import ListNotations.

Lemma split_length:
  forall (A B: Type) (ps: list (A * B)) (xs: list A) (ys: list B),
    split ps = (xs,ys) -> length xs = length ys.
Proof.
  induction ps; simpl; intros xs ys H.
  - inversion H; auto.
  - destruct a. destruct (split ps) eqn:T; simpl in *.
    destruct xs; destruct ys; inversion H; subst.
    simpl; apply f_equal; auto.
Qed.

(* Try copying the proof from split_length, then modify as needed! *)
Lemma split_combine:
  forall (A B: Type) (ps: list (A * B)) (xs: list A) (ys: list B),
    split ps = (xs,ys) -> combine xs ys = ps.
Proof.
  induction ps; simpl; intros xs ys H.
  - inversion H; auto.
  - destruct a. destruct (split ps) eqn:T; simpl in *.
    destruct xs; destruct ys; inversion H; subst.
    simpl; apply f_equal; auto.
Qed.

Lemma combine_split:
  forall (A B: Type) (ps: list (A * B)) (xs: list A) (ys: list B),
    length xs = length ys -> combine xs ys = ps -> split ps = (xs,ys).
Proof.
  induction ps; simpl; intros xs ys H J.
  - destruct xs; destruct ys; simpl in *; inversion H; inversion J; auto.
  - destruct a. destruct (split ps) eqn:T.
    destruct xs; destruct ys; simpl in *; inversion H; inversion J; subst.
    specialize (IHps _ _ H1 eq_refl). inversion IHps; auto.
Qed.
