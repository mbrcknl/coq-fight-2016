(* Relationship between combine (zip) and split (unzip). *)

Require Import List.
Import ListNotations.

Lemma split_combine:
  forall (A B: Type) (ps: list (A * B)) (xs: list A) (ys: list B),
    split ps = (xs,ys) <-> length xs = length ys /\ combine xs ys = ps.
Proof.
  intros A B ps xs ys; split; revert xs ys; induction ps as [|[x y] ps IHps]; simpl; intros xs ys H.
  - inversion H; auto.
  - destruct (split ps) as [xs' ys'] eqn:P; inversion H as [[J K]];
    destruct (IHps _ _ eq_refl) as [L M]; simpl; rewrite M; auto.
  - destruct H as [J K]; destruct xs; destruct ys; inversion J; inversion K; reflexivity.
  - destruct H as [J K]; destruct xs; destruct ys; simpl in *; try (now inversion K);
    rewrite (IHps xs ys); inversion J; inversion K; auto.
Qed.
