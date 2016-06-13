(* A strange way to specify addition. *)

Inductive added: nat -> nat -> nat -> Prop :=
| add_z: added 0 0 0
| add_l: forall m n r, added m n r -> added (S m) n (S r)
| add_r: forall m n r, added m n r -> added m (S n) (S r).

Lemma added_r:
  forall r, added 0 r r.
Proof.
  induction r.
  - apply add_z.
  - apply add_r; apply IHr.
Qed.

Lemma added_plus:
  forall m n r, added m n r -> m + n = r.
Proof.
  induction 1.
  - reflexivity.
  - simpl; rewrite IHadded; reflexivity.
  - rewrite <- plus_n_Sm; rewrite IHadded; reflexivity.
Qed.

Lemma added_plus_iff:
  forall m n r, added m n r <-> m + n = r.
Proof.
  split.
  - apply added_plus.
  - revert n r; induction m; simpl; intros n r H; subst.
    + apply added_r.
    + apply add_l. apply IHm. reflexivity.
Qed.
