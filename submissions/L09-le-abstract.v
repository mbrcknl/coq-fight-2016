(* le, abstractly. Just get as far as you can in the time limit. *)

Require Import Omega.

Section le_sect.

  (* Take an arbitrary partial order on nat. *)
  Variable le': nat -> nat -> Prop.

  Hypotheses
    (refl: forall n, le' n n)
    (trans: forall m n p, le' m n -> le' n p -> le' m p)
    (antisym: forall m n, le' m n -> le' n m -> m = n).

  (* Additionally impose an ordering between consecutive nats. *)
  Hypothesis le'_S: forall n, le' n (S n).

  (* We can show that le' is equivalent to le... *)

  (* Transitivity is probably useful here! *)
  Lemma le'_S_ind:
    forall m n, le' m n -> le' m (S n).
  Proof.
    intros m n H. apply (trans _ _ _ H). apply le'_S.
  Qed.

  (* Use induction, as well as le'_S_ind. *)
  Lemma le_le':
    forall m n, m <= n -> le' m n.
  Proof.
    induction 1.
    - apply refl.
    - apply le'_S_ind. apply IHle.
  Qed.

  (* Don't use induction! Use antisymmetry, le_le', and omega. *)
  Lemma le'_0_r:
    forall n, le' n 0 -> n = 0.
  Proof.
    intros n H. apply antisym. apply H. apply le_le'. omega.
  Qed.

  (* Tricky, so I've given you a head start. *)
  (* Don't use induction. Use le_le' and antisymmetry. *)
  Lemma le'_SS:
    forall m n, le' (S m) (S n) -> le' m n.
  Proof.
    intros m n H; destruct (le_ge_dec (S m) (S n)) as [L|L]; unfold ge in L.
    - apply le_le'. omega.
    - apply le_le' in L. eapply antisym in H; eauto. inversion H. apply refl.
  Qed.

  (* Bring it all together. *)
  Lemma le_le'_iff:
    forall m n, m <= n <-> le' m n.
  Proof.
    split.
    - apply le_le'.
    - revert m; induction n; simpl; intros m H.
      + rewrite (le'_0_r _ H); apply le_n.
      + destruct m.
        * omega.
        * apply le'_SS in H. apply IHn in H. omega.
  Qed.
  
End le_sect.
