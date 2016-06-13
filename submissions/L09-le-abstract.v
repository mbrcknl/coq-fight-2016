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

  (* Show that le' is not so arbitrary after all... *)
  Lemma le'_S_ind:
    forall m n, le' m n -> le' m (S n).
  Proof.

  Qed.

  Lemma le_le':
    forall m n, m <= n -> le' m n.
  Proof.

  Qed.

  Lemma le'_0_r:
    forall n, le' n 0 -> n = 0.
  Proof.

  Qed.

  (* Hint: start with `destruct (le_ge_dec something something)`. *)
  Lemma le'_SS:
    forall m n, le' (S m) (S n) -> le' m n.
  Proof.

  Qed.

  Lemma le_le'_iff:
    forall m n, m <= n <-> le' m n.
  Proof.

  Qed.
  
End le_sect.
