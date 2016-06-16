(* A strange way to specify addition. *)

Require Import Arith.
Import Nat.
Require Import Omega.

Inductive added: nat -> nat -> nat -> Prop :=
| add_z: added 0 0 0
| add_l: forall m n r, added m n r -> added (S m) n (S r)
| add_r: forall m n r, added m n r -> added m (S n) (S r).

Hint Resolve add_z add_l add_r.

Lemma added_r:
  forall r, added 0 r r.
Proof.
  induction r; eauto.
Qed.

Hint Resolve added_r.

Lemma added_plus:
  forall m n r, added m n r -> m + n = r.
Proof.
  induction 1; omega.
Qed.

Lemma added_plus_iff:
  forall m n r, added m n r <-> m + n = r.
Proof.
  split.
  - apply added_plus.
  - revert n r; induction m; simpl; intros n r H; subst; eauto.
Qed.