(* Difference of squares. *)

Require Import Omega.
Require Import Arith.
Import Nat.

(* Some useful lemmas from the standard library... *)
Check mul_sub_distr_l: forall n m p, p * (n - m) = p * n - p * m.
Check mul_add_distr_r: forall n m p, (n + m) * p = n * p + m * p.
Check mult_assoc: forall n m p, n * (m * p) = n * m * p.
Check mult_comm: forall n m, n * m = m * n.
Check square_le_mono: forall n m, n <= m <-> n * n <= m * m.
Check mul_1_r: forall n, n * 1 = n.

Lemma difference_of_squares:
  forall a b, b <= a -> a * a - b * b = (a + b) * (a - b).
Proof.
  intros a b H.
  rewrite mul_sub_distr_l.
  repeat (rewrite mul_add_distr_r).
  rewrite (mult_comm a b).
  omega.
Qed.

Lemma difference_of_squares_nested:
  forall a b, b <= a -> a ^ 4 - b ^ 4 = (a * a + b * b) * (a + b) * (a - b).
Proof.
  intros a b H.
  assert (forall x, x ^ 4 = x * x * (x * x)) as J.
  simpl; intros; rewrite mul_1_r; repeat (rewrite mult_assoc); reflexivity.
  rewrite (J a); rewrite (J b); clear J.
  rewrite (difference_of_squares (a * a)).
  rewrite (difference_of_squares a); auto.
  rewrite mult_assoc; reflexivity.
  destruct (square_le_mono b a); auto.
Qed.
