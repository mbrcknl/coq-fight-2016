(* Difference of squares. *)

Require Import Omega.
Require Import Arith.
Import Nat.

(* Some useful lemmas from the standard library... *)
Check mul_sub_distr_l: forall n m p, p * (n - m) = p * n - p * m.
Check mul_add_distr_r: forall n m p, (n + m) * p = n * p + m * p.
Check mult_assoc: forall n m p, n * (m * p) = n * m * p.
Check mult_comm: forall n m, n * m = m * n.
Check mul_1_r: forall n, n * 1 = n.

Lemma difference_of_squares:
  forall a b, a * a - b * b = (a + b) * (a - b).
Proof.

Qed.

Lemma difference_of_squares_nested:
  forall a b, a ^ 4 - b ^ 4 = (a * a + b * b) * (a + b) * (a - b).
Proof.

Qed.
