(* Difference of squares. *)

Require Import Omega.
Require Import Arith.

(* If you're still on 8.4 (laggard!), try this instead: *)
(* Import NPeano.Nat. *)
Import Nat.

(* Some useful lemmas from the standard library... *)
Check mul_sub_distr_l: forall n m p, p * (n - m) = p * n - p * m.
Check mul_add_distr_r: forall n m p, (n + m) * p = n * p + m * p.
Check mult_assoc: forall n m p, n * (m * p) = n * m * p.
Check mult_comm: forall n m, n * m = m * n.
Check mul_1_r: forall n, n * 1 = n.

(* None of these lemmas require induction. Just use the library lemmas above. *)
Lemma squared_squared:
  forall x, x ^ 4 = (x * x) * (x * x).
Proof.

Qed.

(* Expand the right hand side first. *)
Lemma difference_of_squares:
  forall a b, a * a - b * b = (a + b) * (a - b).
Proof.

Qed.

(* Use both lemmas you just proved. *)
Lemma difference_of_squares_nested:
  forall a b, a ^ 4 - b ^ 4 = (a * a + b * b) * (a + b) * (a - b).
Proof.

Qed.
