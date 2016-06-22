(* Fun with commutative semigroups! *)

Require Import List.
Import ListNotations.

Section commutative_semigroup_fun.

  (* Given an arbitrary type T... *)
  Variable T: Type.

  (* ...with a binary operator... *)
  Variable op: T -> T -> T.

  (* ...which we'll write as `+`... *)
  Infix "+" := op (at level 50, left associativity).

  (* ...and which is associative... *)
  Hypothesis assoc: forall a b c, a + (b + c) = a + b + c.

  (* ...and commutative... *)
  Hypothesis comm: forall a b, a + b = b + a.

  (* ...prove these... *)
  Lemma how_do_you_even_rewrite:
    forall a b c d e, a + b + c + d + e = e + d + c + b + a.
  Proof.
    intros. congruence.
  Qed.

  Lemma fold_left_extract:
    forall r a b, fold_left op r (a + b) = a + fold_left op r b.
  Proof.
    induction r as [|c r IHr]; intros a b.
    - reflexivity.
    - simpl. rewrite <- assoc. rewrite IHr. reflexivity.
  Qed.

  Lemma fold_left_fold_right:
    forall r a, fold_left op r a = fold_right op a r.
  Proof.
    induction r as [|b r IHr]; simpl; intro a.
    - reflexivity.
    - rewrite <- IHr. rewrite comm. apply fold_left_extract.
  Qed.

End commutative_semigroup_fun.
