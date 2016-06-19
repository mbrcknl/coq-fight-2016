(* Reversing lists, abstractly. *)

Require Import List.
Import ListNotations.

Section rev_abstract.

  Variables
    (T: Type)
    (f: list T -> list T).

  Lemma app_tail_nil:
    forall (xs ys: list T), xs = xs ++ ys -> ys = [].
  Proof.

  Qed.

  Hypothesis app_rev: forall xs ys, f (xs ++ ys) = f ys ++ f xs.

  (* Hint: `assert` something which allows you to
     use a specialisation of app_rev, and then
     use app_tail_nil. *)
  Lemma nil_id: f [] = [].
  Proof.

  Qed.

  Hypothesis single_id: forall x, f [x] = [x].

  Lemma rev_spec_complete:
    forall xs, f xs = rev xs.
  Proof.

  Qed.

End rev_abstract.
