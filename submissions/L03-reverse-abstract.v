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
    induction xs; simpl; intros ys H; inversion H; auto.
  Qed.

  Hypothesis app_rev: forall xs ys, f (xs ++ ys) = f ys ++ f xs.

  (* Hint: `assert` something which allows you to
     use a specialisation of app_rev, and then
     use app_tail_nil. *)
  Lemma nil_id: f [] = [].
  Proof.
    specialize (app_rev [] []); simpl in *.
    eapply app_tail_nil; eauto.
  Qed.

  Hypothesis single_id: forall x, f [x] = [x].

  Lemma rev_spec_complete:
    forall xs, f xs = rev xs.
  Proof.
    induction xs; simpl.
    - apply nil_id.
    - replace (a::xs) with ([a] ++ xs) by auto.
      rewrite app_rev. rewrite single_id. rewrite IHxs. auto.
  Qed.

End rev_abstract.
