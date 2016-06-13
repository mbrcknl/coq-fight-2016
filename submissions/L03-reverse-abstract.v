(* Reversing lists, abstractly. *)

Require Import List.
Import ListNotations.

Lemma app_tail_nil:
  forall (T: Type) (xs ys: list T), xs = xs ++ ys -> ys = [].
Proof.
  induction xs; simpl; intros; inversion H; auto.
Qed.

Lemma rev_spec_complete:
  forall (T: Type) (f: list T -> list T),
    (forall x, f [x] = [x]) ->
    (forall xs ys, f (xs ++ ys) = f ys ++ f xs) ->
    (forall xs, f xs = rev xs).
Proof.
  intros T f H J; induction xs.
  - specialize (J [] []); simpl in J.
    apply app_tail_nil in J.
    rewrite J; reflexivity.
  - replace (f (a :: xs)) with (f ([a] ++ xs)) by reflexivity.
    rewrite J. rewrite H. rewrite IHxs. reflexivity.
Qed.
