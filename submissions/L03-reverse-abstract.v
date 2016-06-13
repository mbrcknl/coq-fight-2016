(* Reversing lists, abstractly. *)

Require Import List.
Import ListNotations.

Lemma app_tail_nil:
  forall (T: Type) (xs ys: list T), xs = xs ++ ys -> ys = [].
Proof.

Qed.

Lemma rev_spec_complete:
  forall (T: Type) (f: list T -> list T),
    (forall x, f [x] = [x]) ->
    (forall xs ys, f (xs ++ ys) = f ys ++ f xs) ->
    (forall xs, f xs = rev xs).
Proof.

Qed.
