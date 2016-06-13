(* An alternate list induction principle. *)

Require Import List.
Import ListNotations.

Lemma list_ind_alt:
  forall (A: Type) (P: list A -> Prop),
    (P []) ->
    (forall (x: A), P [x]) ->
    (forall (x y: A) (zs: list A), P zs -> P (x::y::zs)) ->
    (forall (xs: list A), P xs).
Proof.

Qed.
