(* A graph reachability lemma. *)

Section graph_reachability.

  (* Assume a base type of elements. *)
  Variable T: Type.

  (* We identify a set of elements by its membership predicate. *)
  Definition set: Type := T -> Prop.

  (* The subset relation is defined pointwise on membership predicates. *)
  Definition subset (A B: set): Prop := forall x, A x -> B x.
  
  (* Likewise, set union. *)
  Definition union (A B: set): set := fun x => A x \/ B x.

  (* Now assume a step relation on T. *)
  Variable step: T -> T -> Prop.

  (* The set of elements reachable by 0 or more steps from a set of roots R. *)
  Inductive reachable (R: set): set :=
  | reach_root: forall x, R x -> reachable R x
  | reach_step: forall x y, reachable R x -> step x y -> reachable R y.

  Hint Constructors reachable.

  (* Prove that reachability is distributive over set union, in two parts. *)
  Lemma reachable_union:
    forall R S, subset (reachable (union R S))
                  (union (reachable R) (reachable S)).
  Proof.
    intros R S x H; induction H.
    - destruct H; [left|right]; eauto.
    - destruct IHreachable; [left|right]; eauto.
  Qed.

  Lemma union_reachable:
    forall R S, subset (union (reachable R) (reachable S))
                  (reachable (union R S)).
  Proof.
    intros R S x [H|H]; induction H; eauto.
    - apply reach_root; left; auto.
    - apply reach_root; right; auto.
  Qed.

End graph_reachability.
