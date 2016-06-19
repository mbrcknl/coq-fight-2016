(* Boolean maps *)

Lemma bools_errand:
  forall (f: bool -> bool) (b: bool), f (f (f b)) = f b.
Proof.
  destruct b; destruct (f true) eqn:T; destruct (f false) eqn:F;
    try (rewrite T); try (rewrite F); auto.
Qed.

Fixpoint iterate (n: nat) (f: bool -> bool) (x: bool): bool :=
  match n with
    | O => x
    | S p => f (iterate p f x)
  end.

Definition twice := iterate 2.

Lemma bools_iterated:
  forall (f: bool -> bool) (b: bool) (n: nat), iterate n (twice f) (f b) = f b.
Proof.
  induction n; simpl.
  - auto.
  - rewrite IHn. unfold twice; simpl. apply bools_errand.
Qed.
