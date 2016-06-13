(* Boolean maps *)

Lemma bools_errand:
  forall (f: bool -> bool) (b: bool), f (f (f (f (f b)))) = f (f (f b)).
Proof.
  intros f; destruct b; destruct (f true) eqn:T; destruct (f false) eqn:F;
  repeat (try rewrite T; try rewrite F); auto.
Qed.

Fixpoint iterate (n: nat) (f: bool -> bool) (x: bool): bool :=
  match n with
    | O => x
    | S p => f (iterate p f x)
  end.

Definition twice := iterate 2.

Lemma bools_iterated:
  forall (f: bool -> bool) (b: bool) (m n: nat),
    iterate m (twice f) (f b) = iterate n (twice f) (f b).
Proof.
  intros f b m n.
  assert (forall k, iterate k (twice f) (f b) = f b).
  - induction k; simpl.
    + reflexivity.
    + rewrite IHk; unfold twice; simpl;
        destruct b; destruct (f true) eqn:T; destruct (f false) eqn:F;
        try (rewrite T); try (rewrite F); auto.
  - rewrite (H m); rewrite (H n); reflexivity.
Qed.
