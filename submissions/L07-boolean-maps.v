(* Boolean maps *)

Lemma bools_errand:
  forall (f: bool -> bool) (b: bool), f (f (f (f (f b)))) = f (f (f b)).
Proof.

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

Qed.
