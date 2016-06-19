(* Boolean maps *)

Lemma bools_errand:
  forall (f: bool -> bool) (b: bool), f (f (f b)) = f b.
Proof.

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

Qed.
