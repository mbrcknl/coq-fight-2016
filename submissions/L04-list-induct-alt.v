(* An alternate list induction principle. *)

Section list_ind_alt_sect.

  Variables
    (P: nat -> Prop).

  Hypotheses
    (P_0: P 0)
    (P_1: P 1)
    (P_2: forall n, P n -> P (S (S n))).

  (* You'll need to strengthen the goal before induction,
     to get a stronger induction hypothesis.
     Use `assert something` first to achieve this.
     The `something` must be weak enough to be true in the base case,
     and strong enough to leapfrog alternate nats in the inductive case.
     Start by thinking about what you already know in the base case. *)
  Lemma list_ind_alt (n: nat): P n.
  Proof.

  Qed.

End list_ind_alt_sect.
