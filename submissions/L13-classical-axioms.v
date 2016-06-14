(* Equivalence of two classical axioms. *)

Definition peirce   := forall (P Q: Prop), ((P -> Q) -> P) -> P.
Definition imp_disj := forall (P Q: Prop), (P -> Q) -> ~P \/ Q.

Lemma imp_disj_peirce:
  imp_disj -> peirce.
Proof.

Qed.

Lemma peirce_imp_disj:
  peirce -> imp_disj.
Proof.

Qed.
