(* Equivalence of two classical axioms. *)

Definition peirce   := forall (P Q: Prop), ((P -> Q) -> P) -> P.
Definition imp_disj := forall (P Q: Prop), (P -> Q) -> ~P \/ Q.

Lemma imp_disj_peirce:
  imp_disj -> peirce.
Proof.
  unfold peirce, imp_disj.
  intros H P Q I.
  destruct (H P P (fun p => p)) as [J|J].
  apply I; intro K; destruct (J K).
  apply J.
Qed.

Lemma peirce_imp_disj:
  peirce -> imp_disj.
Proof.
  unfold peirce, imp_disj.
  intros H P Q I.
  apply (H _ False).
  intros J.
  left; intros K.
  apply J.
  right; apply I; apply K.
Qed.
