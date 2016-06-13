(* Binary representation of the positive integers. *)

Inductive pos: Set :=
  | bI: pos
  | b0: pos -> pos
  | b1: pos -> pos.

(* For illustration, we can interpret these as naturals. *)

Fixpoint nat_of (p: pos): nat :=
  match p with
    | (* Initial one bit. *)
      bI => 1
    | (* Shift left plus zero. *)
      b0 p => 2 * nat_of p
    | (* Shift left plus one. *)
      b1 p => S (2 * nat_of p)
  end.

(* In this interpretation, we read bits right-to-left. *)

Example eg_11: nat_of (b1 (b1 (b0 bI))) = 11. simpl. reflexivity. Qed.
Example eg_12: nat_of (b0 (b0 (b1 bI))) = 12. simpl. reflexivity. Qed.
Example eg_13: nat_of (b1 (b0 (b1 bI))) = 13. simpl. reflexivity. Qed.

(* A successor function consistent with this interpretation. *)

Fixpoint succ (p: pos): pos :=
  match p with
    | (* Carry the one. *)
      bI => b0 bI
    | (* Increment the least-significant bit. *)
      b0 q => b1 q
    | (* Carry the one. *)
      b1 q => b0 (succ q)
  end.

(* Challenge: prove a nat-like induction principle for `pos`. *)
(* This is a bit tricky, so I've given you a head start. *)

Definition pos_succ_rect:
  forall (p: pos) (P: pos -> Type) (I: P bI) (S: forall p, P p -> P (succ p)), P p.
Proof.
  induction p; intros P I S.
  - (* Base case bI *)
    assumption.
  - (* Inductive case b0 *)
    (* Note: when we apply IHp, we implicitly instantiate its P
         with `fun p => P (b0 p)`! *)
    apply IHp.
    + (* Prove the first assumption of IHp, which corresponds to I,
           but with the specialised P. *)
      (* Look at the next sub-case for some hints. *)
      change (P (succ bI)). apply S. apply I.
    + (* Prove the second assumption of IHp, which corresponds to S,
           but with the specialised P. *)
      intros q H.
      (* The `change` tactic replaces the current goal with another,
           provided it has the same normal form. *)
      (* Here, `P (succ (succ (b0 q)))` could be simplified
           to `P (b0 (succ q))`, so this `change` is allowed. *)
      change (P (succ (succ (b0 q)))).
      (* We use the S we were given to prove IHp's S, but since we
           have lifted IHp's P over b0, we need to apply S twice! *)
      apply S. apply S. apply H.
  - (* Inductive case b1 *)
    (* Should be somewhat similar to the b0 case! *)
    apply IHp.
    + change (P (succ (succ bI))). apply S. apply S. apply I.
    + intros q H. change (P (succ (succ (b1 q)))).
      apply S. apply S. apply H.
Defined.
