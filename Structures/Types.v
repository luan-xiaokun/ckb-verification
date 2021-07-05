From mathcomp.ssreflect Require Import all_ssreflect.

From mathcomp.finmap Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Parameter UserId : Set.
Parameter Transaction : Set.
Parameter HashValue : Set.
Parameter ProofValue : Set.

(* assume a finite set of users *)
Axiom userid_eqMixin : Equality.mixin_of UserId.
Canonical userid_eqType := Eval hnf in EqType UserId userid_eqMixin.
Axiom userid_choiceMixin : Choice.mixin_of UserId.
Canonical userid_choiceType := Eval hnf in ChoiceType UserId userid_choiceMixin.
Axiom userid_finMixin : Finite.mixin_of userid_eqType.
Canonical userid_finType := Eval hnf in FinType UserId userid_finMixin.

(* assume a countable set of transactions *)
Axiom transaction_eqMixin : Equality.mixin_of Transaction.
Canonical transaction_eqType := Eval hnf in EqType Transaction transaction_eqMixin.
Axiom transaction_choiceMixin : Choice.mixin_of Transaction.
Canonical transaction_choiceType := Eval hnf in ChoiceType Transaction transaction_choiceMixin.

(* assume a countable set of hash value *)
Axiom hashvalue_eqMixin : Equality.mixin_of HashValue.
Canonical hashvalue_eqType := Eval hnf in EqType HashValue hashvalue_eqMixin.
Axiom hashvalue_choiceMixin : Choice.mixin_of HashValue.
Canonical hashvalue_choiceType := Eval hnf in ChoiceType HashValue hashvalue_choiceMixin.

(* assume a countbale set of proof value *)
Axiom proofvalue_eqMixin : Equality.mixin_of ProofValue.
Canonical proofvalue_eqType := Eval hnf in EqType ProofValue proofvalue_eqMixin.
Axiom proofvalue_choiceMixin : Choice.mixin_of ProofValue.
Canonical proofvalue_choiceType := Eval hnf in ChoiceType ProofValue proofvalue_choiceMixin.

(* assume a discrete time model *)
Definition Time := nat.

Record Block :=
  mkBlock {
      prev_blk : HashValue;
      prop_txs : seq HashValue;
      comm_txs : seq Transaction;
      proof : ProofValue;
      }.

(* register canonical structures *)
Definition codeBlock (b : Block) :=
  (prev_blk b, prop_txs b, comm_txs b, proof b).

Definition decodeBlock c :=
  let: (prev_blk, prop_txs, comm_txs, proof) := c in
  mkBlock prev_blk prop_txs comm_txs proof.

Lemma cancelBlock : pcancel codeBlock (fun x => Some (decodeBlock x)).
Proof. by case. Qed.

Canonical block_eqType := EqType Block (PcanEqMixin cancelBlock).
Canonical block_choiceType := ChoiceType Block (PcanChoiceMixin cancelBlock).

(* blockchain, block tree and transaction pool *)
Definition Blockchain := seq Block.

Definition BlockTree := {fmap HashValue -> Block}.

Definition TxPool := seq Transaction.
