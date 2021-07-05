From mathcomp Require Import all_ssreflect.

From CKB Require Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(********    Parameters    ********)

(* assume there is at least one user *)
Parameter user : UserId.

(* parameters about hash function *)
Parameter hashT : Transaction -> HashValue.
Parameter hashPID : Transaction -> HashValue.
Parameter hashB : Block -> HashValue.
Notation "#b x" := (hashB x) (at level 20).
Notation "#t x" := (hashT x) (at level 20).

(* parameters about blockchain *)
Parameter GenesisBlock : Block.
Definition last_blk (bc : Blockchain) := last GenesisBlock bc.
Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

(* a transaction in commitment zone is valid if it
  - 1. is within the range [close, far]
  - 2. is compatible with previous transactions *)
Parameters close window' : nat.
Definition window := window'.+1.
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.
Definition slice {T : eqType} (s : seq T) (t0 : T) (low : nat) (len : nat) :=
  foldr (fun i a => nth t0 s i :: a) [::] (iota low len).
Definition commTxsValid (t : Transaction) (bc : Blockchain) :=
  txValid t bc && (#t t \in foldr cat [::] [seq prop_txs b | b <- (slice bc GenesisBlock close window)]).

(* different miners may generate different proofs at different time, 
   the `seq Transactions' should be commitment transactions, stressing that
   the validity of proposal transactions does not affect the block's validity *)
Parameter genProof : UserId -> Blockchain -> seq Transaction -> Time -> option ProofValue.

(* VAF is used to ensure a block is valid wrt. its proof,
   since the proof is contained in the block, there is no need to provide
   another `ProofValue' argument  *)
Parameter VAF : Block -> bool.
  
(* fork choice rule provides partial order on blockchains *)
Parameter FCR : Blockchain -> Blockchain -> bool.
Notation "A >b B" := (FCR A B) (at level 70).
Notation "A >=b B" := (A = B \/ A >b B) (at level 70).

(********     Axioms     ********)

(* axioms for hash function and genesis block *)
Axiom hashB_inj : injective hashB.
Axiom hashT_inj : injective hashT.
Axiom hashPID_inj : injective hashPID.
Axiom nonGB_hash : forall (b : Block), b <> GenesisBlock -> prev_blk b != #b b.
Axiom GB_hash : prev_blk GenesisBlock = #b GenesisBlock.
Axiom GB_nil : comm_txs GenesisBlock = nil /\ prop_txs GenesisBlock = nil.
(* Axiom nonGB_noloop : forall (a b : Block), b != GenesisBlock -> prev_blk b = #b a -> prev_blk a != #b b. *)
(* axioms for transaction validity *)
Axiom txvalid_nil : forall (t : Transaction), txValid t [::].

Lemma nil_slice {T : eqType} : forall (t : T) (m n : nat), slice [::] t m n = List.repeat t n.
Proof.
  move => t m n; elim: n m=> [|n IH] m //=.
    by rewrite -(IH m.+1) /slice //= nth_nil.
Qed.

Lemma not_commtxvalid_nil : forall (t : Transaction), ~~commTxsValid t [::].
Proof.
  rewrite /commTxsValid => t; rewrite txvalid_nil.
  rewrite nil_slice. elim: window => //= n IH.
    by destruct GB_nil as [_ H]; rewrite H //=.
Qed.

(* axioms for VAF *)
(* Axiom VAF_nocycle : forall (b : Block) (bc : Blockchain), VAF b bc -> b \notin bc. *)
Axiom VAF_init : VAF GenesisBlock.

(* axioms for fork choice rule *)
Axiom FCR_nrefl : forall bc, ~ bc >b bc.
Axiom FCR_trans : forall bc1 bc2 bc3, bc1 >b bc2 -> bc2 >b bc3 -> bc1 >b bc3.
Axiom FCR_rel : forall bc1 bc2, bc1 >b bc2 \/ bc1 = bc2 \/ bc2 >b bc1.
(* Axiom FCR_subchain : forall bc1 bc2, subchain bc1 bc2 -> bc2 >=b bc1. *)
Axiom FCR_ext : forall bc b ext, bc ++ (b :: ext) >b bc.
