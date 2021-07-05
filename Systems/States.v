From mathcomp.ssreflect Require Import all_ssreflect.

From mathcomp.finmap Require Import finmap.

From CKB Require Import Types Parameters Chains Forest Messages.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fset_scope.
Open Scope fmap_scope.

(* local state *)
Record UState :=
  mkUState {
      id : UserId;
      peers : seq UserId;
      btree : BlockTree;
      txpool : TxPool;
(*      missingpool : {fmap UserId -> seq HashValue}; (* hashes of missing transactions *)
      waiting : bool;          (* indicate if the node is waiting for response *)
      clock : Time;            (* reset after requesting *)
      deadline : Time;         (* black list the sender if it does not send valid transactions back before ddl *)
      retry : nat;             (* 0: not waiting; 1: first request; 2: second request *) *)
    }.

(* register UState as canonical structures *)
Definition codeUState (us : UState) :=
  (id us, peers us, btree us, txpool us).

Definition decodeUState c :=
  let: (u, prs, bt, pool) := c in
  mkUState u prs bt pool.

Lemma cancelUState : pcancel codeUState (fun x => Some (decodeUState x)).
Proof. by case. Qed.

Canonical ustate_eqType := EqType UState (PcanEqMixin cancelUState).
Canonical ustate_choiceType := ChoiceType UState (PcanChoiceMixin cancelUState).

(* initial block tree only has genesis block *)
Definition initBlockTree := [fmap].[#b GenesisBlock <- GenesisBlock].

(* initial state includes all users as peers *)

Definition initUState (u : UserId) :=
  mkUState u (seq.rem u (enum userid_finType)) initBlockTree [::].

(* transition triggered by receiving message *)
Definition recv_msg (us : UState) (from : UserId) (m : Message) (t : Time) :=
  let: mkUState u prs bt tp := us in
  match m with
  | BlkMsg b => true
  | TxsMsg ts => true
  | ReqMsg hs => false
  end.

(* internal transition *)
Inductive InternalTransition :=
| IntTxs of seq Transaction
| IntMine.

(**** local state transition after receiving messages ****)

(* case 1. receive BlkMsg
   - commitment transactions are valid and proof is valid
   - case 1.1. some proposal transactions are missing
   - case 1.2. all proposal transactions are in txpool *)

(* case 2. receive BlkMsg
   - commitment transactions are not valid, or proof is not valid *)

(* validity_ok means the commitment transactions and proof of the block is valid wrt. the local state *)
Definition validity_ok (b : Block) (us : UState) :=
  VAF b.

(* to request missing transactions, we need to know which transactions are missing 
   also, if return value is [::], then there are no missing transactions *)
Definition missing_transactions (hs : seq HashValue) (ts : TxPool) :=
  [seq h <- hs | h \notin [seq hashPID t | t <- ts]].

Definition prop_missing (b : Block) (us : UState) :=
  missing_transactions (prop_txs b) (txpool us) == [::].

(* combine these two, precondition of requesting transactions (case 1.1) *)
Definition request_ok (b : Block) (us : UState) :=
  validity_ok b us && prop_missing b us.

(* using `missing_transactions', we can compute these missing transactions *)
Definition prop_missing_txs (b : Block) (us : UState) :=
  missing_transactions (prop_txs b) (txpool us).

(* update state
   - 1. add the block to the block tree
   - 2. removing transactions in the pool that are not consistent with the current chain 
   - 3. if proposal transactions are missing, add these to missingpool*)
Definition receive_block_update (b : Block) (us : UState) :=
  let: mkUState u ps bt pool := us in
  let: new_bt := bt.[#b b <- b] in
  mkUState u ps new_bt [seq t <- pool | txValid t (btBlockchain new_bt)].

(* broadcast messages *)
Definition broadcast_message (m : Message) (us : UState) (sender : UserId) :=
  let: mkUState u ps _ _ := us in
  emitBroadcast u (seq.rem sender ps) m.

(* request from sender *)
Definition request_missing (b : Block) (us : UState) (sender : UserId) :=
  emitOne (mkPacket (id us) sender (ReqMsg (prop_missing_txs b us))).

(* case 3. receive TxsMsg 
   - case 3.1. if the transactions are not all in the txpool, add them and broadcast the message
   - case 3.2. if the transactions are already in txpool, then do nothing*)

(* update state 
   - add the transactions to the pool *)
Definition receive_transactions_update (ts : seq Transaction) (us : UState) :=
  let: mkUState u ps bt pool := us in
  let: new_pool := foldr (fun t tp => tpExtend tp bt t) pool ts in
  mkUState u ps bt new_pool.

(* compare the missing pool and the received transactions
   return true if they match, otherwise return false *)
Fixpoint contains {T : eqType} (s1 s2 : seq T) :=
  match s2 with
  | [::] => true
  | h :: s => (h \in s1) && contains (seq.rem h s1) s
  end.

Definition already_have_transactions (ts : seq Transaction) (us : UState) :=
  contains (txpool us) ts.

(* case 4. recive ReqMsg
   check if has the requested transactions
   - case 4.1. if yes, send these requested transactions
   - case 4.2. if only has part of these, send what he has
   - case 4.3. if not, send a nil message *)

(* get the requested transactions according to its hash value *)
Definition get_transactions_with_hashes (hs : seq HashValue) (us : UState) :=
  [seq t <- txpool us | hashPID t \in hs].

(* response to request *)
Definition response_to_transactions (hs : seq HashValue) (us : UState) (sender : UserId) :=
  emitOne (mkPacket (id us) sender (TxsMsg (get_transactions_with_hashes hs us))).

(* process incoming messages *)
Definition proc_msg (us : UState) (from : UserId) (m : Message) (time : Time) :=
  match m with
  | BlkMsg b =>
    if VAF b then
      if prop_missing b us then
        pair (receive_block_update b us)
             (request_missing b us from ++ broadcast_message m us from)
      else pair (receive_block_update b us)
                (broadcast_message m us from)
    else pair us emitZero
  | TxsMsg ts =>
    if already_have_transactions ts us then
      pair us emitZero
    else pair (receive_transactions_update ts us)
              (broadcast_message m us from)
  | ReqMsg hs  => pair us (response_to_transactions hs us from)
  end.

(* process internal transition *)
Definition proc_int (us : UState) (int : InternalTransition) (time : Time) :=
  match int with
  | IntTxs ts =>
    pair (receive_transactions_update ts us)
                      (emitBroadcast (id us) (peers us) (TxsMsg ts))
  | IntMine =>
    let: bc := btBlockchain (btree us) in
    let: txs := [seq t <- txpool us | commTxsValid t bc] in
    match genProof (id us) bc txs time with
    | Some pf =>
      let: prev_blk := last_blk bc in
      let: b := mkBlock (#b prev_blk) [seq hashPID t | t <- txpool us & t \notin txs] txs pf in
      if VAF b && all [pred t | commTxsValid t bc] (comm_txs b) then
        let: new_bt := (btree us).[#b b <- b] in
        let: new_pool := [::] in
        pair (mkUState (id us) (peers us) new_bt new_pool) (emitBroadcast (id us) (peers us) (BlkMsg b))
      else pair us emitZero
    | None => pair us emitZero
    end
  end.

(* local system transition *)
Inductive local_step (us us' : UState) : Prop :=
| Idle of us = us'
| RcvMsg from msg t of us' = (proc_msg us from msg t).1
| IntT int t of us' = (proc_int us int t).1 .
