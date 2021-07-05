From mathcomp.ssreflect Require Import all_ssreflect.

From mathcomp.finmap Require Import finmap.

From CKB Require Import Types Parameters Chains Forest.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fset_scope.
Open Scope fmap_scope.

(* three types of messages, sending blocks, sending transactions, and requesting transactions *)
Inductive MessageType :=
| MtBlock
| MtTxs
| MtReq.

Inductive Message :=
| BlkMsg of Block
| TxsMsg of seq Transaction
| ReqMsg of seq HashValue.

(* register message type as canonical structures *)
Definition MessageType2o (mt : MessageType) : 'I_3 :=
  inord (match mt with
         | MtBlock => 0
         | MtTxs => 1
         | MtReq => 2
         end).

Definition o2MessageType (o : 'I_3) : option MessageType :=
  match val o with
  | 0 => Some MtBlock
  | 1 => Some MtTxs
  | 2 => Some MtReq
  | _ => None
  end.

Lemma pcancel_MessageType : pcancel MessageType2o o2MessageType.
Proof. by case; rewrite /o2MessageType /= inordK. Qed.

Canonical messageType_eqType := EqType MessageType (PcanEqMixin pcancel_MessageType).
Canonical messageType_choiceType := ChoiceType MessageType (PcanChoiceMixin pcancel_MessageType).
Canonical messageType_countType := CountType MessageType (PcanCountMixin pcancel_MessageType).
Canonical messageType_finType := FinType MessageType (PcanFinMixin pcancel_MessageType).

(* given a message, return its type *)
Definition msg_type (m : Message) :=
  match m with
  | BlkMsg _ => MtBlock
  | TxsMsg _ => MtTxs
  | ReqMsg _ => MtReq
  end.

(* given a message, return the block in it, if it has any; otherwise return genesis block *)
Definition msg_block (m : Message) :=
  match m with
  | BlkMsg b => b
  | _ => GenesisBlock
  end.

(* given a message, return the requesting hashed in it, if it has any *)
Definition msg_hashes (m : Message) :=
  match m with
  | ReqMsg hs => hs
  | _ => [::]
  end.

(* define equality of message *)
Definition msg_eq (a b : Message) :=
  match a, b with
  | BlkMsg bA, BlkMsg bB => bA == bB
  | TxsMsg tA, TxsMsg tB => tA == tB
  | ReqMsg hA, ReqMsg hB => hA == hB
  | _, _ => false
  end.

(* register Message as canonical structures *)
Lemma msg_eqP : Equality.axiom msg_eq.
Proof.
  move => ma mb; case: ma; case: mb => //= pb pa; try by [constructor 2];
  do? [
  case E: (pa == pb); [constructor 1 | constructor 2]; move /eqP: E => E;
    [by subst pa | by case]
  ].
Qed.    

Canonical message_eqType := EqType Message (EqMixin msg_eqP).

(* a packet is a triple of source, destination, and message *)
Record Packet :=
  mkPacket {
      src : UserId;
      dst : UserId;
      msg : Message;
    }.

(* register Packet as canonical structures *)
Definition codePacket (p : Packet) :=
  (src p, dst p, msg p).

Definition decodePacket c :=
  let: (src, dst, msg) := c in
  mkPacket src dst msg.

Lemma pcancel_Packet : pcancel codePacket (fun x => Some (decodePacket x)).
Proof. by case. Qed.

Canonical packet_eqType := EqType Packet (PcanEqMixin pcancel_Packet).

(* abbrv for packet *)
Definition emitZero : seq Packet := [::].
Definition emitOne p : seq Packet := [:: p].
Definition emitMany (ps : seq Packet) := ps.
Definition emitBroadcast (from : UserId) (to : seq UserId) (m : Message) :=
  [seq mkPacket from t m | t <- to].
