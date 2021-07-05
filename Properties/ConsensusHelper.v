From mathcomp Require Import all_ssreflect.

From mathcomp Require Import finmap.

From CKB Require Import Types Parameters Chains Forest Setfs Messages States Network.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* some local state has the chain as its main chain *)
Definition has_chain (bc : Blockchain) (us : UState) : Prop :=
  btBlockchain (btree us) == bc.

(* some local state has the block tree *)
Definition has_bt (bt : BlockTree) (us : UState) : Prop :=
  btree us == bt.

(* the main blockchain is valid wrt. the block tree *)
Definition valid_with_bc (bt : BlockTree) (bc : Blockchain) :=
  (forall h b, bt.[? h] = Some b -> h = #b b) /\
  bt.[? #b GenesisBlock] = Some GenesisBlock /\
  bc = btBlockchain bt.

(* get in flight blocks for a user
   all blocks should be valid in terms of its proof validity *)
Fixpoint blocks_for_rec (ps : seq Packet) :=
  match ps with
  | [::] => [::]
  | p :: ps' =>
    if (msg p) is BlkMsg b then
      if VAF b then b :: blocks_for_rec ps'
      else blocks_for_rec ps'
    else blocks_for_rec ps'
  end.

Definition blocks_for (u : UserId) (gs : GState) :=
  undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u]).

Lemma compute_blockchain_initBlockTree :
  forall (b : Block),
    #b b \in initBlockTree ->
    compute_blockchain initBlockTree b = [:: GenesisBlock].
Proof.
  move => b; rewrite /compute_blockchain.
  have D : #|` domf initBlockTree| = 1 by rewrite /initBlockTree /= fsetU0 cardfs1.
  move: GB_hash => P.
  rewrite /initBlockTree inE /= fsetU0 in_fset1 => /eqP /hashB_inj E.
  rewrite /compute_blockchain_rec cardfs1.
  rewrite E fset11 inE [domf [fmap].[_ <- _]]/= inE fset11 /orb P.
    by rewrite fnd_set !eqxx.
Qed.
  
Lemma btBlockchain_initBlockTree :
  btBlockchain initBlockTree = [:: GenesisBlock].
Proof.
  rewrite /initBlockTree /btBlockchain /good_blockchains /all_blockchains /=.
  rewrite fsetU0 /=.
  have H : get_block [fmap].[#b GenesisBlock <- GenesisBlock] (#b GenesisBlock)
           \in [seq get_block [fmap].[#b GenesisBlock <- GenesisBlock] k | k <- [fset #b GenesisBlock]].
    by apply: map_f; rewrite fset11.
  rewrite {1}/get_block fnd_set eqxx in H.
  have P : size [seq get_block [fmap].[#b GenesisBlock <- GenesisBlock] k | k <- [fset #b GenesisBlock]]
           = size [fset #b GenesisBlock].
    by apply: size_map.
  rewrite cardfs1 in P.
  have I : #b GenesisBlock \in initBlockTree.
    by rewrite /initBlockTree inE /= fsetU0 fset11.
  suff Hsuff : [seq get_block [fmap].[#b GenesisBlock <- GenesisBlock] k | k <- [fset #b GenesisBlock]]
                 = [:: GenesisBlock].
  rewrite Hsuff /= (compute_blockchain_initBlockTree I) /= eqxx init_valid_blockchain /=.
    by rewrite /take_better_bc; case: ifP => //.
  move: H P; set s := [seq get_block [fmap].[#b GenesisBlock <- GenesisBlock] k | k <- [fset #b GenesisBlock]].
  case: s => [|b s] H //=.
    by case => /size0nil S; move: H; rewrite S mem_seq1 => /eqP ->.
Qed.
  
Lemma in_undup {T : eqType} :
  forall (s : seq T) (x : T), x \in undup (x :: s).
Proof.
  elim => [|h s IH] x; first by rewrite inE.
  rewrite /=; case I: (x \in h :: s); last by rewrite inE; apply /orP; left.
  move: I.
  rewrite inE Bool.orb_true_iff; move => [H | H].
  move /eqP: H => <-; rewrite /= in IH.
  case In: (x \in s); last by rewrite inE; apply /orP; left.
    by move: (IH x) => /=; rewrite In.  
  rewrite /= in IH; move: (IH x); rewrite H.
  case In: (h \in s); first by done.
    by rewrite inE => Hin; apply /orP; right.
Qed.  

(* a lemma stating the above implementation is what we expected *)
Lemma b_in_blocks_for (p : Packet) (b : Block) (gs : GState) :
  VAF b -> p \in inflight_msg gs -> msg p = BlkMsg b -> b \in blocks_for (dst p) gs.
Proof.
  move => Hvaf Hflight Hmsg.
  rewrite /blocks_for.
  elim: (inflight_msg gs) Hflight => [|p' ps' IH] //.
  rewrite inE => /orP [Hp | Hin].
  move /eqP: Hp => <- /=.
  rewrite eqxx /blocks_for_rec Hmsg Hvaf.
    by rewrite in_undup.
  move: (IH Hin) => H.
  rewrite /=; case (dst p' == dst p); last by done.
  rewrite /=. case: (msg p'); [| by done | by done].
  move => b'; case E: (b' == b); case: (VAF b') => //.
    by move /eqP: E => ->; rewrite in_undup.
  rewrite /=; case I: (b' \in blocks_for_rec _); first by done.
    by rewrite inE; apply /orP; right.  
Qed.

(* the blockchain is the main chain in the global system *)
Definition largest_chain (gs : GState) (bc : Blockchain) :=
  forall (u : UserId) (bc' : Blockchain),
    holds u gs (fun us => has_chain bc' us -> bc >=b bc').

(* define global stable state, i.e. no in flight packets, and all users have some same blockchain *)
Definition g_stable (gs : GState) :=
  inflight_msg gs = [::] /\
  exists (bc : Blockchain),
    forall (u : UserId), holds u gs (has_chain bc).

(* lemmas to deal with blocks_for_rec and cat *)
Lemma blocks_for_split :
  forall (p1 p2 : seq Packet),
    blocks_for_rec (p1 ++ p2) = blocks_for_rec p1 ++ blocks_for_rec p2.
Proof.
  elim => [|h p1 IH] p2; first by rewrite cat0s.
  rewrite cat_cons /=.
  case: (msg h) => b; try apply: IH.
  case V: (VAF b); last by apply: IH.
    by rewrite cat_cons IH.
Qed.

Lemma valid_blockchain_preserve :
  forall (bc pre : Blockchain) (b : Block),
    valid_blockchain_rec (rcons bc b) pre -> VAF b.
Proof.
  elim => [|a bc IH] pre b.
  - rewrite /valid_blockchain /valid_blockchain_rec /=.
      by move => /andP [/andP [V _] _].
  - rewrite rcons_cons /valid_blockchain /valid_blockchain_rec -!/valid_blockchain_rec.
    move => /andP [_ H].
    apply: IH H.
Qed.
