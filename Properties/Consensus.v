From mathcomp Require Import all_ssreflect.

From mathcomp Require Import finmap.

From CKB Require Import Types Parameters Chains Forest Setfs Messages States Network ConsensusHelper.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition G_syncing (gs : GState) :=
  exists (can_bt : BlockTree) (can_bc : Blockchain) (can_u : UserId),
    [/\ holds can_u gs (has_chain can_bc),
     largest_chain gs can_bc,
     (valid_bt can_bt /\ has_gb can_bt /\ can_bc = btBlockchain can_bt /\ good_bt can_bt),
     (forall (u' : UserId),
       peers (user_state gs u') = rem u' (enum userid_finType)) &
     forall (u' : UserId),
       holds u' gs (fun us => can_bt = foldl bt_upd (btree us) (blocks_for u' gs))
    ].

Definition sync_inv (gs : GState) :=
  Coh gs /\ G_syncing gs.

(* sync invariant holds in the initial state *)
Lemma sync_initial_state :
  sync_inv initGState.
Proof.
  rewrite /sync_inv; split.
  exact Coh_init.
  exists initBlockTree, [:: GenesisBlock], user; split.
  - rewrite /holds /has_chain initGState_user.
      by rewrite /initUState btBlockchain_initBlockTree eqxx.
  - rewrite /largest_chain /holds /has_chain => u bc.
    rewrite initGState_user => /eqP <-.
      by rewrite btBlockchain_initBlockTree; left.
  - repeat split; rewrite /initBlockTree.
    + move => h b; rewrite fnd_set; case: ifP; last by rewrite fnd_fmap0.
        by move => /eqP ->; case => ->.
    + by rewrite /has_gb fnd_set eqxx.
    + by rewrite -/initBlockTree btBlockchain_initBlockTree.
    + move => b; rewrite -/initBlockTree => I; apply /andP.
      split; rewrite compute_blockchain_initBlockTree //;
        by [rewrite /good_blockchain eqxx | apply: init_valid_blockchain].
  - by move => u; rewrite initGState_user /initUState /=.
  - rewrite /holds => u.
      by rewrite initGState_user /initUState /=.
Qed.

(* sync invariant means eventual consensus *)
Lemma sync_eventual_consensus (gs : GState) :
  sync_inv gs -> (forall (u : UserId), blocks_for u gs == [::]) ->
  exists (bc : Blockchain), largest_chain gs bc /\
                            (forall (u : UserId), holds u gs (has_chain bc)).
Proof.
  case => C [can_bt] [can_bc] [can_u] [H1 H2 [H3 [H4 [H5 H6]]] H7 H8] Hnil.
  exists can_bc. split => // u.
  move: (Hnil u) => /eqP Hnilb.
  move: (H8 u). rewrite Hnilb /=.
    by rewrite /has_chain /holds H5 => <-.
Qed.

(* sync invariant holds as long as user states do not change *)
Lemma sync_no_change (gs : GState) :
  forall (p1 p2 : seq Packet) (u : UserId) (us : UState),
    let: gs' := {| user_state := setfs (user_state gs) u us;
                   inflight_msg := p1;
                   consumed_msg := p2 |} in
    peers us = peers (user_state gs u) ->
    btree us = btree (user_state gs u) ->
    (forall (u : UserId), blocks_for u gs = blocks_for u gs') ->
    G_syncing gs -> G_syncing gs'.
Proof.
  move => p1 p2 u us Hpeers Hbtree H.
  rewrite /G_syncing /largest_chain /holds /user_state.
  case => bc [bt] [can_u] [H1 H2 H3 H4 H5].
  exists bc, bt, can_u.
  split => //= => [|u' bc'|u'|u']; rewrite setfsNK; case: ifP.
    by rewrite /has_chain Hbtree /=; move /eqP => <-; apply: H1.
    by move => _; apply: H1.
    by rewrite /has_chain Hbtree /=; move /eqP => <- ; apply: H2.
    by move => _; apply: H2.
    by rewrite Hpeers /=; move /eqP => ->; apply: H4.
    by move => _; apply: H4.
    rewrite (H5 u') H => /eqP ->.
    by rewrite /blocks_for Hbtree /=.
    by rewrite (H5 u') H /blocks_for /=.
Qed.

Lemma irrelevant_message :
  forall (gs : GState) (u : UserId) (p : Packet),
    p \in inflight_msg gs -> (forall (b : Block), msg p != BlkMsg b)->
    blocks_for_rec [seq p0 <- inflight_msg gs | dst p0 == u] =
    blocks_for_rec [seq p0 <- rem p (inflight_msg gs) | dst p0 == u].
Proof.
  move => gs u p /rem_split => Hex Hn.
  case: Hex => p1 [p2] [P_ext [P_nin P_rem]].
  rewrite P_rem P_ext !filter_cat !blocks_for_split /=.
  case: ifP => //= D.
  case M: (msg p) => //= [b'].
    by contradict M; apply /eqP.
Qed.

Lemma irrelevant_broadcast :
  forall (u : UserId) (prs : seq UserId) (ps : seq Packet) (a : pred Packet) (m : Message),
    (forall (b : Block), m != BlkMsg b) ->
    blocks_for_rec [seq p <- ps ++ emitBroadcast u prs m | a p] =
    blocks_for_rec [seq p <- ps | a p].
Proof.
  move => u; elim => [|i prs IH] ps a m Hn /=; first by rewrite cats0.
  rewrite -(IH ps a m Hn).
  rewrite !filter_cat !blocks_for_split /=.
  case: ifP => //=; case: m Hn => [b|ts|hs] Hn;
    by [move: (Hn b); rewrite eqxx |].
Qed.

Lemma filter_all_nil {T : Type} :
  forall (a : pred T) (s : seq T),
    all (fun x => ~~ a x) s -> [seq t <- s | a t] = [::].
Proof.
  move => a; elim => [|h s IH] => //=.
  move => /andP [/negPf N A].
    by rewrite N; apply: IH.
Qed.

Lemma relevant_broadcast :
  forall (from u : UserId) (b : Block) (prs : seq UserId),
  uniq prs -> u \in prs -> VAF b ->
  blocks_for_rec [seq p <- emitBroadcast from prs (BlkMsg b) | dst p == u] = [::b].
Proof.
  move => from u b prs Uniq In V.
  rewrite /emitBroadcast.
  elim: prs Uniq In => [|p prs IH] Uniq In //.
  move: Uniq => /= /andP [Hn Uniq].
  move: In; rewrite inE => /orP; case => [/eqP E | H].
  - subst p; rewrite eqxx /= V.
    suff S : all (fun x => dst x != u) [seq {| src := from; dst := t; msg := BlkMsg b |} | t <- prs]
      by rewrite filter_all_nil => //.
    elim: prs Hn Uniq {IH} => [|p prs IH] //=.
    rewrite inE negb_or => /andP; case => [Neq Nin].
    move /andP => [PNin Uniq]; apply /andP; split; last by apply: IH.
      by apply /negP; rewrite eq_sym; apply /negP.
  - case: ifP => /eqP U; last by apply: IH.
      by subst p; move: Hn; rewrite H.
Qed.

Lemma irrelevant_broadcast' :
  forall (from u : UserId) (b : Block) (prs : seq UserId),
  uniq prs -> u \notin prs ->
  blocks_for_rec [seq p <- emitBroadcast from prs (BlkMsg b) | dst p == u] = [::].
Proof.
  move => from u b prs Uniq Nin.
  rewrite /emitBroadcast.
  elim: prs Uniq Nin => [|p prs IH] Uniq Nin //.
  move: Uniq => /= /andP [Hn Uniq].
  move: Nin. rewrite inE negb_or => /andP; case => Neq Nin.
  rewrite eq_sym; move /negPf: Neq => ->.
    by apply: IH.
Qed.
  
Lemma foldl_blocks_for_upd :
  forall (bt : {fmap HashValue -> Block}) (p : Packet) (ps : seq Packet) (a : pred Packet) (b : Block),
    a p -> msg p = BlkMsg b -> VAF b ->
    foldl bt_upd bt (undup (blocks_for_rec [seq p0 <- p :: ps | a p0])) =
    foldl bt_upd (bt_upd bt b) (undup (blocks_for_rec [seq p0 <- ps | a p0])).
Proof.
  move => bt p ps a b A M V.
  rewrite /= A /= M V /=.
  case: ifP => Hin; last by done.  
  move: Hin; elim: (blocks_for_rec [seq p0 <- ps | a p0]) bt => [|b' bs IH] bt //=.
  rewrite inE => /orP; move => [/eqP H | H].
  - subst b'.
    case: ifP => Hin; first by apply: IH.
      by rewrite /= btupd_dupE.
  - case: ifP => Hin; first by apply: IH.
    rewrite /= bt_updC.
      by apply: IH.
Qed.

Lemma blocks_for_cat :
  forall (s1 s2 : seq Packet) (a : pred Packet),
    blocks_for_rec [seq p <- s1 ++ s2 | a p] =
    blocks_for_rec [seq p <- s1 | a p] ++ blocks_for_rec [seq p <- s2 | a p].
Proof.
  elim => [|h s1 IH] s2 a //=.
  case: ifP => A //=.
  case M: (msg h) => [b|ts|hs] //.
  case V: (VAF b) => //.
    by rewrite cat_cons IH.
Qed.

Lemma relevant_message :
  forall (gs : GState) (p : Packet) (bt : {fmap HashValue -> Block}) (b : Block),
  valid_bt bt ->
  p \in inflight_msg gs ->
  msg p = BlkMsg b -> VAF b ->
  foldl bt_upd bt.[#b b <- b] (undup (blocks_for_rec [seq p0 <- rem p (inflight_msg gs) | dst p0 == dst p]))
  = foldl bt_upd bt (undup (blocks_for_rec [seq p0 <- inflight_msg gs | dst p0 == dst p])).
Proof.
  move => gs p bt b Hv Hin M V.
  move: (rem_split Hin) => [s1] [s2] [Heq [Hn Hrem]].
  rewrite Hrem Heq !blocks_for_cat !foldl_undup_split.
  rewrite [foldl _ (foldl _ bt _) _]foldl_comm.
  rewrite (@foldl_blocks_for_upd bt p s2 _ b) => //.
    by rewrite foldl_comm.
Qed.

Lemma irrelevant_blkmsg:
  forall (gs : GState) (p : Packet) (bt : {fmap HashValue -> Block}) (u : UserId),
  p \in inflight_msg gs ->
  dst p == u = false -> 
  foldl bt_upd bt (undup (blocks_for_rec [seq p0 <- rem p (inflight_msg gs) | dst p0 == u]))
  = foldl bt_upd bt (undup (blocks_for_rec [seq p0 <- inflight_msg gs | dst p0 == u])).
Proof.
  move => gs p bt u Hin Ndst.
  move: (rem_split Hin) => [s1] [s2] [Heq [Hn Hrem]].
  rewrite Hrem Heq !blocks_for_cat !foldl_undup_split.
    by rewrite /= Ndst.
Qed.

Lemma in_seq_undup {T : eqType} :
  forall (s : seq T) (x : T),
    x \in s -> x \in undup s.
Proof.
  elim => [|h s IH] x //=.
  rewrite inE => /orP; move => [/eqP H | H]; case: ifP => Hp.
    by subst h; apply: IH.
    by rewrite H mem_head.
    by apply: IH.
    by rewrite inE; apply /orP; right; apply: IH.
Qed.

Lemma in_undup_seq {T : eqType} :
  forall (s : seq T) (x : T),
    x \in undup s -> x \in s.
Proof.
  elim => [|h s IH] x //=.
  case: ifP => E; rewrite inE.
    by move => /IH => H; apply /orP; right.
  move => /orP [/eqP H | H].
    by rewrite H mem_head.
    by rewrite inE; apply /orP; right; apply: IH.
Qed.

Lemma block_in_queue :
  forall (p : Packet) (b : Block) (u : UserId) (gs : GState),
    p \in inflight_msg gs -> dst p = u -> 
    msg p = BlkMsg b -> VAF b ->
    b \in blocks_for u gs. 
Proof.
  move => p b u gs Hin D M V.
  rewrite /blocks_for.
  elim: (inflight_msg gs) Hin => [|p' ps IH] //=.
  rewrite inE => /orP; move => [/eqP H | H].
    by rewrite -H D eqxx /= M V in_undup.
  case: ifP => /eqP E /=; last by apply: IH.
  case: (msg p').
  move => b'; case: ifP => _; last by apply: IH.
  apply: in_seq_undup; rewrite inE; apply /orP; right.
  apply: in_undup_seq.
    by apply: IH.
    by move => _; apply: IH.
    by move => _; apply: IH.
Qed.

Lemma notin_rem_peers :
  forall (u u' : UserId),
    u \notin rem u' (rem u (enum userid_finType)).
Proof.
  move => u u'.
  move: (enum_uniq userid_finType) => U.
  have H : u \notin rem u (enum userid_finType).
    by rewrite mem_rem_uniqF.
  elim: (rem u (enum userid_finType)) H => [|p ps IH] //=.
  rewrite inE negb_or => /andP; case => /negPf Neq Nin.
  case: ifP => //= F.
  rewrite inE negb_or; apply /andP; split.
    by rewrite Neq.
    by apply: IH.
Qed.

Lemma rem_in_mem {T : eqType} :
  forall (s : seq T) (x y : T),
    x <> y -> x \in s -> x \in rem y s.
Proof.
  elim => [|z s IH] x y N //.
  rewrite inE => /orP; case => [/eqP E | H].
  - subst z; rewrite /=.
    move /eqP/negPf: N => ->.
      by rewrite inE eqxx.
  - rewrite /=; case: ifP => E //.
    rewrite inE; apply /orP; right.
      by apply: IH.
Qed.

Lemma count1_impl_in {T : eqType} :
  forall (s : seq T) (x : T),
    count_mem x s = 1 -> x \in s.
Proof.
  elim => [|y s IH] x //=.
  case E: (y == x) => /=.
  - move /eqP: E => -> _.
      by rewrite inE eqxx.
  - rewrite add0n => /IH.
      by rewrite inE orbC => ->. 
Qed.

Lemma in_rem_peers :
  forall (u1 u2 u3: UserId),
    u1 <> u3 -> u3 <> u2 ->
    u3 \in rem u1 (rem u2 (enum userid_finType)).
Proof.
  move => u1 u2 u3 N1 N2.
  have H1 : u3 \in rem u2 (enum userid_finType).
  apply: rem_in_mem => //. rewrite enumT.
  apply: count1_impl_in; apply: enumP.
  apply: rem_in_mem => //.
    by apply /eqP/negPf; move /eqP/negPf: N1; rewrite eq_sym.
Qed.
    
(* final theorem *) 
Theorem sync_inv_step (gs gs' : GState) (s : Schedule) :
  sync_inv gs -> system_step gs gs' s -> sync_inv gs'.
Proof.
  move => [C Isync] S; split; first by apply (Coh_step S).
  case: S;
  (* Idle *)
  first by move => [_ <-].
  (* Deliver *)
  move => p.
  case => [C_uiq C_valid C_gb] S_dst S_flight.
  case P: (proc_msg _ _ _ _) => [us ps] ->.
  case M: (msg p) => [b | ts | hs]; move: P; rewrite M /=.
  
  (* Block message *)
  - case: ifP => V; last first.
    (* invalid block *)
    case => H_useq H_peq.
    apply: sync_no_change; [by rewrite -H_useq..| | by done].
    rewrite -H_peq /blocks_for /emitZero cats0 /= => u.
    move: (rem_split S_flight) => [p1] [p2] [P_ext [P_nin P_rem]].
    rewrite P_rem P_ext !filter_cat !blocks_for_split /=.
      by case: ifP => //=; rewrite M V.
    (* valid block *)
    case: Isync => can_bt [can_bc] [can_u] [I_chain I_large [I_valid [I_gb [I_ext I_good]]] I_cliq I_sub].  
    case: ifP => P; case => H_useq H_peq; exists can_bt, can_bc, can_u; split => //.
    (* no missing transactions *)
    (* has chain *)
    +  rewrite /holds /=.
       rewrite setfsNK; case: ifP => /eqP D; last by apply: I_chain.
       rewrite -H_useq /receive_block_update.
       move: I_chain; rewrite /holds /has_chain D /= => /eqP.
       move: (I_sub (dst p)); rewrite /holds.
       case U: (user_state gs (dst p)) => [u prs bt txp] /= Hbt Hc; apply /eqP.
       have H : btBlockchain bt = btBlockchain (foldl bt_upd bt (blocks_for can_u gs))
         by rewrite D Hc I_ext Hbt.
       rewrite -Hc.
       have Hin : b \in blocks_for can_u gs.
       apply: block_in_queue; [exact S_flight | by rewrite D | exact M | exact V].
       have Hvalid : valid_bt bt by move: (C_valid (dst p)); rewrite /holds U.
       have Hgb : has_gb bt by move: (C_gb (dst p)); rewrite /holds U.
         by rewrite (btBlockchain_seq_same Hvalid Hgb Hin) //.
     (* largest chain *)
     + rewrite /largest_chain /holds /= => u bc.
       rewrite setfsNK; case: ifP => /eqP D; last by apply: I_large.
       rewrite -H_useq /has_chain => /eqP Hc.
       have Hgeq : can_bc >=b btBlockchain (btree (user_state gs (dst p)))
         by apply: (I_large (dst p)); rewrite /has_chain eqxx.
       move: (I_sub (dst p)) Hgeq Hc; rewrite /holds.
       case U: (user_state gs (dst p)) => [id prs bt' txp] /= => Hbt Hgeq Hc.
       have H : can_bc = btBlockchain (foldl bt_upd bt' (blocks_for (dst p) gs))
         by rewrite I_ext Hbt.
       have Hin : b \in blocks_for (dst p) gs.
       apply: block_in_queue; [exact S_flight | done | exact M | exact V].
       subst bc.
       have Hvalid : valid_bt bt' by move: (C_valid (dst p)); rewrite /holds U.
       have Hgb : has_gb bt' by move: (C_gb (dst p)); rewrite /holds U.
         by apply: (btBlockchain_seq_sub_geq Hvalid Hgb Hin Hgeq);left.
     (* cliq property *)
     + move => u /=.
       rewrite setfsNK; case: ifP => /eqP D; last by apply: I_cliq.
       rewrite -H_useq /receive_block_update /= -D.
       move: (I_cliq u) => <-.
         by case: (user_state gs u).
     (* eventual consensus *)
     + rewrite /holds /= => u.
       rewrite setfsNK /blocks_for /=; case: ifP => /eqP D.
       * rewrite -H_useq /receive_block_update /=.
         case U: (user_state gs (dst p)) => [u0 prs0 bt0 txp0] => /=.
         rewrite filter_cat blocks_for_split foldl_undup_split.
         rewrite D relevant_message; [|by move: (C_valid u); rewrite /holds D U/=|by done..].
         move: (I_sub u); rewrite /holds /blocks_for D U /= => <-.
         rewrite -H_peq /=; case: ifP => S //=; rewrite /broadcast_message U /=.
         rewrite irrelevant_broadcast' //=;
                 [by move: (C_uiq (dst p)); rewrite /holds U /=; apply: rem_uniq |
                  move /eqP: S => ->; rewrite mem_rem_uniqF => //].
         by move: (C_uiq (dst p)); rewrite /holds U /=.
         rewrite irrelevant_broadcast' //=;
                 [by move: (C_uiq (dst p)); rewrite /holds U /=; apply: rem_uniq |
                  move: (I_cliq (dst p)); rewrite U /= => ->; apply: notin_rem_peers].
       * rewrite filter_cat blocks_for_split foldl_undup_split.
         move: (I_sub u). rewrite /holds /blocks_for.
         rewrite irrelevant_blkmsg => //; last by apply /eqP => E; apply: D; rewrite E.
         move => Hbt; rewrite -Hbt -H_peq /=.
         case U: (user_state gs (dst p)) => [u0 prs0 bt0 txp0] => /=.
         case: ifP => /eqP S //=.
         ** rewrite S /broadcast_message.
            rewrite irrelevant_broadcast' //=;
              [by move: (C_uiq (dst p)); rewrite /holds U /=; apply: rem_uniq |
              rewrite mem_rem_uniqF => //; by move: (C_uiq (dst p)); rewrite /holds U /=].
         ** rewrite /broadcast_message.
            rewrite relevant_broadcast //=;
            [|by move: (C_uiq (dst p)); rewrite /holds U /=; apply: rem_uniq |
              by move: (I_cliq (dst p)); rewrite U /= => ->;apply: in_rem_peers].
            move: (I_sub (dst p)); rewrite /holds U /=.
            move: (b_in_blocks_for V S_flight M) => Bin Btseq.
            suff Hin : #b b \in can_bt by rewrite /bt_upd btupd_in_noeffect.
              by rewrite Btseq; apply: (foldl_btupd_in_mem_seq) => //;
                 move: (C_valid (dst p)); rewrite /holds U /=.
     (* missing transactions *)
     (* has chain *)  
     + rewrite /holds /=.
       rewrite setfsNK; case: ifP => /eqP D; last by apply: I_chain.
       rewrite -H_useq /receive_block_update.
       move: I_chain; rewrite /holds /has_chain D /= => /eqP.
       move: (I_sub (dst p)); rewrite /holds.
       case U: (user_state gs (dst p)) => [u prs bt txp] /= Hbt Hc; apply /eqP.
       have H: btBlockchain bt = btBlockchain (foldl bt_upd bt (blocks_for can_u gs))
         by rewrite D Hc I_ext Hbt.
       rewrite -Hc.
       have Hin : b \in blocks_for can_u gs.
       apply: block_in_queue; [exact S_flight | done | exact M | exact V].
       have Hvalid : valid_bt bt by move: (C_valid (dst p)); rewrite /holds U.
       have Hgb : has_gb bt by move: (C_gb (dst p)); rewrite /holds U.
         by rewrite (btBlockchain_seq_same Hvalid Hgb Hin) //.
     (* largest chain *)
     + rewrite /largest_chain /holds /= => u bc.
       rewrite setfsNK; case: ifP => /eqP D; last by apply: I_large.
       rewrite -H_useq /has_chain => /eqP Hc.
       have Hgeq : can_bc >=b btBlockchain (btree (user_state gs (dst p)))
         by apply: (I_large (dst p)); rewrite /has_chain eqxx.
       move: (I_sub (dst p)) Hgeq Hc; rewrite /holds.
       case U: (user_state gs (dst p)) => [id prs bt' txp] /= => Hbt Hgeq Hc.
       have H : can_bc = btBlockchain (foldl bt_upd bt' (blocks_for (dst p) gs))
         by rewrite I_ext Hbt.
       have Hin : b \in blocks_for (dst p) gs.
       apply: block_in_queue; [exact S_flight | done | exact M | exact V].
       subst bc.
       have Hvalid : valid_bt bt' by move: (C_valid (dst p)); rewrite /holds U.
       have Hgb : has_gb bt' by move: (C_gb (dst p)); rewrite /holds U.
         by apply: (btBlockchain_seq_sub_geq Hvalid Hgb Hin Hgeq); left.
     (* cliq property *)
     + move => u /=.
       rewrite setfsNK; case: ifP => /eqP D; last by apply: I_cliq.
       rewrite -H_useq /receive_block_update /= -D.
       move: (I_cliq u) => <-.
         by case: (user_state gs u).
     (* eventual consensus *)
     + rewrite /holds /= => u.
       rewrite setfsNK /blocks_for /=; case: ifP => /eqP D.
       * rewrite -H_useq /receive_block_update /=.
         case U: (user_state gs (dst p)) => [u0 prs0 bt0 txp0] => /=.
         rewrite filter_cat blocks_for_split foldl_undup_split.
         rewrite D relevant_message; [|by move: (C_valid u); rewrite /holds D U/=|by done..].
         move: (I_sub u); rewrite /holds /blocks_for D U /= => <-.
         rewrite -H_peq /=; rewrite /broadcast_message U /=.
         rewrite irrelevant_broadcast' //=;
           [by move: (C_uiq (dst p)); rewrite /holds U /=; apply: rem_uniq |
           by move: (I_cliq (dst p)); rewrite U /= => ->; apply: notin_rem_peers].
       * rewrite filter_cat blocks_for_split foldl_undup_split.
         move: (I_sub u). rewrite /holds /blocks_for.
         rewrite irrelevant_blkmsg => //; last by apply /eqP => E; apply: D; rewrite E.
         move => Hbt; rewrite -Hbt -H_peq /=.
         case U: (user_state gs (dst p)) => [u0 prs0 bt0 txp0] => /=.
         case S: (src p == u); move /eqP: S => S.
         ** rewrite S irrelevant_broadcast' //=.
            by move: (C_uiq (dst p)); rewrite /holds U /=; apply: rem_uniq.
            move: (I_cliq (dst p)); rewrite U /= => ->; rewrite mem_rem_uniqF //;
              by apply: rem_uniq; rewrite enum_uniq.
         ** rewrite relevant_broadcast //=;
            [|by move: (C_uiq (dst p)); rewrite /holds U /=; apply: rem_uniq |
             by move: (I_cliq (dst p)); rewrite U /= => ->;apply: in_rem_peers].
            move: (I_sub (dst p)); rewrite /holds U /=.
            move: (b_in_blocks_for V S_flight M) => Bin Btseq.
            suff Hin : #b b \in can_bt by rewrite /bt_upd btupd_in_noeffect.
              by rewrite Btseq; apply: (foldl_btupd_in_mem_seq) => //;
                 move: (C_valid (dst p)); rewrite /holds U /=.
            
  (* Transactions message *)
  - case: ifP => A [H_useq H_peq].
    (* old transactions *)
    apply: sync_no_change; [by rewrite -H_useq..| | by done].
    rewrite -H_peq /blocks_for /emitZero cats0 /= => u.
      by rewrite (irrelevant_message u S_flight); last rewrite M. 
    (* new transactions *)
    apply: sync_no_change; last by done.
    rewrite -H_useq /receive_transactions_update /=.
      by case: (user_state gs (dst p)).  
    rewrite -H_useq /receive_transactions_update /=.
      by case: (user_state gs (dst p)).
    rewrite -H_peq /blocks_for /broadcast_message => u /=.
    case: (user_state gs (dst p)) => id prs _ _.
    rewrite irrelevant_broadcast; last by done.
      by rewrite (irrelevant_message u S_flight); last rewrite M.
      
  (* Requests message *)
  - case => H_useq H_peq.
    apply: sync_no_change; [by rewrite -H_useq..| | by done].
    rewrite -H_peq /blocks_for /response_to_transactions /emitOne /= => u.
    rewrite (irrelevant_message u S_flight); last by rewrite M.
    rewrite filter_cat blocks_for_split /=.
      by case: ifP => //=; rewrite cats0.
      
  (* InternalTransition *)
  move => u int; case => [C_uiq C_valid C_gb] Hallow.
  case P: (proc_int _ _ _) => [us ps] ->.
  case I: int => [ts|]; move: P; rewrite I.
  (* Internal transactions emit *)
  - case => H_useq H_peq.
    apply: sync_no_change; last by done.
    rewrite -H_useq /receive_transactions_update /=.
      by case: (user_state gs u).
    rewrite -H_useq /receive_transactions_update /=.
      by case: (user_state gs u).
    rewrite -H_peq /blocks_for => u' /=.
    rewrite filter_cat blocks_for_split -[emitBroadcast _ _ _]cat0s.
      by rewrite irrelevant_broadcast /=.
      
  (* Internal mine blocks *)
  - rewrite /=. case: (genProof _ _ _); last first.
    (* failing miner *)
    case => H_useq H_peq; rewrite -H_peq /emitZero cat0s.
    rewrite setfs_nupd; by done.
    move => pfv.
    case: ifP => V; last first.
    case => <- <-; rewrite /emitZero cat0s.
      by rewrite setfs_nupd.
    (* successful miner *)
    case: Isync => can_bt [can_bc] [can_u] [I_chain I_large [I_valid [I_gb [I_ext I_good]]] I_cliq I_sub].
    move: V; set new_b := {|
      prev_blk := #b last_blk (btBlockchain (btree (user_state gs u)));
      prop_txs := [seq hashPID t
                  | t <- txpool (user_state gs u)
                    & t
                        \notin [seq t0 <- txpool (user_state gs u)
                               | commTxsValid t0 (btBlockchain (btree (user_state gs u)))]];
      comm_txs := [seq t <- txpool (user_state gs u) | commTxsValid t (btBlockchain (btree (user_state gs u)))];
      proof := pfv |} => V.
    case => H_useq H_peq.
    (* updated canonical block tree is still comlete *)
    have Good : good_bt can_bt.[#b new_b <- new_b].
    rewrite /good_bt => b.
    rewrite inE dom_setf in_fset1U => /orP.
    case => [/eqP /hashB_inj Heq | Hin].
    + subst b.
      move: (btBlockchain_good can_bt) => Gbc.
      have HP : prev_blk new_b = #b last_blk (btBlockchain (btree (user_state gs u))) by done.
      move /andP: V => [Vnew Vall].
      move: (btupd_mint_goodness (C_valid u) (C_gb u) (btBlockchain_good _) Vnew Vall HP); case => HG HV.
      change (good_blockchain (compute_blockchain (bt_upd can_bt new_b) new_b) &&
              valid_blockchain (compute_blockchain (bt_upd can_bt new_b) new_b)).
      rewrite (I_sub u) /= bt_updE foldl_comm /=.
      rewrite good_bt_add_seq_same_chain //;
        [by rewrite HG HV
        |by apply: btupd_validP (C_valid u)
        |by apply: btupd_gbP (C_gb u)].
    + move: (I_good b Hin) => /andP; case => HG HV.
      move: (good_bt_add_block_same_chain new_b I_valid I_gb HG).
        by rewrite /bt_upd => ->; rewrite HG HV.
    (* consider whether the newly mined block contributes to the canonical chain *)
    case T: (btBlockchain (btree us) >b can_bc); last first.
    (* Case 1: new block does not contribute to the canonical chain *)
    move: T => /FCR_ngtT T.
    exists can_bt.[#b new_b <- new_b], can_bc, can_u; split => //.
    (* has chain *)
    + rewrite /holds /=.
      rewrite setfsNK; case: ifP => /eqP E; last by apply: I_chain.
      subst can_u; move: I_chain; rewrite /holds -H_useq /has_chain /= => /eqP E.
      case: T => T; first by rewrite T -H_useq /= eqxx.
      move: E T => <-; rewrite -H_useq /= => contra.
      contradict contra; rewrite -FCR_ngt; apply: btBlockchain_btupd_geq;
        [apply: C_valid | apply: C_gb].
    (* largest chain *)
    + rewrite /largest_chain /holds /= => u' bc'.
      rewrite setfsNK; case: ifP => /eqP E; last by  apply: I_large.
      rewrite -H_useq /has_chain /= => /eqP <-.
        by move: T; rewrite -H_useq /=.
    (* valid block forest and having GenesisBlock *)
    + repeat split; [by apply: btupd_validP => // |  apply: btupd_gbP => // |  | ].
    (* canonical chain is still the main chain of the extended block forest *)
    + subst can_bc.
      move: (btBlockchain_btupd_geq new_b I_valid I_gb); case => // Gt.
      move: (I_sub u); rewrite /holds => Sub.
      move /andP: V => [Vnew Vall].
      have P : (prev_blk new_b = #b last_blk (btBlockchain (btree (user_state gs u)))) by subst new_b.
      contradict Gt; apply: btupd_within => //;
         [by apply: C_valid|by apply: C_gb|by subst new_b|by rewrite -H_useq /= in T|exact Sub].
    (* the extended block forest is still complete *)
    + exact Good.
    (* cliq property *)
    + rewrite /= => u'.
      rewrite setfsNK; case: ifP => /eqP E; last by apply: I_cliq.
        by rewrite -H_useq E /=; apply: I_cliq.
    (* eventual consensus *)
    + rewrite /holds /= => u'.
      rewrite setfsNK; case: ifP => /eqP E.
      * rewrite -H_useq E /blocks_for /=.
        rewrite filter_cat blocks_for_split foldl_undup_split.
        rewrite -H_peq irrelevant_broadcast' /=;
                       [|by apply: C_uiq
                        |by rewrite I_cliq mem_rem_uniqF //; apply: enum_uniq].
        move: (I_sub u); rewrite /holds /blocks_for => ->.    
        change (bt_upd (foldl bt_upd (btree (user_state gs u))
                              (undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u]))) new_b
                = foldl bt_upd (btree (user_state gs u)).[#b new_b <- new_b]
                              (undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u]))).
          by rewrite bt_updE foldl_comm.
      * rewrite /blocks_for /=.
        rewrite filter_cat blocks_for_split foldl_undup_split.
        rewrite -H_peq relevant_broadcast /=;
                       [|by apply: C_uiq
                        |by rewrite I_cliq enumT; apply: rem_in_mem => //; apply: count1_impl_in; apply: enumP
                        |by move /andP: V => [V _]].
        move: (I_sub u'); rewrite /holds /blocks_for => ->.
        change (bt_upd (foldl bt_upd (btree (user_state gs u'))
                              (undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u']))) new_b
                = foldl bt_upd (bt_upd (btree (user_state gs u')) new_b)
                              (undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u']))).
          by rewrite bt_updE foldl_comm.
    (* Case 2: new block contributes to the canonical chain *)
    exists can_bt.[#b new_b <- new_b], (btBlockchain (btree us)), u; split => //.
    (* has chain *)
    + by rewrite /holds /= setfsNK eqxx -H_useq /has_chain /=.
    (* largest chain *)
    + rewrite /largest_chain /holds /= => u' bc'.
      rewrite setfsNK; case: ifP => /eqP E; first by rewrite /has_chain -H_useq /= => /eqP; left.
      rewrite /has_chain -H_useq /= => /eqP <-.
      move: (I_large u' (btBlockchain (btree (user_state gs u')))).
      rewrite /holds /has_chain /= => /(_ (eqxx _)) H.
        by apply: FCR_geq_trans H; right; rewrite -H_useq /= in T.
    (* valid block forest and having GenesisBlock *)
    + repeat split; [by apply: btupd_validP => // | apply: btupd_gbP => // | |].
    (* canonical chain is still the main chain of the extended block forest *)
    + move: (I_sub u); rewrite /holds -H_useq /= => Hbt; subst can_bc.
      rewrite -H_useq /= in T.
      rewrite (btupd_with_new I_valid I_gb _ _ _ _ T Hbt) //;
        [by apply: C_valid|by apply: C_gb].
    (* the extended block forest is still complete *)
    + exact Good.
    (* cliq property *)
    + rewrite /= => u'.
        by rewrite setfsNK; case: ifP => /eqP E; [rewrite E -H_useq | ]; rewrite I_cliq.
    (* eventual consensus *)
    + rewrite /holds /blocks_for /= => u'.
      rewrite setfsNK; case: ifP => /eqP E.
      rewrite -H_useq E /=.
      rewrite filter_cat blocks_for_split foldl_undup_split.
      rewrite -H_peq irrelevant_broadcast' /=;
                     [|apply: C_uiq | rewrite I_cliq mem_rem_uniqF //; apply: enum_uniq].
      move: (I_sub u); rewrite /holds /= => ->.
      change (bt_upd (foldl bt_upd (btree (user_state gs u))
                          (undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u]))) new_b
            = foldl bt_upd (btree (user_state gs u)).[#b new_b <- new_b]
                          (undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u]))).
        by rewrite bt_updE foldl_comm.
      rewrite filter_cat blocks_for_split foldl_undup_split.
      rewrite -H_peq relevant_broadcast /=;
                     [|by apply: C_uiq
                      |by rewrite I_cliq enumT; apply: rem_in_mem => //; apply: count1_impl_in; apply: enumP
                      |by move /andP: V => [V _]].
      move: (I_sub u'); rewrite /holds /blocks_for => ->.
      change (bt_upd (foldl bt_upd (btree (user_state gs u'))
                            (undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u']))) new_b
              = foldl bt_upd (bt_upd (btree (user_state gs u')) new_b)
                            (undup (blocks_for_rec [seq p <- inflight_msg gs | dst p == u']))).
        by rewrite bt_updE foldl_comm.
Qed.

Lemma sync_inv_reachable :
  forall (gs gs': GState),
    sync_inv gs -> reachable_state gs gs' -> sync_inv gs'.
Proof.
  move => gs gs' S R; elim: R S => //.
  - by move => gs1 gs2 s Step Sync; apply: (sync_inv_step Sync Step).
  - move => gs1 gs2 gs3 R12 S12 R23 H23 S1. 
      by apply: (H23 (S12 S1)).
Qed.
  
Lemma final_consensus :
  forall (gs : GState),
    reachable_state initGState gs ->
    (forall (u : UserId), blocks_for u gs == [::]) ->
    exists (bc : Blockchain), largest_chain gs bc /\
                              (forall (u : UserId), holds u gs (has_chain bc)).
Proof.
  move => gs /(sync_inv_reachable sync_initial_state).
    by apply: sync_eventual_consensus.
Qed.
