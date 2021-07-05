From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.finmap Require Import finmap.

From CKB Require Import Types Parameters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fset_scope.
Open Scope fmap_scope.

Lemma hashB_non : forall (b1 b2 : Block),
    b1 != b2 = (#b b1 != #b b2).
Proof.
  move => b1 b2; case B: (b1 == b2); first by move /eqP: B => ->; rewrite eqxx.
  apply /esym => /=; apply /eqP.
  move /eqP in B; contradict B; by move /hashB_inj: B.
Qed.

(* lemmas to deal with rem and cat *)
Lemma mem_split {T : eqType} :
  forall (x : T) (s : seq T), x \in s -> exists s1 s2, s = s1 ++ x :: s2 /\ x \notin s1.
Proof.
  move => x; elim => // h s IH H.
  have Hin : (x \in h :: s) by done.
  move: H; rewrite inE => /orP.
  case E: (x == h); move => [_ | H] //.
  - exists [::], s.
      by move /eqP: E <-; rewrite cat0s.
  - exists [::], s.
      by move /eqP: E <-; rewrite cat0s.
  - move: (IH H) => [s1] [s2] [Heq Hnin].
    exists (h :: s1), (s2).
    rewrite cat_cons Heq; split => //.
    rewrite inE negb_or.
      by rewrite E Hnin.
Qed.

Lemma rem_split {T : eqType} :
  forall (x : T) (s : seq T),
    x \in s -> exists s1 s2, s = s1 ++ x :: s2 /\ x \notin s1 /\ rem x s = s1 ++ s2.
Proof.
  move => x s H.
  move: (mem_split H) => [s1] [s2] [Heq Hnin].
  exists s1, s2.
  repeat split => //.
  rewrite Heq; clear s H Heq.
  elim: s1 Hnin => [|h s1 IH] Hnin.
    by rewrite !cat0s /= eqxx.
  move: Hnin. rewrite inE negb_or => /andP [Hneq Hnin].
  rewrite /=. rewrite eq_sym.
  case E: (x == h); first by rewrite E in Hneq.
    by rewrite (IH Hnin).
Qed.

Lemma last_in_nil {T : eqType} :
  forall (s : seq T) (t : T),
    last t s \in s = (s != [::]).
Proof. elim => [|h s IH] t //=; by rewrite mem_last. Qed.

Lemma last_impl_mem {T : eqType} :
  forall (s : seq T) (x t : T),
    x != t ->
    x = last t s -> x \in s.
Proof.
  elim => [|h s IH] x t N /=.
  by move => H; subst x; rewrite eqxx in N.
  rewrite inE; move => /IH.
  case: (x == h) => H //=.
    by move: (H (erefl _)).
Qed.

Lemma rcons_in {T : eqType} :
  forall (s : seq T) (x y : T),
    x \in rcons s y = (x \in s) || (x == y).
Proof.
  elim => [|a s IH] x y /=; first by rewrite mem_seq1.
    by rewrite inE IH inE orbA.
Qed.

Lemma in_seq_all {T : eqType} :
  forall (s : seq T) (a : pred T) (t : T),
    t \in s ->
    all a s -> a t.
Proof.
  elim => [|x s IH] a t //=.
  rewrite inE => /orP; case => [/eqP E | H].
    by rewrite E => /andP; case.
    by move /andP => [_ A]; apply: IH.
Qed.

(* FCR lemmas *)
Section FCR.

Variables b1 b2 b3 : Blockchain.
  
Lemma FCR_neg :
    b1 >b b2 -> b2 >b b1 = false.
Proof.  
  move => H; apply /negP => contra.
    by apply: FCR_nrefl (FCR_trans H contra).
Qed.
    
Lemma FCR_ngeq :
    b1 >b b2 <-> ~ b2 >=b b1.
Proof.
  split.
  move => H [P | P].
  subst b2; apply: FCR_nrefl H.
    by apply: FCR_nrefl (FCR_trans H P).
  move: (FCR_rel b1 b2); case => //; case; auto.
Qed.

Lemma FCR_ngt :
    b1 >=b b2 <-> ~ b2 >b b1.
Proof.
  split.
  move => [H | H].
  subst b1; apply: FCR_nrefl.
    by move => P; move: (FCR_trans H P) => /FCR_nrefl.
    by move: (FCR_rel b1 b2); tauto.
Qed.

Lemma FCR_geq_trans : 
    b1 >=b b2 -> b2 >=b b3 -> b1 >=b b3.
Proof.
  case => H; case => P.
    by left; subst b1 b2.
    by right; subst b1.
    by right; subst b2.
    by right; apply: FCR_trans; [exact H|exact P].
Qed.

Lemma FCR_gt_geq_trans :
    b1 >b b2 -> b2 >=b b3 -> b1 >b b3.
Proof.
  move => G; case => H.
    by subst b2.
    by apply: (FCR_trans G H).
Qed.

Lemma FCR_geq_gt_trans :
    b1 >=b b2 -> b2 >b b3 -> b1 >b b3.
Proof.
  case => H.
    by subst b1.
    by move => P; apply: (FCR_trans H P).
Qed.

Lemma FCR_ngtT :
    b2 >b b1 = false <-> b1 >=b b2.
Proof.
  rewrite FCR_ngt; split; first by move => ->.
    by move => /negP /negPf.
Qed.

End FCR.

(* blocktree validity and blockchain validity *)
Section validity.
  
(* a block tree is valid if the key is always the hash of the value *)
Definition valid_bt (bt : BlockTree) :=
  forall (h : HashValue) (b : Block), bt.[? h] = Some b -> #b b = h.

(* a block is valid if 
   - 1. its proof is valid (VAF b bc) 
   -2. commitment transactions are all valid (all ... (comm_txs b)) *)
Definition valid_block (b : Block) (bc : Blockchain) :=
  VAF b && all [pred t | commTxsValid t bc] (comm_txs b).

(* a blockchain is valid if every block is valid wrt. its previous chain *)
Fixpoint valid_blockchain_rec (bc pref : Blockchain) :=
  if bc is b :: bc' then
    [&& VAF b && all [pred t | commTxsValid t pref] (comm_txs b) & valid_blockchain_rec bc' (rcons pref b)]
  else true.

Definition valid_blockchain (bc : Blockchain) :=
  valid_blockchain_rec bc [::].

Lemma validE (bt : BlockTree) (h : HashValue):
    forall P : h \in bt, valid_bt bt -> #b bt [`P] = h.
Proof. by rewrite /valid_bt => P V; move: (in_fnd P) => /V. Qed.

Lemma valid_bt_in_mem :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt ->
    #b b \in bt -> bt.[? #b b] = Some b.
Proof.
  move => bt b V I.
  move: (in_fnd I) => H.
  move: (V _ _ H) => /hashB_inj E.
    by rewrite H E.
Qed.

Lemma btupd_validP :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt ->
    valid_bt bt.[#b b <- b].
Proof.
  move => bt b Hv h k.
  rewrite fnd_set; case: ifP => /eqP H; last by apply: Hv.
  case => Heq.
    by rewrite H -Heq.
Qed.

Lemma btrem_validP :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt ->
    valid_bt bt.[~ #b b].
Proof.
  move => bt b V h b' H. unfold valid_bt in V.
  move: (H); rewrite fndSomeP; case => X _.
  have I : h \in bt.
  move: X; rewrite inE domf_rem inE => /andP.
    by case => _ I; rewrite I.
  apply: V; rewrite -H fnd_restrict.
    by rewrite -domf_rem X.
Qed.

Lemma btupd_noeffect_in :
  forall (bt : BlockTree) (b : Block),
    bt = bt.[#b b <- b] -> #b b \in bt.
Proof.
  move => bt b; rewrite -fmapP => H.
  move: (H (#b b)); rewrite fnd_set eqxx.
    by rewrite fndSomeP; case.
Qed.

Lemma btupd_in_noeffect :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt ->
    #b b \in bt -> bt.[#b b <- b] = bt.
Proof.
  move => bt b V I.
  rewrite -fmapP => k.
  rewrite fnd_set; case: ifP => // /eqP E.
  subst k; symmetry.
  move: (in_fnd I) => /V /hashB_inj.
    by rewrite in_fnd => ->.
Qed.

Lemma init_valid_blockchain :
  valid_blockchain [:: GenesisBlock].
Proof.
  rewrite /valid_blockchain /=.
  rewrite VAF_init /=; apply /andP; split => //.
    by move: GB_nil => [-> _] /=.
Qed.

Lemma valid_blockchain_rconsE :
  forall (bc pre : Blockchain) (b : Block),
    valid_blockchain_rec (rcons bc b) pre
    = valid_blockchain_rec bc pre && valid_blockchain_rec [:: b] (pre ++ bc).
Proof.
  elim => [|a bc IH] pre b; first by rewrite cats0.
  rewrite rcons_cons [valid_blockchain_rec (a :: rcons bc b) pre]/=.
  rewrite [valid_blockchain_rec (a :: bc) pre]/=.
    by rewrite IH cat_rcons andbA.
Qed.  

Lemma valid_blockchain_rcons :
  forall (bc : Blockchain) (b : Block),
    VAF b -> all [pred t | commTxsValid t bc] (comm_txs b) ->
    valid_blockchain bc -> valid_blockchain (rcons bc b).
Proof.
  move => bc b V A; rewrite /valid_blockchain.
    by rewrite valid_blockchain_rconsE /= V A => ->.
Qed.

End validity.

(* blocktree having genesisblock *)
Section genesisblock.

(* the block tree has genesis block *)
Definition has_gb (bt : BlockTree) :=
  bt.[? #b GenesisBlock] = Some GenesisBlock.

Definition get_block (bt :BlockTree) (h : HashValue) :=
  if bt.[? h] is Some b then b else GenesisBlock.

Lemma get_blockE :
  forall (bt : BlockTree) (b : Block),
    get_block bt.[#b b <- b] (#b b) = b.
Proof. by move => bt b; rewrite /get_block fnd_set eqxx. Qed.

Lemma get_blockNE :
  forall (bt : BlockTree) (b : Block),
    #b b \notin bt -> get_block bt (#b b) = GenesisBlock.
Proof. by move => bt b Hb; rewrite /get_block not_fnd. Qed.

Lemma btupd_gbP :
  forall (bt : BlockTree) (b : Block),
  has_gb bt ->
  has_gb bt.[#b b <- b].
Proof.
  move => bt b Hgb; rewrite /has_gb.
  rewrite fnd_set; case: ifP => //.
    by move => /eqP /hashB_inj ->.
Qed.

Lemma btrem_gbP :
  forall (bt : BlockTree) (b : Block),
    has_gb bt -> b == GenesisBlock = false->
    has_gb bt.[~ #b b].
Proof.
  move => bt b G.
  move => /negbT; rewrite hashB_non => /negPf H.
  move: G; rewrite /has_gb fndSomeP; case => X Y.
  rewrite /has_gb in_fnd.
    by rewrite domf_rem inE in_fset1 eq_sym H X.
    by move => P; rewrite getf_restrict Y.
Qed.

Lemma has_gb_n1 :
  forall (bt : BlockTree),
    has_gb bt -> exists n, #|` domf bt| = n.+1.
Proof.
  rewrite /has_gb => bt.
  rewrite fndSomeP; case => H _.
  move: (cardfsD1 (#b GenesisBlock) (domf bt)); rewrite H add1n => X.
    by exists  #|` domf bt `\ #b GenesisBlock|.
Qed.

End genesisblock.

(* lemmas about btupd *)
Section btupd.

Definition bt_upd (bt : BlockTree) (b : Block) := bt.[#b b <- b].

Lemma btupd_dupE :
  forall (bt : BlockTree) (b : Block),
    bt_upd (bt_upd bt b) b = bt_upd bt b.
Proof.
  move => bt b; rewrite /bt_upd.
  rewrite -fmapP => k.
  rewrite !fnd_set; case: ifP => //=.
    by move => ->.
Qed.

Lemma bt_updC :
  forall (bt : BlockTree) (b1 b2 : Block),
    bt_upd (bt_upd bt b1) b2 = bt_upd (bt_upd bt b2) b1.
Proof.
  move => bt b1 b2; rewrite /bt_upd.
  rewrite -fmapP => k.
  rewrite !fnd_set; case: ifP; case: ifP => //=.
    by move /eqP => -> /eqP /hashB_inj ->.
Qed.

Lemma bt_updE :
  forall (bt : BlockTree) (b : Block),
    bt_upd bt b = foldl bt_upd bt [::b].
Proof. by done. Qed.

Lemma foldl_comm :
  forall (bt : BlockTree) (s1 s2 : seq Block),
    foldl bt_upd (foldl bt_upd bt s1) s2 = foldl bt_upd (foldl bt_upd bt s2) s1.
Proof.
  move => bt s1; elim: s1 bt => [|b s1 IH] bt s2 //=.
  suff H2 : bt_upd (foldl bt_upd bt s2) b = foldl bt_upd (bt_upd bt b) s2
    by rewrite H2 -IH.
  elim: s2 bt => [|h s2 IH2] bt //=.
  by rewrite IH2 bt_updC.
Qed.

Lemma foldl_btupd_validP :
  forall (bs : seq Block) (bt : BlockTree),
    valid_bt bt -> valid_bt (foldl bt_upd bt bs).
Proof.
  elim /last_ind => [|bs b IH] bt V //.
  rewrite -cats1 foldl_cat foldl_comm /=.
    by apply: IH; apply: btupd_validP.
Qed.

Lemma foldl_btupd_gbP :
  forall (bs : seq Block) (bt : BlockTree),
    has_gb bt -> has_gb (foldl bt_upd bt bs).
Proof.
  elim /last_ind => [|bs b IH] bt G //.
  rewrite -cats1 foldl_cat foldl_comm /=.
    by apply: IH; apply: btupd_gbP.
Qed.

Lemma foldl_block_forE :
  forall (s : seq Block) (bt : BlockTree),
    foldl bt_upd bt (undup s) =
    foldl bt_upd bt s.
Proof.
  elim => [|b s IH] bt //=.
  case: ifP => Hin //=.
  rewrite IH.
  rewrite bt_updE foldl_comm /= {2}/bt_upd.
  rewrite -fmapP => k.
  rewrite fnd_set.
  case: ifP => /eqP E //=.
  subst k; clear IH.
  elim: s Hin bt => [|h s IH] Hin bt //=.
  move: Hin; rewrite inE => /orP; move => [/eqP H | H]; last by apply: IH.
  subst h.
  by rewrite bt_updE foldl_comm /= fnd_set eqxx.
Qed.
    
Lemma foldl_undup_split :
  forall (bt : BlockTree) (s1 s2 : seq Block),
    foldl bt_upd bt (undup (s1 ++ s2)) =
    foldl bt_upd (foldl bt_upd bt (undup s1)) (undup s2).
Proof.
  move => bt s1 s2; rewrite !foldl_block_forE.
  elim: s1 s2 bt => [|b s1 IH] s2 bt //=.
Qed.

Lemma foldl_upd_within :
  forall (bt : BlockTree) (bs bf af : seq Block) (b : Block),
  valid_bt bt ->
  bs = bf ++ b::af ->
  foldl bt_upd (bt_upd bt b) (af ++ bf) =
  foldl bt_upd bt bs.
Proof.
  move => bt bs bf af b Hv Heq.
  rewrite Heq !foldl_cat /= !bt_updE.
  rewrite foldl_comm.
    by rewrite [foldl bt_upd _ bf]foldl_comm.
Qed.

Lemma btupd_gbP_foldl :
  forall (bs : seq Block) (bt : BlockTree),
    has_gb bt ->
    has_gb (foldl bt_upd bt bs).
Proof.
  elim => [|b bs IH] bt G //=.
    by apply: IH; apply: btupd_gbP.
Qed.

Lemma btupd_validP_foldl :
  forall (bs : seq Block) (bt : BlockTree),
    valid_bt bt ->
    valid_bt (foldl bt_upd bt bs).
Proof.
  elim => [|b bs IH] bt V //=.
    by apply: IH; apply: btupd_validP.
Qed.

Lemma foldl_btupd_in_mem :
  forall (bs : seq Block) (bt : BlockTree) (b : Block),
    #b b \in bt -> #b b \in (foldl bt_upd bt bs).
Proof.
  elim => [|h bs IH] bt b I //=.
  rewrite bt_updE foldl_comm /= [bt_upd _ h]/bt_upd.
  case E: (#b b == #b h); rewrite inE.
  move /eqP: E => E; rewrite -E.
    by rewrite inE fset11.
  rewrite inE; apply /orP; right.
    by apply: IH.  
Qed.
    
Lemma foldl_btupd_in_mem_same :
  forall (bs : seq Block) (bt : BlockTree) (h : HashValue),
    valid_bt bt ->
    h \in bt -> (foldl bt_upd bt bs).[? h] = bt.[? h].
Proof.
  elim => [|b bs IH] bt h V I //=.
  rewrite bt_updE foldl_comm.
  change ((foldl bt_upd bt bs).[#b b <- b].[? h] = bt.[? h]).
  rewrite fnd_set.
  case: ifP => /eqP E; last by apply: IH.
  subst h.
    by rewrite valid_bt_in_mem.
Qed.

Lemma foldl_btupd_in_noeffect :
  forall (bs : seq Block) (bt : BlockTree),
    valid_bt bt ->
    all [pred b | #b b \in bt] bs -> foldl bt_upd bt bs = bt.
Proof.
  elim => [|b bs IH] bt V //=.
  move /andP => [I A]; rewrite {2}/bt_upd.
  move: (btupd_in_noeffect V I) => ->.
  apply: IH => //.
Qed.

Lemma foldl_btupd_noeffect_cons :
  forall (bs : seq Block) (b : Block) (bt : BlockTree),
    valid_bt bt ->
    bt = foldl bt_upd (bt_upd bt b) bs -> bt = foldl bt_upd bt bs.
Proof.
  move => bs b bt V.
  rewrite bt_updE foldl_comm /= [bt_upd _ b]/bt_upd.
  rewrite -fmapP => P.
  rewrite -fmapP => k.
  case E: (k == #b b); last first.
  - by rewrite P fnd_set E.
  - move /eqP: E => E. subst k.
    move: (P (#b b)); rewrite fnd_set eqxx.
    rewrite fndSomeP. case => X E.
    move: (foldl_btupd_in_mem bs X) => I.
    move: (in_fnd I) => ->.
    rewrite -(foldl_btupd_in_mem_same bs V X).
      by apply: in_fnd.
Qed.

Lemma foldl_btupd_noeffect_in_mem :
  forall (bs : seq Block) (b : Block) (bt : BlockTree),
    valid_bt bt ->
    bt = foldl bt_upd (bt_upd bt b) bs -> #b b \in bt.
Proof.
  elim => [|b' bs IH] b bt V //=.
    by apply: btupd_noeffect_in.
  rewrite bt_updC.
  change (bt = foldl bt_upd (bt_upd bt b') (b :: bs) -> #b b \in bt) => H.
  move: (foldl_btupd_noeffect_cons V H) => /=.
    by apply: IH.
Qed.    
  
Lemma foldl_btupd_noeffect :
  forall (bs : seq Block) (bt : BlockTree),
    valid_bt bt ->
    bt = foldl bt_upd bt bs -> all [pred b | #b b \in bt] bs.
Proof.
  elim => [|b bs IH] bt V E //=.
  move: (foldl_btupd_noeffect_cons V E) => H.
  apply /andP; split; last by apply: IH.
    by apply: foldl_btupd_noeffect_in_mem E.
Qed.

Lemma foldl_btupd_in_mem_seq :
  forall (bs : seq Block) (b : Block) (bt : BlockTree),
    valid_bt bt ->
    b \in bs -> #b b \in foldl bt_upd bt bs.
Proof.   
  elim => [|b' bs IH] b bt V //.
  rewrite inE => /orP; case => [/eqP E | H].
  - subst b' => /=.
    rewrite bt_updE foldl_comm /= [bt_upd _ b]/bt_upd.
      by rewrite inE /= inE fset11.
  - rewrite /= bt_updE foldl_comm /=.
    move: (IH _ _ V H).
      by rewrite bt_updE => /(foldl_btupd_in_mem [:: b']).
Qed.

Lemma foldl_btupd_last :
  forall (bt : BlockTree) (bs : seq Block) (b : Block),
    foldl bt_upd bt (rcons bs b) = foldl bt_upd bt.[#b b <- b] bs.
Proof.
  move => bt bs b.
  by rewrite -cats1 foldl_cat foldl_comm /=.
Qed.

End btupd.

Section take_better.

Definition take_better_bc bc2 bc1 :=
  if (bc2 >b bc1) then bc2 else bc1.

Lemma take_better_geq :
  forall (bcs : seq Blockchain) (bc : Blockchain),
    foldr take_better_bc bc bcs >=b bc.
Proof.
  elim => [|bc' bcs IH] bc /=; first by left.
  rewrite {1 3}/take_better_bc; case: ifP => B; case: (IH bc).
  - by move => <-; right.
  - by move => H; right; apply: (FCR_trans B H).
  - by move => ->; left.
  - by move => G; right.
Qed.

Lemma take_betterP (c bc1 bc2 : Blockchain) :
  bc1 >=b bc2 ->
  take_better_bc c bc1 >=b take_better_bc c bc2.
Proof.
  case => H; first by rewrite H; left.
  rewrite /take_better_bc.
  case B: (c >b bc1); first by move: (FCR_trans B H) => ->; left.
  case: ifP => P; by [rewrite -FCR_ngtT | right].
Qed.

Lemma foldr_take_betterC :
  forall (bcs1 bcs2 : seq Blockchain) (bc : Blockchain),
    foldr take_better_bc bc (bcs1 ++ bcs2) =
    foldr take_better_bc bc (bcs2 ++ bcs1).
Proof.
  elim => [|c bcs1 IH] bcs2 bc /=; first by rewrite cats0.
  rewrite -cat1s catA -IH catA.
  clear IH.
  elim: (bcs1 ++ bcs2) bc => [|c' bcs IH] bc //=.
  rewrite -IH {1 2 4 5}/take_better_bc.
  repeat case: ifP => //.
    by move => _ C1 _ C2; move: (FCR_trans C1 C2) => /FCR_nrefl.
    by move => /FCR_ngtT Geq Gt _; move: (FCR_gt_geq_trans Gt Geq) => C1 C2;
       move: (FCR_trans C1 C2) => /FCR_nrefl.
    by move => _ ->.
    by move => C1 C2; move: (FCR_trans C2 C1) => -> .
    by move => _ /FCR_ngtT; case => C1 // _ /FCR_ngtT; case => C2 //;
       move: (FCR_trans C1 C2) => /FCR_nrefl.
    by move => _ ->.
    by move => _ ->.
Qed.

Lemma foldr_take_betterE (bs : seq Blockchain) (c bc : Blockchain) :
  bc \in bs ->
  take_better_bc bc (foldr take_better_bc c bs) = foldr take_better_bc c bs.
Proof.
  move => /mem_split [s1] [s2] [H Nin]; subst bs.
  rewrite foldr_take_betterC cat_cons /=.
  set x := foldr take_better_bc c (s2 ++ s1); rewrite /take_better_bc.
  case: ifP; case: ifP => //.
    by move => ->.
Qed.

Lemma perm_foldr_take_better :
  forall (bs1 bs2 : seq Blockchain) (c : Blockchain),
    perm_eq bs1 bs2 ->
    foldr take_better_bc c bs1 = foldr take_better_bc c bs2.
Proof.
  elim => [|bc bs1 IH] bs2 c; first by rewrite perm_sym => /perm_nilP -> /=.
  move => P; have I: bc \in bs2 by move /perm_mem: P => /(_ bc); rewrite inE eqxx /= => <-.
  move: (perm_to_rem I) => /(perm_trans P); rewrite perm_cons => H.
  move: (IH _ c H); rewrite /= => ->.
  clear P H IH bs1.
  elim: bs2 bc c I => [|h bs IH] bc c I //=.
  case E: (bc == h); first by move /eqP: E => ->; rewrite eqxx.
  move: I; rewrite inE E eq_sym E /= => I.
  move: (IH bc c I) => <-; set x := foldr take_better_bc c (rem bc bs).
  rewrite /take_better_bc; case: ifP; case: ifP => H1 H2.
  - by rewrite (FCR_trans H2 H1); move: H2 => /FCR_neg ->.
  - move: H1; rewrite FCR_ngtT H2; case.
     by move: H2 => /FCR_neg F <-; rewrite F.
     by move => /(FCR_trans H2) H3; move: H3 => /FCR_neg ->.
  - case B: (bc >b x). 
    move: H2 => /FCR_ngtT; case; first by move => ->; move: (@FCR_nrefl bc) => /negP /negPf ->.
      by move => ->.
      by rewrite H1.
  - by rewrite H2 H1.
Qed.

Lemma subset_take_better_geq (bs1 bs2 : seq Blockchain) (c : Blockchain) :
  {subset bs1 <= bs2} ->
  foldr take_better_bc c bs2 >=b foldr take_better_bc c bs1.
Proof.
  rewrite /sub_mem; elim: bs1 bs2 => [|bc bs1 IH] bs2 S /=; first by apply: take_better_geq.
  have Hin: bc \in bs2 by move: (mem_head bc bs1) => /S.
  case B: (bc \in bs1).
  - have S': forall x, x \in bs1 -> x \in bs2.
    move => x I; have: x \in bc :: bs1 by rewrite in_cons I orbC.
      by move => /S.
      by move: (IH _ S') => Geq; rewrite foldr_take_betterE.
  - move: (rem_split Hin) => [s1] [s2] [E1 [Nin E2]].
    have S': forall x, x \in bs1 -> x \in rem bc bs2.
    move => x I; have: x \in bc :: bs1 by rewrite in_cons I orbC.
    move => /S; have: (x == bc) = false.
    move /negP in B; apply /eqP; contradict B; by subst bc.
    rewrite E2 E1 !mem_cat => F; case /orP; first by move => ->.
      by rewrite inE F /= orbC => ->.
    move: (IH _ S') => Geq.
    rewrite E2 in Geq.
    rewrite E1 foldr_take_betterC cat_cons /=.
      by apply: take_betterP; rewrite foldr_take_betterC.
Qed.

Lemma foldr_take_better_in :
  forall (bcs : seq Blockchain) (bc : Blockchain),
    foldr take_better_bc bc bcs = bc \/ foldr take_better_bc bc bcs \in bcs.
Proof.
  elim => [|c bcs IH] bc //=; first by left.
  rewrite {1 3}/take_better_bc; case: ifP; first by rewrite inE eqxx; right.
  move => /FCR_ngtT; case; first by move => ->; rewrite inE eqxx; right.
  specialize (IH bc); case: IH; first by left.
    by rewrite inE orbC => ->; right.
Qed.
  
Lemma best_element_in :
  forall (bc bc' : Blockchain) (bs1 bs2 : seq Blockchain),
    bc >b [:: GenesisBlock] ->
    bc >b foldr take_better_bc [:: GenesisBlock] (bs1 ++ bs2) ->
    bc \in bs1 ++ bc' :: bs2 ->
           bc = foldr take_better_bc [:: GenesisBlock] (bs1 ++ bc' :: bs2).
Proof.
  move => bc bc' bs1 bs2 G Gt In.
  have H : forall c, c \in bs1 ++ bs2 -> bc >b c.
  - elim: (bs1 ++ bs2) Gt => [|c bs IH] Gt c' //.
    move: Gt; rewrite /= {1}/take_better_bc /=.
    case: ifP => H1 H2.
    move: (FCR_trans H2 H1) => /IH /(_ c') => H.
    rewrite inE; case /orP => [/eqP E | I]; by [subst c'|apply: H I].
    rewrite inE; case /orP => [/eqP E | I]; last by apply: IH H2 c' I.
    move /FCR_ngtT: H1; case => H; first by subst c c'.
      by subst c'; apply: FCR_trans H2 H.
  have [H1 H2] : (forall z, z \in bs1 -> bc >b z) /\
                 (forall z, z \in bs2 -> bc >b z).
  - split => z I; move: (H z); rewrite mem_cat I /=; first by move /(_ is_true_true).
      by rewrite orbC /=; move /(_ is_true_true).
  clear H.
  have E : bc = bc'.
  - suff C: bc \in bc' :: bs2.
    + elim: (bs2) C H2 => [|c bs IH]; first by rewrite inE => /eqP ->.
      rewrite inE; case/orP; first by move /eqP => ->.
        by move => H /(_ bc H) /FCR_nrefl.
    elim: (bs1) H1 In => [|c bs IH] H1.
    rewrite inE; case/orP; first by move => ->.
      by move => ->; rewrite orbC.
    rewrite mem_cat; case/orP => //.
      by move => /H1 /FCR_nrefl.
  subst bc'; clear In Gt.
  suff C: bc = foldr take_better_bc [:: GenesisBlock] (bc :: bs2).
  rewrite -[bc :: bs2]cat1s foldr_cat -C => {C}.
  elim: bs1 H1 => [|c bs1 IH] H1 //=.
  rewrite {1}/take_better_bc; case: ifP => H; last first.
    by apply: IH => z I; apply: H1; rewrite inE I orbC.
  move: (H1 c); rewrite inE eqxx => /(_ is_true_true).
  move: (take_better_geq bs1 bc); case => E.
    by move: H; rewrite E => C1 C2; move: (FCR_nrefl (FCR_trans C1 C2)).
    by move: (FCR_trans H E) => C1 C2; move: (FCR_nrefl (FCR_trans C1 C2)).
  clear bs1 H1.
  rewrite /= {1}/take_better_bc; case: ifP => Geq //.
  move /FCR_ngtT: Geq; case => Gt //.
  case: (foldr_take_better_in bs2 [:: GenesisBlock]) => E.
    by rewrite E in Gt; move: (FCR_trans Gt G) => /FCR_nrefl.
  move: (H2 _ E) => contra.
    by move: (FCR_trans contra Gt) => /FCR_nrefl.
Qed.

End take_better.

Section hash_chain.

Fixpoint hash_blockchain_rec (bc : Blockchain) (b : Block) :=
  match bc with
  | [::] => true
  | b' :: bc => (prev_blk b' == #b b) && hash_blockchain_rec bc b'
  end.

Definition hash_blockchain (bc : Blockchain) :=
  match bc with
  | [::] => true
  | b :: bc => hash_blockchain_rec bc b
  end.

Lemma hashchain_rcons :
  forall (bc : Blockchain) (b : Block),
    prev_blk b = #b last_blk bc->
    hash_blockchain bc ->
    hash_blockchain (rcons bc b).
Proof.
  elim => [|a bc IH] b //.
  rewrite rcons_cons /=.
  case: bc IH => [|c bc] IH /=.
    by rewrite /last_blk /= => ->; rewrite eqxx.
  rewrite /last_blk !last_cons /= in IH *.
    by move => H /andP [P Q]; rewrite IH // P.
Qed.
    
Lemma hashchain_tail :
  forall (bc : Blockchain) (b : Block),
  hash_blockchain (b :: bc) ->
  hash_blockchain bc.
Proof. by move => bc b; case: bc=>//= a bc /andP [P] ->; case: bc. Qed.

Lemma hash_chain_tail2 :
  forall (bc : Blockchain) (a b : Block),
  hash_blockchain ([:: a, b & bc]) ->
  prev_blk b = #b a.
Proof.
  case => [|c bc] /=; first by move => a b /andP => [[]] /eqP ->.
    by move => a b /and3P [] /eqP ->.
Qed.

Lemma hashchain_uniq_hash_nocycle :
  forall (bc : Blockchain) (b : Block),
  hash_blockchain (b :: bc) ->
  uniq (map hashB (b :: bc)) ->
  (forall c, c \in bc -> prev_blk c != #b last_blk (b :: bc)).
Proof.
  elim => [|a bc IH] b H U c //.
  rewrite inE => /orP; case; last first.
  have U' : uniq [seq #b i | i <- [:: a & bc]].
    by move: U => /= /and3P; case; rewrite inE negb_or => /andP [] _ _ -> ->.
  move => /(IH a (hashchain_tail H) U' c).
    by rewrite /last_blk.
  move /eqP => Eq; subst c.
  move: H => /= /andP [/eqP H1 H2]; rewrite H1.
  move: U => /= /and3P; case; rewrite inE negb_or => /andP [H3 H4] H5 H6.
  rewrite /last_blk !last_cons.
  suff Hsuff : b \in bc = false.
  apply /eqP => /hashB_inj; move /negP in Hsuff.
  contradict Hsuff.
  have N : b != a by apply /eqP => E; subst a; move: H3; rewrite eqxx.
    by apply: last_impl_mem Hsuff => //.
  apply /negP => N; move /negP in H4.
  contradict H4; by apply: map_f.
Qed.

End hash_chain.

Section compute_blockchain.

(* a good blockchain should has genesis block as its first block *)
Definition good_blockchain (bc : Blockchain) :=
  if bc is b :: _ then b == GenesisBlock else false.

(* compute blockchain *)
Fixpoint compute_blockchain_rec (bt : BlockTree) (b : Block) (remdom : {fset HashValue}) (n : nat) :=
  if (#b b) \in remdom then
    if (#b b) \in bt then
      let rest := remdom `\ (#b b) in  (* remove hash of b from remaining *)
      if n is n'.+1 then
        match bt.[? (prev_blk b)] with
        | None => [:: b]    (* prev block not in bc means gap *)
        | Some prev =>
          if b == GenesisBlock then [:: b] else
            rcons (nosimpl (compute_blockchain_rec bt.[~ #b b] prev rest n')) b
        end
      else [::] (* n is 0 means all blocks are visited *)
    else [::]
  else [::]     (* hash of b not in remaining dom means loop *).

Definition compute_blockchain (bt : BlockTree) (b : Block) :=
  compute_blockchain_rec bt b (domf bt) (size (domf bt)).

Definition bc_fun (bt : BlockTree) :=
  fun (x : HashValue) =>
    [eta take_better_bc (([eta compute_blockchain bt] \o [eta get_block bt]) x)].

(* we call a block tree is good if
   - 1. every blockchain has genesis block as its head
   - 2. all commitment transactions of each blockchain are valid 
   this implies that it is actually a `tree' and all transactions are valid *)
Definition good_bt (bt : BlockTree) :=
  forall b, #b b \in bt ->
                     good_blockchain (compute_blockchain bt b) && valid_blockchain (compute_blockchain bt b).

(* get all blockchains from a block tree *)
Definition all_blockchains (bt : BlockTree) :=
  [seq compute_blockchain bt b | b <- [seq get_block bt k | k <- domf bt]].

Definition good_blockchains (bt : BlockTree) :=
  [seq c <- all_blockchains bt | good_blockchain c && valid_blockchain c].

Lemma compute_blockchain_gb :
  forall (bt : BlockTree) dom n,
  has_gb bt -> #b GenesisBlock \in dom ->
  compute_blockchain_rec bt GenesisBlock dom n.+1 = [:: GenesisBlock].
Proof.
  move => bt dom n G I.
  rewrite /= I.
  move: G; rewrite /has_gb fndSomeP; case => H _.
  by rewrite H GB_hash in_fnd eqxx.
Qed.

Lemma good_blockchain_geq_gb :
  forall (bc : seq Block),
    good_blockchain bc -> bc >=b [:: GenesisBlock].
Proof.
  move => bc; rewrite /good_blockchain.  
  case: bc => [|b bc] //.  
  move => /eqP E; rewrite E.
  case: bc => [|b' bc]; first by left.
  right; rewrite -cat1s.
    by apply: FCR_ext. 
Qed.

Lemma good_bt_good_blockchain :
  forall (bt : BlockTree) (b : Block),
    good_bt bt ->
    #b b \in bt -> good_blockchain (compute_blockchain bt b).
Proof.
  move => bt b; rewrite /good_bt.
    by move => /(_ b) H /H /andP [V _].
Qed.

Lemma good_bt_valid_blockchain :
  forall (bt : BlockTree) (b : Block),
    good_bt bt ->
    #b b \in bt -> valid_blockchain (compute_blockchain bt b).
Proof.
  move => bt b; rewrite /good_bt.
    by move => /(_ b) H /H /andP [_ V].
Qed.
    
Lemma good_bt_add_block_notwithin :
  forall (bt : BlockTree) (b' : Block),
    good_bt bt -> has_gb bt ->
    #b b' \notin bt ->
    (forall b : Block, #b b \in bt -> prev_blk b != #b b').
Proof.
  move => bt b' G H Nin b In.
  apply /eqP => E.
  move: (good_bt_good_blockchain G In); rewrite /compute_blockchain /compute_blockchain_rec.
  move: (cardfsD1 (#b b) (domf bt)).
  set bt' := bt.[~ #b b].
  set remdom' := domf bt `\ #b b.
  have D : domf bt' = remdom' by rewrite domf_restrict fsetIDAC fsetIid.
  rewrite In /= add1n => S.
  rewrite S In E not_fnd //.
  rewrite /= => /eqP contra.
  move: GB_hash; rewrite -contra E => /hashB_inj F.
    by subst b'; move: In Nin => ->.
Qed.

Lemma compute_blockchain_ext :
  forall (bt : BlockTree) (a b : Block) (n : nat) (dom : {fset HashValue}),
  valid_bt bt ->
  dom = domf bt -> n = #|` domf bt| -> #b a \notin bt ->
  exists bs : seq Block,
    bs ++ compute_blockchain_rec bt b dom n =
    compute_blockchain_rec bt.[#b a <- a] b (domf bt.[#b a <- a]) #|` domf bt.[#b a <- a]|.
Proof.
  move => bt a b n dom V D E Nin.
  rewrite dom_setf cardfsU1 Nin add1n -E.
  elim: n bt a b dom V D E Nin => [|n IH] bt a b dom V D E Nin.
  - rewrite /=; move /esym/cardfs0_eq/fmap_nil: E => E; rewrite D E fsetU0 /=.
    exists (compute_blockchain_rec bt.[#b a <- a] b  [fset #b a] 1).
      by rewrite cats0 /= E fsetU0 /=.
  - rewrite {2}/compute_blockchain_rec -!/compute_blockchain_rec.
    case: ifP => B; last first.
    exists [::]; rewrite cat0s /=.
    move /negbT: B; rewrite inE negb_or => /andP; case => Hneq /negPf Hnin.
      by rewrite D Hnin.
    rewrite inE B.
    move: B; rewrite inE => /orP; case => [H | H].
    move: H; rewrite in_fset1 => /eqP /hashB_inj B; subst a.
    move /negPf: Nin => Nin.
    rewrite /compute_blockchain_rec -!/compute_blockchain_rec D Nin.
    exists (compute_blockchain_rec bt.[#b b <- b] b (#b b |` domf bt) n.+2);
      by rewrite cats0 /= fset1U1.
    rewrite /compute_blockchain_rec -!/compute_blockchain_rec D H.
    have Neq : b == a = false
      by apply /eqP => contra; subst a; move: H Nin => ->.
    case C1 : (prev_blk b \in bt).
    + have Neq2 : prev_blk b == #b a = false
        by apply /eqP => contra; move: contra C1 Nin => -> ->.      
      rewrite fnd_set in_fnd Neq2.
      case: ifP => /eqP B; first by exists [::].
      move: (in_fnd C1) => /V ->.
      rewrite 14?inE C1 orbC nonGB_hash // fnd_rem.
      have Hsize : n = #|` domf bt.[~ #b b]|
        by move: (cardfsD1 (#b b) (domf bt)); rewrite H add1n -E domf_rem => /eq_add_S ->.
      have Hprev : #b bt.[C1] = prev_blk b by move:(in_fnd C1) => /V.
      case: ifP.
      * rewrite inE => /eqP  P/=.
        case: n IH E Hsize => [|n] IH E /esym;
          [by move => /cardfs0_eq; rewrite domf_rem => -> /=; exists [:: bt.[C1]]|].
        rewrite /compute_blockchain_rec -!/compute_blockchain_rec P.
        have Hin : #b bt.[C1] \in domf bt.[~ #b b]
          by rewrite domf_rem inE Hprev in_fset1 C1 nonGB_hash //.
        rewrite -{2}domf_rem Hin fnd_rem in_fset1 eqxx => _.
          by exists [::].
      * rewrite /orb /andb => P.
        have Hvalid : valid_bt bt.[~ #b b]
          by move => h0 b0; rewrite fnd_rem1; case: ifP => R //; move => /V.
        have Hnin : #b a \notin bt.[~ #b b]
          by rewrite inE domf_rem inE negb_and Nin orbC.
        have Hhash : #b b == #b a = false
          by apply /eqP => /hashB_inj contra; subst a; contradict Neq; rewrite eqxx.
        have Hdom : #b a |` domf bt `\ #b b = (#b a |` domf bt) `\ #b b
          by rewrite fsetDUl [[fset _] `\ #b b]mem_fsetD1 //; rewrite in_fset1 Hhash.
        
        case Q: (prev_blk bt.[C1] == #b a).
        move: (IH bt.[~ #b b] a bt.[C1] (domf bt.[~ #b b]) Hvalid erefl Hsize Hnin).
        rewrite domf_rem => [[bs] R].
        exists bs; rewrite -rcons_cat R {1}/compute_blockchain_rec -!/compute_blockchain_rec Hprev.
        rewrite inE in_fsetD1 C1 nonGB_hash // orbC /andb /orb.
        rewrite inE inE orbC domf_rem in_fsetD1 C1 nonGB_hash // /andb /orb.
        rewrite !fnd_set Q [(bt.[#b a <- a]).[~ #b b]]remf1_set.
          by rewrite Hhash Hdom.
        rewrite fnd_set Q.
        move: (IH bt.[~ #b b] a bt.[C1] (domf bt.[~ #b b]) Hvalid erefl Hsize Hnin).
        rewrite domf_rem => [[bs] R].
        exists bs; rewrite -rcons_cat R {1}/compute_blockchain_rec -!/compute_blockchain_rec Hprev.
        rewrite inE in_fsetD1 C1 nonGB_hash // orbC /andb /orb.
        rewrite inE inE orbC domf_rem in_fsetD1 C1 nonGB_hash // /andb /orb.
        rewrite !fnd_set Q [(bt.[#b a <- a]).[~ #b b]]remf1_set.
          by rewrite fnd_rem P Hhash Hdom.
          
     + rewrite fnd_set not_fnd; last by rewrite C1.
       case: ifP => B; last by exists [::].
       have Neq2 : b == GenesisBlock = false
         by apply /eqP => contra; subst b; move: C1 H; rewrite GB_hash => ->.
       have Hnin : #b a \in [fset #b b] = false.
       move: Neq => /eqP Neq; apply /negP.
         by contradict Neq; move: Neq; rewrite in_fset1 => /eqP/hashB_inj.
       have Hhash : #b b == #b a = false
         by apply /eqP => /hashB_inj contra; move /eqP: Neq; subst b.
       have Hin : #b a \in domf bt.[#b a <- a].[~ #b b]
         by rewrite mem_remf1 eq_sym Hhash in_fsetE fset11.
       rewrite Neq2 inE fset1U1 Hnin Hin /=.
       case: ((bt.[#b a <- a]).[~ #b b]).[? prev_blk a] => [b'|]; last by exists [:: a].
       case: ifP => A; first by exists [:: a].
       eexists (rcons (compute_blockchain_rec _ b' _ n) a).
         by rewrite cats1.
Qed.

Lemma compute_blockchain_prefix :
  forall (bt : BlockTree) (a b : Block),
  valid_bt bt ->
  exists p, p ++ (compute_blockchain bt b) = compute_blockchain bt.[#b a <- a] b.
Proof.
  move => bt a b V.
  case A: (#b a \in bt); first by rewrite btupd_in_noeffect //; exists [::].
  apply: compute_blockchain_ext => //.
    by rewrite A.
Qed.

Lemma compute_blockchain_tail_nogb :
  forall (bt : BlockTree) (b : Block),
  valid_bt bt ->
  compute_blockchain bt b = [::] \/
  exists a t, compute_blockchain bt b = a :: t /\
         forall c, c \in t -> c != GenesisBlock.
Proof.
  move => bt b V.
  case B: (#b b \in bt); last first.
  - left; rewrite /compute_blockchain /compute_blockchain_rec.
    case D: (#|` domf bt| == 0); first by move /eqP: D => ->; rewrite B.
    move /negbT: D; rewrite -lt0n => /prednK => <-.
      by rewrite -!/compute_blockchain_rec B.
  - right; case NG: (b == GenesisBlock); move /eqP: NG => NG.
    rewrite /compute_blockchain /compute_blockchain_rec.
    move: (cardfsD1 (#b b) (domf bt)); rewrite B /= add1n => ->.
    rewrite -!/compute_blockchain_rec B NG GB_hash -NG in_fnd eqxx.
      by exists b, [::].
    have D: domf bt = domf bt by done.
    have S: size (domf bt) = size (domf bt) by done.
    move: {-2}(size (domf bt)) S => n. 
    move: {-2}(domf bt) D => dom.
    elim: n b bt dom V B NG => [|n IH] b bt dom V B NG D /esym.
      by move => /cardfs0_eq E; subst dom; move: B; rewrite inE E in_fset0.
    rewrite /compute_blockchain /compute_blockchain_rec -!/compute_blockchain_rec.
    subst dom => S; rewrite S /=.
    rewrite B.
    case P: (prev_blk b \in bt); last by rewrite (not_fnd); [exists b, [::]|rewrite P].
    move /eqP/negPf: NG => NG; rewrite NG.
    rewrite in_fnd.
    have Phash : (#b bt.[P] = prev_blk b) by move: (in_fnd P) => /V.
    case G: (bt.[P] == GenesisBlock).
    case: n S IH => [|n] S IH; rewrite /compute_blockchain_rec -!/compute_blockchain_rec.
      by case: ifP; [case: ifP; exists b, [::]|exists b, [::]].
    have H : #b bt.[P] \in domf bt `\ #b b
        by rewrite inE in_fset1 Phash nonGB_hash //; apply /eqP; rewrite NG.
    have H' : #b bt.[P] \in domf bt.[~ #b b] by rewrite domf_rem H.
    rewrite H inE H' G.
    case: (bt.[~ #b b]).[? prev_blk bt.[P]] => [_|];
      by exists bt.[P], [:: b]; split => // c; rewrite mem_seq1 => /eqP ->; rewrite NG.
    have Hin : (#b bt.[P] \in bt.[~ #b b])
      by rewrite inE domf_rem inE in_fset1 Phash P andbC /andb nonGB_hash //; move /eqP: NG.
    have Hvalid : valid_bt bt.[~ #b b]
      by move => k v; rewrite fnd_rem; case: ifP => _ //; apply: V.
    have Hsize : n = #|` domf bt.[~ #b b]|.
      by rewrite domf_rem; move: (cardfsD1 (#b b) (domf bt)); rewrite B add1n S => /eq_add_S.
    move /eqP: G => G.
    move: (IH bt.[P] bt.[~ #b b] (domf bt.[~ #b b]) Hvalid Hin G erefl Hsize) => [a] [t].
    rewrite /compute_blockchain -Hsize domf_rem; case => [E H].
    exists a, (rcons t b); rewrite E rcons_cons; split => // c.
    rewrite rcons_in => /orP; case => [I | /eqP I]; first by apply: H.
      by subst c; rewrite NG.
Qed.

Lemma good_bt_add_block_same_chain :
  forall (bt : BlockTree) (a b : Block),
  valid_bt bt -> has_gb bt ->
  good_blockchain (compute_blockchain bt b) ->
  compute_blockchain (bt_upd bt a) b = compute_blockchain bt b.
Proof.
  move => bt a b V G Hg.
  have V' : valid_bt (bt_upd bt a) by apply: btupd_validP.
  case: (compute_blockchain_prefix a b V) (compute_blockchain_tail_nogb b V') => bs E H.
  suff Hsuff : bs = [::] by subst.
  case: H; first by rewrite -E; case: bs E => // .
  case => x; case => t.
  rewrite -E; case => H P.
  case: bs H E => [|b' bs] //.
  rewrite cat_cons; case => Heq; subst b' => Heq; subst t.
  have Hin : GenesisBlock \in (bs ++ compute_blockchain bt b).
  rewrite mem_cat; move: Hg; case: (compute_blockchain _ _) => [|y z] //= /eqP ->.
    by rewrite mem_head orbC.
      by move /P/eqP: Hin.
Qed.

Lemma good_bt_add_seq_same_chain :
  forall (bs : seq Block) (bt : BlockTree) (b : Block),
  valid_bt bt -> has_gb bt ->
  good_blockchain (compute_blockchain bt b) ->
  compute_blockchain (foldl bt_upd bt bs) b = compute_blockchain bt b.
Proof.
  move => bs bt b V G H; elim: bs => [|a bs IH] //=.
  rewrite bt_updE foldl_comm /= good_bt_add_block_same_chain //.
  by apply: btupd_validP_foldl.
  by apply: btupd_gbP_foldl.
  by rewrite IH.
Qed.

Lemma compute_blockchain_notin_upd :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt -> has_gb bt ->
    good_bt bt ->
    #b b \notin bt ->
    (forall x : Block, #b x \in bt -> 
       compute_blockchain bt.[#b b <- b] x = compute_blockchain bt x).
Proof.
  move => bt b V G H Nin x Hin.
  move: (compute_blockchain_prefix b x V) => [p].
  rewrite /bt_upd => E; rewrite -E.
  suff Hsuff: p = [::] by rewrite Hsuff.
  move: (compute_blockchain_tail_nogb x (@btupd_validP _ b V)).
  rewrite /bt_upd; case => P.
  move: P; rewrite /compute_blockchain.
  move: (cardfsD1 (#b b) (domf bt.[#b b <- b])).
  rewrite dom_setf fset1U1 add1n => ->.
  rewrite /compute_blockchain_rec -!/compute_blockchain_rec.
  rewrite inE Hin orbC /orb fnd_set.
  case: ifP.
  (* trivial case *)
  case: ifP => // _ _; rewrite -cats1.
  set bc := compute_blockchain_rec (bt.[#b b <- b]).[~ #b x] b ((#b b |` domf bt) `\ #b x)
                                                             #|` (#b b |` domf bt) `\ #b b|.
  by case: bc.
  case: (bt.[? prev_blk x]) => [pv|] //; case: ifP => // _ _; rewrite -cats1.
  set bc :=  compute_blockchain_rec (bt.[#b b <- b]).[~ #b x] pv ((#b b |` domf bt) `\ #b x)
                                                              #|` (#b b |` domf bt) `\ #b b|.
  by case: bc.  
  (* nontrivial case *)
  case: P => [a] [bc] [Hext P].
  have: good_blockchain (compute_blockchain bt x).
    by move: (H x Hin); case /andP.
  rewrite /good_blockchain.
  move: E; set s := compute_blockchain bt x.
  case: s => [|d s] // E /eqP GB; subst d.
  move: E; rewrite Hext.
  case: p => [|h p] //.
  rewrite cat_cons; case => _ X.
  have: GenesisBlock \in bc by rewrite -X mem_cat mem_head orbC.
    by move => /P; rewrite eqxx.
Qed.

Lemma compute_blockchain_inall :
  forall (bt : BlockTree) (bc : Blockchain),
    valid_bt bt -> has_gb bt ->
    bc \in all_blockchains bt ->
    compute_blockchain bt (last_blk bc) = bc.
Proof.
  move => bt bc V G /mapP [b] I E.
  suff Hsuff : last_blk (compute_blockchain bt b) = b
    by move: Hsuff; rewrite E => ->.
  move /mapP: I => [h] H.
  rewrite /get_block.
  case C: (bt.[? h]) => [a|]; move: C; last by rewrite in_fnd.
  move => /V Heq1 Heq2; subst a h => {E V G bc}.
  have Ek : domf bt = domf bt by done.
  have Es : #|` domf bt| = #|` domf bt| by done.
  move: {-2}#|` domf bt| Es => n.
  move: {-2}(domf bt) Ek => dom Es En.
  elim: n b bt dom Es En H => [|n IH] b bt dom Es En H.
  - move /esym: En => /cardfs0_eq E; subst dom.
      by move: H; rewrite E in_fset0.
  - rewrite /compute_blockchain -Es -En Es /= H.
    case C: (bt.[? _]) => [a|] => //=.
      by case: ifP => _ //; rewrite /last_blk last_rcons.
Qed.

Lemma compute_blockchain_block_in_bt :
  forall (bt : BlockTree) (a b : Block),
  valid_bt bt -> has_gb bt ->
  b \in compute_blockchain bt a -> #b b \in bt.
Proof.
  rewrite /compute_blockchain => bt a b V G.
  have Ek : domf bt = domf bt by done.
  have Es : #|` domf bt| = #|` domf bt| by done.
  move: {-2}#|` domf bt| Es => n.
  move: {-2}(domf bt) Ek => dom Es En.
  elim: n a b bt dom Es En V G => [|n IH] a b bt dom Es En V G /=.
  - move /esym: En => /cardfs0_eq E; subst dom.
      by rewrite E in_fset0.
  - subst dom. case: ifP => I; last by rewrite in_nil.
    rewrite I; case P: (prev_blk a \in bt); last first.
    rewrite not_fnd inE; by [rewrite P | move => /eqP ->; rewrite I].
    rewrite in_fnd; case: ifP.
      by rewrite inE => _ /eqP ->; rewrite I.
    move => NG; rewrite rcons_in => /orP; case.
    have Hsize : n = #|` domf bt.[~ #b a]|
      by rewrite domf_rem; apply: eq_add_S; rewrite En (cardfsD1 (#b a)) I add1n.
    have Hvalid : valid_bt bt.[~ #b a] by apply: btrem_validP => //.
    have Hgb : has_gb bt.[~ #b a] by apply: btrem_gbP => //.
    move: (IH bt.[P] b bt.[~ #b a] (domf bt.[~ #b a]) erefl Hsize Hvalid Hgb) => H.
    rewrite domf_rem in H => /H; rewrite inE domf_rem inE => /andP.
      by case => [_ E]; rewrite E.
      by move => /eqP ->; rewrite I.
Qed.

Lemma all_blockchains_gb :
  forall (bt : BlockTree),
    has_gb bt -> [:: GenesisBlock] \in all_blockchains bt.
Proof.
  rewrite /has_gb => bt G; apply /mapP.
  exists GenesisBlock.
  - apply /mapP; exists (#b GenesisBlock);
      by [move /fndSomeP: G; case | rewrite /get_block G].
  - rewrite /compute_blockchain.
    move: (G) => /has_gb_n1; case => n ->; rewrite compute_blockchain_gb //.
      by move: G; rewrite fndSomeP; case.
Qed.

Lemma compute_blockchain_notin_nil :
  forall (bt : BlockTree) (b : Block) (dom : {fset HashValue}) (n : nat),
    #b b \in bt = false ->
     compute_blockchain_rec bt b dom n = [::].
Proof.
  move => bt b dom n Nin.
  case: n => [|n] //=.
  case: ifP => //; case: ifP => //.
  case: ifP => //.
  rewrite Nin //.
Qed.

Lemma compute_blockchain_single_block :
  forall (bt : BlockTree) (b : Block) (dom : {fset HashValue}) (n : nat),
    #b b \in bt ->
    #b b \in dom ->
    prev_blk b \in bt = false ->
    compute_blockchain_rec bt b dom n.+1 = [:: b].
Proof.
  move => bt b dom n Ibt Idom Nin /=.
    by rewrite Idom Ibt not_fnd // Nin.
Qed.

Lemma compute_blockchain_rem_notin :
  forall (bt : BlockTree) (a b : Block),
    valid_bt bt ->
    #b b \in bt ->
    b \notin compute_blockchain bt a ->
    compute_blockchain bt a = compute_blockchain bt.[~ #b b] a.
Proof.
  rewrite /compute_blockchain => bt a b.
  have Ek: domf bt = domf bt by done.
  have Es: #|` domf bt| = #|` domf bt| by done.
  move: {-2}#|` domf bt| Es => n.
  move: {-2}(domf bt) Ek => dom Es En.
  elim: n a b bt dom Es En => [|n IH] a b bt dom Es En V B.
  by move /esym /cardfs0_eq: En => E; subst dom; rewrite E fset0D restrictf0 domf0 cardfs0 /=.
  have Vrem : valid_bt bt.[~ #b b] by apply: btrem_validP.
  have S : n = #|` domf bt `\ #b b|
    by move: (cardfsD1 (#b b) dom); rewrite -En Es B add1n => /eq_add_S.
  have F : [fset x | x in domf bt & x \in dom `\ #b b] = domf bt `\ #b b.
  rewrite -fsetP => k; subst dom; rewrite !inE.
  case: (k == #b b) => //=; by [rewrite andbC|case: (k \in domf bt) => //=].
  rewrite /=; case: ifP => A; last first.
  rewrite F -S /= compute_blockchain_notin_nil //.
    by subst dom; rewrite inE domf_rem inE A andbC.
  subst dom; rewrite A.
  case P: (prev_blk a \in bt); last first.
  rewrite not_fnd //.
  rewrite inE => /negPf N; move: (cardfsD1 (#b a) (domf bt `\ #b b)).
  have Nhash : (#b a == #b b = false) by apply /eqP; move /eqP in N; contradict N; move /hashB_inj: N.
  rewrite inE in_fset1 Nhash A add1n => S'.
  rewrite F S' compute_blockchain_single_block //.
    by rewrite inE domf_rem inE in_fset1 Nhash A.
    by rewrite inE in_fset1 Nhash A.
    by rewrite inE domf_rem inE in_fset1 P andbC.
    by rewrite P.
  rewrite in_fnd; case: ifP => E.
  move /eqP in E; subst a.
  rewrite inE => /negPf N; move: (cardfsD1 (#b GenesisBlock) (domf bt `\ #b b)).
  have Nhash : (#b GenesisBlock == #b b = false) by apply /eqP; move /eqP in N; contradict N; move /hashB_inj: N.
  rewrite inE in_fset1 Nhash A add1n => S'.
  rewrite F S' compute_blockchain_gb //.
  apply: btrem_gbP => //; rewrite /has_gb in_fnd.
  suff Hsuff : #b bt.[A] = #b GenesisBlock by move /hashB_inj: Hsuff => ->.
    by rewrite validE.
    by rewrite inE in_fset1 Nhash A.
  rewrite rcons_in negb_or => /andP; case => Nin /negPf N.
  have Nhash : (#b a == #b b = false) by apply /eqP; move /eqP in N; contradict N; move /hashB_inj: N.  
  move: (cardfsD1 (#b a) (domf bt `\ #b b)); rewrite inE in_fset1 Nhash A add1n F => S'.
  suff X:
    compute_blockchain_rec bt.[~ #b b] a (domf bt `\ #b b) #|` domf bt `\ #b b|
  = rcons (compute_blockchain_rec
             (bt.[~ #b a]).[& (domf bt `\ #b a) `\ #b b]
             bt.[P]
             (domf (bt.[~ #b a]).[& (domf bt `\ #b a) `\ #b b])
             #|` domf (bt.[~ #b a]).[& (domf bt `\ #b a) `\ #b b]|)
          a.
  rewrite X.
  have HD : domf bt `\ #b a = domf bt.[~ #b a] by rewrite domf_rem.
  have HS : n = #|` domf bt `\ #b a|
    by move: (cardfsD1 (#b a) (domf bt)); rewrite A add1n -En => /eq_add_S.
  have HV : valid_bt bt.[~ #b a] by apply: btrem_validP.
  have HI : #b b \in bt.[~ #b a] by rewrite inE domf_rem inE in_fset1 eq_sym Nhash B.
    by rewrite (IH bt.[P] b bt.[~ #b a] (domf bt `\ #b a) HD HS HV HI Nin).
  have Z : prev_blk a == #b b = false.
  - apply /eqP; move /negP in Nin.
    contradict Nin.
    have Neq : prev_blk a == #b a = false by move /eqP: E => /nonGB_hash /negPf.
    have Eq : #b bt.[P] = #b b by rewrite validE //.
    move /hashB_inj in Eq; rewrite Eq.
    rewrite S S' /= inE in_fset1 B eq_sym Nhash /=.
    rewrite inE domf_rem inE in_fset1 B eq_sym Nhash /=.
    case: (_.[? prev_blk b]) => [b'|]; last by rewrite mem_head.
    case: ifP => _ //; first by rewrite mem_head.
      by rewrite rcons_in eqxx orbC.
  have P' : prev_blk a \in bt.[~ #b b] by rewrite inE domf_rem inE in_fset1 Z P.
  rewrite S'/= inE in_fset1 Nhash A /= inE domf_rem inE in_fset1 Nhash A /=.
  rewrite in_fnd E /=.
  have D : [fset x | x in [fset x0 | x0 in domf bt & x0 \in domf bt `\ #b a] & x \in domf bt `\ #b a `\ #b b]
           = domf bt `\ #b b `\ #b a.
  rewrite -fsetP => k; rewrite !inE.
  case: (k == #b a) => //=. by rewrite andbA andbC.
  case: (k == #b b) => //=. by rewrite andbC.
    by case: (k \in domf bt).
  have X : [ffun x => bt (fincl (fset_sub (domf bt) (mem (domf bt `\ #b b))) x)] [` P']
           = bt.[P].
  suff Hsuff : #b [ffun x => bt (fincl (fset_sub (domf bt) (mem (domf bt `\ #b b))) x)] [` P']
               = #b bt.[P] by move /hashB_inj: Hsuff.
    by rewrite !validE.
  have Y : (bt.[~ #b b]).[& [fset x | x in domf bt & x \in domf bt `\ #b b] `\ #b a]
           = (bt.[~ #b a]).[& domf bt `\ #b a `\ #b b].
  rewrite -fmapP => k; rewrite !FmapE.fmapE.
  suff Hsuff : [fset x | x in domf bt & x \in domf bt `\ #b b] `\ #b a
               = domf bt `\ #b a `\ #b b.
  rewrite Hsuff; case: ifP => //; rewrite inE in_fset1 inE in_fset1.
  by move /andP => [H1 /andP [H2 H3]]; rewrite inE in_fset1 H1 H2 H3 /=.
  rewrite -fsetP => h; rewrite !inE.
  case: (h == #b a) => //=. by rewrite andbC.
  case: (h == #b b) => //=. by rewrite andbC.
    by case: (h \in domf bt).
    by rewrite D X Y.
Qed.

Lemma compute_blockchain_rcons :
  forall (bt : BlockTree) (b pb : Block),
    valid_bt bt ->
    #b b \in bt -> #b pb \in bt ->
    b != GenesisBlock ->
    prev_blk b = #b pb ->                         
    b \notin compute_blockchain bt pb ->
    compute_blockchain bt b = rcons (compute_blockchain bt pb) b.
Proof.
  move => bt b pb V I I' NG P Nin.
  rewrite (compute_blockchain_rem_notin V I Nin) /compute_blockchain.
  have Ek: domf bt = domf bt by done.
  have Es: #|` domf bt| = #|` domf bt| by done.
  move: {-2}#|` domf bt| Es => n.
  move: {-2}(domf bt) Ek => dom Es En.
  elim: n b bt dom Es En V NG I I' P Nin => [|n IH] b bt dom Es En V NG I I' P Nin /=.
  - move /esym /cardfs0_eq: En => E; subst dom.
      by move: I; rewrite inE E in_fset0.
  - subst dom; rewrite I P in_fnd.
    move /negPf: NG => NG; rewrite NG.
    have: #b bt.[I'] = #b pb by rewrite validE.
    move /hashB_inj => ->.
    have: [fset x | x in domf bt & x \in domf bt `\ #b b] = domf bt `\ #b b.
    rewrite -fsetP => k; rewrite !inE.
    case: (k == #b b) => //=. by rewrite andbC.
      by case: (k \in domf bt).
    move => ->; move: (cardfsD1 (#b b) (domf bt)).
      by rewrite I add1n -En => /eq_add_S <-.
Qed.

Lemma compute_blockchain_last_within :
  forall (bt : BlockTree) (b : Block),
    (compute_blockchain bt b == [::]) || (b \in compute_blockchain bt b).
Proof.
  rewrite /compute_blockchain => bt b.
  have Ek: domf bt = domf bt by done.
  have Es: #|`domf bt| = #|`domf bt| by done.
  move: {-2}#|` domf bt| Es => n.
  move: {-2}(domf bt) Ek => dom Es En.
  elim: n b bt dom Es En =>[|n IH] b bt dom Es En /=.
    by case: ifP => //; case: ifP.
  subst dom; case: ifP => // ->.
  case: (bt.[? prev_blk b]) => [a|] /=; last by rewrite mem_head.
  case: ifP; first by rewrite mem_head.
    by rewrite rcons_in eqxx orbA orbC.
Qed.

Lemma compute_blockchain_last_blk :
  forall (bt : BlockTree) (b : Block),
    (compute_blockchain bt b = [::]) \/ (#b last_blk (compute_blockchain bt b) = #b b).
Proof.
  rewrite/compute_blockchain => bt b.
  have Ek: domf bt = domf bt by done.
  have Es: #|` domf bt| = #|` domf bt| by done.
  move: {-2}#|` domf bt| Es => n.
  move: {-2}(domf bt) Ek => dom Es En.
  elim: n b bt dom Es En => [|n IH] b bt dom Es En /=.
  case: ifP; last by left.
    by case: ifP; left.
  subst dom; case: ifP; last by left.
  move => ->; case: bt.[? prev_blk b] => [a|]; last by right.
  case: ifP; first by right.
    by rewrite /last_blk last_rcons; right.
Qed.

Lemma compute_blockchain_nil_notin :
  forall (bt : BlockTree) (b : Block) (dom : {fset HashValue}) (n : nat),
    n = #|` dom| ->
    compute_blockchain_rec bt b dom n = [::] ->
    #b b \notin dom \/ #b b \notin bt.
Proof.
  move => bt b dom.
  elim => [|n IH].
  - move => /esym /cardfs0_eq => E; subst dom; by left.
  - move => E /=.
    case: ifP => //; last by left.
    case: ifP => //; last by right.
    case: bt.[? prev_blk b] => [a|] //.
    case: ifP => //.
    move => NG B D.
    set bc := (compute_blockchain_rec bt.[~ #b b] a (dom `\ #b b) n).
    by case: bc.
Qed.

Lemma compute_blockchain_hashchain :
  forall (bt : BlockTree) (b : Block),
  valid_bt bt -> has_gb bt ->
  hash_blockchain (compute_blockchain bt b).
Proof.
  rewrite /compute_blockchain => bt b V G.
  have Ek: domf bt = domf bt by done.
  have Es: #|` domf bt| = #|` domf bt| by done.
  move: {-2}#|` domf bt| Es => n.
  move: {-2}(domf bt) Ek => dom Es En.
  elim: n b bt dom Es En V G => [|n IH] b bt dom Es En V G /=.
  by case: ifP=>//=; case: ifP=>//=.
  case: ifP => X //; case: ifP => Y //.
  case P: (prev_blk b \in bt); last by rewrite not_fnd // P.
  rewrite in_fnd; case: ifP => NG //.
  case PG: (prev_blk b == #b GenesisBlock).
  have: #b bt.[P] = #b GenesisBlock by rewrite validE //; move /eqP: PG.
  move => /hashB_inj ->.
  move: (cardfsD1 (#b GenesisBlock) (domf bt `\ #b b)).
  have Nhash : #b GenesisBlock == #b b = false
    by apply /eqP => /hashB_inj => contra; move: contra NG => ->; rewrite eqxx.
  subst dom; move /eqP: PG => PG.
  rewrite inE in_fset1 Nhash -PG P add1n.
  move: (cardfsD1 (#b b) (domf bt)); rewrite X add1n -En => /eq_add_S <- ->.
  rewrite compute_blockchain_gb //=.
    by rewrite PG eqxx.
    by apply: btrem_gbP => //; rewrite inE in_fset1 Nhash -PG P.
    by rewrite inE in_fset1 Nhash -PG P.
  have W : hash_blockchain (compute_blockchain_rec bt.[~ #b b] bt.[P] (dom `\ #b b) n).
  apply: IH => //.
  by subst dom; rewrite domf_rem.
  by move: (cardfsD1 (#b b) dom); rewrite X add1n -En => /eq_add_S.
  by apply: btrem_validP.
  by apply: btrem_gbP.
  apply: hashchain_rcons => //.
  have BP : prev_blk b = #b bt.[P] by rewrite validE => //.  
  case: (compute_blockchain_last_blk bt.[~ #b b] bt.[P]); rewrite /compute_blockchain.
  - subst dom; rewrite domf_rem.
    move => /(compute_blockchain_nil_notin (erefl _)).
    have Neq : (prev_blk b == #b b) = false by move /eqP: NG => /nonGB_hash /negPf.
    by case; [|rewrite inE domf_rem]; rewrite inE in_fset1 -BP P Neq.
  - subst dom; move: (cardfsD1 (#b b) (domf bt)).
      by rewrite X add1n -En domf_rem => /eq_add_S <- ->.
Qed.

End compute_blockchain.

Section btBlockchain.

Definition btBlockchain (bt : BlockTree) :=
  foldr take_better_bc [:: GenesisBlock] (good_blockchains bt).

Lemma btBlockchain_largest :
  forall (bt : BlockTree) (bc : Blockchain),
    bc \in good_blockchains bt -> btBlockchain bt >=b bc.
Proof.
  rewrite /btBlockchain /good_blockchains => bt bc.
  elim: (all_blockchains bt) => [|c bcs IH] //=.
  case: ifP => V; last by apply: IH.
  rewrite inE => /orP; case => [/eqP H | H].
  subst c; rewrite /= {1 3}/take_better_bc.
  case: ifP; first by left.
    by move => /FCR_ngtT.
  rewrite /= {1 3}/take_better_bc.
  case: ifP; last by move => _; apply: (IH H).
  move: (IH H); case.
  move => ->; by right.
    by move => P Q; right; apply: (FCR_trans Q P).
Qed.

Lemma perm_eq1E {T : eqType} (s : seq T) (x : T) :
  perm_eq s [:: x] -> s = [:: x].
Proof.
  elim: s x => [|y s IH] x.
  rewrite /perm_eq all_cat; case /andP => /= _.
    by rewrite eqxx add1n; case /andP => /eqP.
  case A: (x == y).
  - move /eqP in A; subst y; rewrite perm_cons.
    case: s IH => [|y s] IH //=.
    rewrite /perm_eq all_cat; case /andP => /=.
      by rewrite eqxx add1n; case /andP => /eqP.
  - move: (mem_seq1 y x); rewrite eq_sym A => H /perm_mem.
      by move => /(_ y); rewrite mem_head H.
Qed.
  
Lemma perm_notin_fsetU {T : choiceType} (x : T) (f : {fset T}) :
  x \notin f ->
  perm_eq (enum_fset (x |` f)) (x :: (enum_fset f)).
Proof.
  have Ek: enum_fset f = enum_fset f by done.
  move: {-2}(enum_fset f) Ek => s.
  elim: s f => [|y s IH] f H.
  rewrite enum_fsetE /fsetU -H cats0 => N.
  rewrite enum_fsetE enum_fset1 /=. 
  rewrite -enum_fsetE /=.
  have: Imfset.imfset fsetU_key (fun x0 : T => x0) (Phantom (mem_pred T) (mem (cons x nil))) = [fset x].
  rewrite unlock /=; move: (seq_fset_perm fsetU_key [:: x]) => /=.
  move => /perm_eq1E. admit.
    by move => ->; rewrite enum_fsetE enum_fset1.
  (*rewrite imfset_id.
  
  move => /esym /cardfs0_eq => E; rewrite E fsetU0 => H.
  have P: (enum_fset fset0) = [::] by move => t; rewrite enum_fsetE enum_fset0.
  rewrite P in H; rewrite H => Nin.
  have Q: (enum_fset [fset #b b]) = [:: #b b] by rewrite enum_fsetE enum_fset1.
    by rewrite Q.
  rewrite enum_fsetE. 
  rewrite /perm_eq => Nin.
  rewrite all_cat; apply /andP; split => /=; last first.
  apply /andP; split.
  rewrite eqxx add1n; move /count_memPn: Nin => H.
  rewrite H. Print canonical_keys. *)
Admitted.
    
Lemma good_blockchain_split_perm :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt -> has_gb bt ->
    good_bt bt -> #b b \notin bt ->
    good_bt bt.[#b b <- b] ->
    perm_eq (good_blockchains bt.[#b b <- b]) ((compute_blockchain bt.[#b b <- b] b) :: good_blockchains bt).
Proof.
  move => bt b.
  move => V G Hg Nin Hcg.
  rewrite {1}/good_blockchains /all_blockchains.
  have P1 : perm_eq (enum_fset (#b b |` domf bt)) (#b b :: (enum_fset (domf bt)))
    by rewrite perm_notin_fsetU.
  have P2 : perm_eq [seq get_block bt.[#b b <- b] k | k <- domf bt.[#b b <- b]]
                    (b :: [seq get_block bt.[#b b <- b] k | k <- domf bt]).
  rewrite dom_setf; move: (perm_map (get_block bt.[#b b <- b]) P1) => /=.
    by rewrite {2}/get_block fnd_set eqxx.
  have P4 : perm_eq
              [seq c <- [seq compute_blockchain bt.[#b b <- b] b0
                        | b0 <- b :: [seq get_block bt.[#b b <- b] k | k <- domf bt]]
              | good_blockchain c & valid_blockchain c]
              [seq c <- [seq compute_blockchain bt.[#b b <- b] b0
                        | b0 <- [seq get_block bt.[#b b <- b] k | k <- domf bt.[#b b <- b]]]
              | good_blockchain c & valid_blockchain c].
  move: (perm_map (compute_blockchain bt.[#b b <- b]) P2) => H.
    by apply: perm_filter; rewrite perm_sym.
  suff Hsuff: perm_eq
                [seq c <- [seq compute_blockchain bt.[#b b <- b] b0 |
                           b0 <- b :: [seq get_block bt.[#b b <- b] k | k <- domf bt]]
                | good_blockchain c & valid_blockchain c]
                (compute_blockchain bt.[#b b <- b] b :: good_blockchains bt).
    by rewrite perm_sym in P4; apply: (perm_trans P4 Hsuff).
  rewrite /= (good_bt_good_blockchain Hcg); last by rewrite inE dom_setf fset1U1.
  rewrite (good_bt_valid_blockchain Hcg) /=; last by rewrite inE dom_setf fset1U1.
  rewrite perm_cons; clear P4.
  rewrite /good_blockchains /all_blockchains; apply: perm_filter.
  have: [seq get_block bt.[#b b <- b] k | k <- domf bt] = [seq get_block bt k | k <- domf bt].
  - rewrite -eq_in_map /prop_in1 => h Hin.
    rewrite /get_block fnd_set; case: ifP => // /eqP E.
      by subst h; rewrite Hin in Nin.
  move => ->.
  have: [seq compute_blockchain bt.[#b b <- b] b0 | b0 <- [seq get_block bt k | k <- domf bt]]
        = [seq compute_blockchain bt b0 | b0 <- [seq get_block bt k | k <- domf bt]].
  - rewrite -eq_in_map; case B: (#b b \in bt).
      by move: (btupd_in_noeffect V B); rewrite /bt_upd => ->.
    move /negbT in B; rewrite /prop_in1 => a /mapP [h] Hin.
    rewrite /get_block in_fnd => H.
    move: (validE Hin V) => E.
    apply: compute_blockchain_notin_upd => //.
      by rewrite H E.
  by move => ->.
Qed.

Lemma good_blockchains_btupd_subset (bt : BlockTree) (b : Block) :
  valid_bt bt ->
  {subset good_blockchains bt <= good_blockchains bt.[#b b <- b]}.
Proof.
  rewrite /sub_mem /good_blockchains => V cs.
  rewrite mem_filter; case /andP => /andP [Hg Hv] Hin.
  rewrite mem_filter; rewrite Hg Hv /=.
  move: Hin; rewrite /all_blockchains => /mapP.
  case => x /mapP; case => h Hin Ex Ecs.
  subst x cs; rewrite {1}/get_block in_fnd.
  apply /mapP. exists bt.[Hin].
  - apply /mapP; exists h; first by rewrite dom_setf inE Hin orbC.
    rewrite /get_block fnd_set; case: ifP.
      by move => /eqP E; subst h; move: (validE Hin V) => /hashB_inj.
      by move => Neq; rewrite in_fnd.
  - case B: (#b b \in bt); first by move: (btupd_in_noeffect V B); rewrite /bt_upd => ->.
    move: (compute_blockchain_prefix b bt.[Hin] V) => [p].
    rewrite /bt_upd => E; rewrite -E.
    suff Hsuff: p = [::] by rewrite Hsuff.
    move: (compute_blockchain_tail_nogb bt.[Hin] (@btupd_validP _ b V)).
    rewrite /bt_upd; case => P.
    move: P; rewrite /compute_blockchain.
    move: (cardfsD1 (#b b) (domf bt.[#b b <- b])).
    rewrite dom_setf fset1U1 add1n => ->.
    rewrite /compute_blockchain_rec -!/compute_blockchain_rec.
    rewrite inE validE // Hin orbC /orb fnd_set.
    case: ifP.
    (* trivial case *)
    case: ifP => // _ _; rewrite -cats1.
    set bc := compute_blockchain_rec (bt.[#b b <- b]).[~ h] b ((#b b |` domf bt) `\ h)
                                                            #|` (#b b |` domf bt) `\ #b b|.
      by case: bc.
    case: (bt.[? prev_blk bt.[Hin]]) => [pv|] //; case: ifP => // _ _; rewrite -cats1.
    set bc :=  compute_blockchain_rec (bt.[#b b <- b]).[~ h] pv ((#b b |` domf bt) `\ h)
                                                               #|` (#b b |` domf bt) `\ #b b|.
      by case: bc.  
    (* nontrivial case *)
    case: P => [a] [bc] [Hext P].
    move: Hg; rewrite /good_blockchain /get_block in_fnd.
    move: E; set s := compute_blockchain bt bt.[Hin].
    case: s => [|d s] // E /eqP GB; subst d.
    move: E; rewrite Hext.
    case: p => [|x p] //.
    rewrite cat_cons; case => _ X.
    have: GenesisBlock \in bc by rewrite -X mem_cat mem_head orbC.
      by move => /P; rewrite eqxx.
Qed.

Lemma good_blockchains_foldl_btupd_subset (bt : BlockTree) (bs : seq Block) :
  valid_bt bt ->
  {subset good_blockchains bt <= good_blockchains (foldl bt_upd bt bs)}.
Proof.
  elim: bs bt => [|b bs IH] bt V //=.
  rewrite bt_updE foldl_comm /= {1}/bt_upd.
  move: (IH bt V) => H x /H.
    by apply: good_blockchains_btupd_subset; apply: btupd_validP_foldl.
Qed.
    
Lemma btBlockchain_btupd_geq :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt -> has_gb bt ->
    btBlockchain (bt_upd bt b) >=b btBlockchain bt.
Proof.
  move => bt b V G.
  rewrite /btBlockchain /bt_upd.
  move: (good_blockchains_btupd_subset b V).
    by apply: subset_take_better_geq.
Qed.

Lemma btBlockchain_geq :
  forall (bs : seq Block) (bt : BlockTree),
    valid_bt bt -> has_gb bt ->
    btBlockchain (foldl bt_upd bt bs) >=b btBlockchain bt.
Proof.
  elim /last_ind => [|bs b IH] bt V G /=; first by left.
  rewrite -cats1 foldl_cat /=.
  have: (btBlockchain (bt_upd (foldl bt_upd bt bs) b) >=b btBlockchain (foldl bt_upd bt bs))
    by apply: btBlockchain_btupd_geq; [apply: foldl_btupd_validP | apply: foldl_btupd_gbP].
  move: (IH bt V G) => P Q.
    by apply: FCR_geq_trans Q P.
Qed.
    
Lemma btBlockchain_seq_same :
  forall (bs : seq Block) (b : Block) (bt : BlockTree),
  valid_bt bt -> has_gb bt ->
  b \in bs -> btBlockchain bt = btBlockchain (foldl bt_upd bt bs) ->
  btBlockchain bt = btBlockchain (bt_upd bt b).
Proof.
  move => bs b bt V G I.
  move: (mem_split I) => [bs1] [bs2] [Heq Hnin]; subst bs.
  have Hvalid : valid_bt (bt_upd bt b) by apply: btupd_validP.
  have Hgb : has_gb (bt_upd bt b) by apply: btupd_gbP.
  move: (btBlockchain_btupd_geq b V G) => P.
  case: P; first by move => ->.
  rewrite -cat1s => contra E; rewrite E in contra.
  contradict contra.
  rewrite foldl_cat foldl_comm /= -foldl_cat.
    by rewrite -FCR_ngt; apply: btBlockchain_geq.
Qed.

Lemma btBlockchain_seq_geq :
  forall (bt : BlockTree) (bs : seq Block) (b : Block),
    valid_bt bt -> has_gb bt ->
    b \in bs -> btBlockchain bt >=b btBlockchain (foldl bt_upd bt bs) ->
    btBlockchain bt >=b btBlockchain (bt_upd bt b).
Proof.
  move => bt bs b V G I [Heq | Hgt].
    by rewrite -(btBlockchain_seq_same V G I) //; left.
  contradict Hgt.
    by rewrite -FCR_ngt; apply: btBlockchain_geq.
Qed.  

Lemma btBlockchain_seq_sub_geq :
  forall (bc : Blockchain) (bt : BlockTree) (bs : seq Block) (b : Block),
    valid_bt bt -> has_gb bt ->
    b \in bs -> bc >=b btBlockchain bt ->
          bc >=b btBlockchain (foldl bt_upd bt bs) ->
          bc >=b btBlockchain (bt_upd bt b).
Proof.

  move => bc bt bs b V G I HG1 HG2.
  move: (mem_split I) => [bs1] [bs2] [H Hnin]; subst bs.
  have HValid : valid_bt (bt_upd bt b) by apply: btupd_validP.
  have HGb : has_gb (bt_upd bt b) by apply: btupd_gbP.
  move: (btBlockchain_btupd_geq b V G) => H.
  move: (btBlockchain_geq (bs1 ++ b :: bs2) HValid HGb) => P.
  rewrite -cat1s foldl_cat foldl_comm foldl_cat /= -foldl_cat in HG2 *.
  rewrite -cat1s foldl_cat foldl_comm foldl_cat /= -foldl_cat btupd_dupE in P *.
    by apply: FCR_geq_trans HG2 P.
Qed.

Lemma btBlockchain_in_all_blockchains :
  forall (bt : BlockTree),
    has_gb bt ->
    btBlockchain bt \in all_blockchains bt.
Proof.
  move => bt G; rewrite /btBlockchain /good_blockchains.
  move: (all_blockchains_gb G) => /mem_split [bs1] [bs2] [E _].
  rewrite E; clear E.
  have B : [:: GenesisBlock] >b foldr take_better_bc [:: GenesisBlock] _ = false
        by move => bc; apply /negP; rewrite -FCR_ngt; apply: take_better_geq.
  elim: bs1 bs2 => [|bc bs1 IH] bs2.
  - rewrite /= eqxx init_valid_blockchain /=.
    rewrite {1}/take_better_bc B.
    elim: bs2 => [|bc' bs2 IH2] /=; first by rewrite mem_head.
    + case: ifP => V /=.
      rewrite {1}/take_better_bc; case: ifP => H.
        by rewrite inE mem_head orbC.
        by move: IH2; rewrite inE => /orP; case => IH2; rewrite 2?inE IH2; [|rewrite orbA orbC].
    + by move: IH2; rewrite inE => /orP; case => IH2; rewrite 2?inE IH2; [|rewrite orbA orbC].
  - rewrite /=; case: ifP => V /=.
    rewrite {1}/take_better_bc; case: ifP => H; by [rewrite mem_head | rewrite inE IH orbC].
      by rewrite inE IH orbC.
Qed.
      
Lemma btBlockchain_good :
  forall (bt : BlockTree),
    good_blockchain (btBlockchain bt).
Proof.
  move => bt; rewrite /btBlockchain /good_blockchains.
  elim: (all_blockchains bt) => [|bc bcs IH] //=.
  case: ifP => /=; [move => /andP [H _] | by move => _; apply: IH].
    by rewrite /take_better_bc; case: ifP.
Qed.

Lemma btBlockchain_valid :
  forall (bt : BlockTree),
    valid_blockchain (btBlockchain bt).
Proof.  
  move => bt; rewrite /btBlockchain /good_blockchains.
  elim: (all_blockchains bt) => [|bc bcs IH] //=; first by apply: init_valid_blockchain.
  case: ifP => /=; [move => /andP [_ H] | by move => _; apply: IH].
    by rewrite /take_better_bc; case: ifP.
Qed.

Lemma compute_blockchain_uniq_hash :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt -> has_gb bt ->
    uniq (map hashB (compute_blockchain bt b)).
Proof.
  move => bt b V G.
  rewrite map_inj_uniq /compute_blockchain; last by exact hashB_inj.
  have Ek: domf bt = domf bt by done.
  have Es: #|` domf bt| = #|` domf bt| by done.
  move: {-2}#|` domf bt| Es => n.
  move: {-2}(domf bt) Ek => dom Es En.
  elim: n b bt dom Es En V G => [|n IH] b bt dom Es En V G //=.
    by case: ifP => //; case: ifP.
  subst dom; case: ifP => B //.
  rewrite B; case P: (prev_blk b \in bt); last by rewrite not_fnd // P.
  rewrite in_fnd; case: ifP => NG //.
  rewrite rcons_uniq; apply /andP; split; last first.
  apply: IH => //.
    by rewrite domf_rem.
    by move: (cardfsD1 (#b b) (domf bt)); rewrite B add1n -En => /eq_add_S.
    by apply: btrem_validP.
    by apply: btrem_gbP => //.
    apply /negP; rewrite /not.
    move: (cardfsD1 (#b b) (domf bt)); rewrite B add1n -En => /eq_add_S => ->.
    have E : (domf bt `\ #b b) = domf bt.[~ #b b] by rewrite domf_rem.
    rewrite {2 3}E.
    change (b \in compute_blockchain bt.[~ #b b] bt.[P] -> False).
    move => /(compute_blockchain_block_in_bt (btrem_validP V) (btrem_gbP G NG)).
    by rewrite inE domf_rem inE in_fset1 eqxx.
Qed.
  
Lemma good_blockchain_nocycle :
  forall (bt : BlockTree) (bc : Blockchain) (b c : Block),
  valid_bt bt -> has_gb bt ->
  bc = compute_blockchain bt b ->
  good_blockchain bc ->
  c \in bc ->
  c == GenesisBlock \/ prev_blk c != #b b.
Proof.
  move => bt bc b c V G.
  case: (compute_blockchain_last_blk bt b); first by move => -> ->.
  move => /hashB_inj E.
  move: (compute_blockchain_uniq_hash b V G) => U.
  move: (compute_blockchain_hashchain b V G) => Hc.
  case: bc => [|a bc] //=.
  move => Hac /eqP GA; subst a.
  rewrite inE => /orP; case; first by left.
  rewrite -Hac in Hc U E.
  move => /(hashchain_uniq_hash_nocycle Hc U).
    by rewrite E; right.
Qed.
    
Lemma btBlockchain_mint_ext :
  forall (bt : BlockTree) (bc : Blockchain) (b : Block),
    valid_bt bt -> has_gb bt ->
    bc = compute_blockchain bt (last_blk bc) ->
    good_blockchain bc ->
    prev_blk b = #b last_blk bc ->
    VAF b -> b != GenesisBlock ->
    compute_blockchain (bt_upd bt b) b = rcons bc b.
Proof.
  move => bt bc b V G E H P B NG.
  suff Hsuff : compute_blockchain (bt_upd bt b) b =
               rcons (compute_blockchain (bt_upd bt b) (last_blk bc)) b
    by rewrite Hsuff good_bt_add_block_same_chain //; rewrite -E.
  apply: compute_blockchain_rcons => //.
  by apply: btupd_validP.
  by rewrite /bt_upd inE dom_setf fset1U1.
  case /orP: (compute_blockchain_last_within bt (last_blk bc)).
  rewrite -E => /eqP ->; rewrite /last_blk /bt_upd /=.
  move: G; rewrite /has_gb fndSomeP; case => x y.
    by rewrite inE dom_setf inE x orbC.
  move => /(compute_blockchain_block_in_bt V G).
    by rewrite /bt_upd inE inE dom_setf inE orbC => -> .
  rewrite E in H.
  rewrite good_bt_add_block_same_chain // -E.
  apply /negP => I; rewrite -E in H.
  case: (good_blockchain_nocycle V G E H I).
    by move /negPf: NG => ->.
    by rewrite P eqxx.
Qed.

Lemma btupd_mint_goodness :
  forall (bt : BlockTree) (b : Block),
    valid_bt bt -> has_gb bt ->
    good_blockchain (btBlockchain bt) ->
    VAF b -> all [pred t | commTxsValid t (btBlockchain bt)] (comm_txs b) ->
    prev_blk b = #b last_blk (btBlockchain bt) ->
    good_blockchain (compute_blockchain bt.[#b b <- b] b) /\
    valid_blockchain (compute_blockchain bt.[#b b <- b] b).
Proof.
  move => bt b V G H PV A P.
  case NG: (b == GenesisBlock).
  move /eqP: NG => NG; subst b.
  rewrite /compute_blockchain.
  move: (has_gb_n1 (btupd_gbP GenesisBlock G)) => [n] /= ->.
  rewrite compute_blockchain_gb;
    by [rewrite init_valid_blockchain /= eqxx|rewrite /has_gb fnd_set eqxx|rewrite fset1U1].
  move /negbT: NG => NG.
  have In : btBlockchain bt \in all_blockchains bt
    by apply: btBlockchain_in_all_blockchains G.
  have C : btBlockchain bt = compute_blockchain bt (last_blk (btBlockchain bt))
    by rewrite (compute_blockchain_inall V G In).
  rewrite (btBlockchain_mint_ext V G C H P PV NG).
  rewrite /good_blockchain; case X: (rcons _ _) => [|x xs].
  contradict X; by case: (btBlockchain bt) => //.
  have: (good_blockchain (btBlockchain bt) = true) by done.
  rewrite /good_blockchain /=; case Y: (btBlockchain _) => [|h t]; first done.
  move /eqP => Eq; subst h.
  move: X; rewrite Y rcons_cons; case => EG E.
  subst x xs; split => //.
  move: (btBlockchain_valid bt) => HV.
  rewrite Y in HV A; rewrite -rcons_cons.
  apply: valid_blockchain_rcons => //.
Qed.

(* Lemma btBlockchain_mint_gt :
  forall (bt : {fmap HashValue -> Block}) (b : Block),
    valid_bt bt -> has_gb bt ->
    VAF b ->
    all [pred t | commTxsValid t (btBlockchain bt)] (comm_txs b) ->
    prev_blk b = #b last_blk (btBlockchain bt) ->
    b != GenesisBlock ->
    btBlockchain (bt_upd bt b) >b btBlockchain bt.
Proof.
  move => bt b V G B A P NG.
  have HGood : good_blockchain (rcons (btBlockchain bt) b)
    by move: (btBlockchain_good bt); rewrite /good_blockchain; case: (btBlockchain bt).
  have HValid : valid_blockchain (rcons (btBlockchain bt) b)
    by apply: btBlockchain_valid_last => //; apply: btBlockchain_valid.
  have HExt : compute_blockchain (bt_upd bt b) b = rcons (btBlockchain bt) b.
  apply: btBlockchain_mint_ext => //;
    [rewrite compute_blockchain_inall => //; apply: btBlockchain_in_all_blockchains => //
    |apply: btBlockchain_good].
  have HIn : rcons (btBlockchain bt) b \in
      filter (fun c => good_blockchain c && valid_blockchain c) (all_blockchains (bt_upd bt b)).
  - rewrite mem_filter HGood HValid -HExt /all_blockchains /=; apply /mapP.
    exists b => //; apply /mapP.
    exists (#b b); by [rewrite fset1U1 | rewrite /get_block /bt_upd fnd_set eqxx].
    have: btBlockchain (bt_upd bt b) >=b rcons (btBlockchain bt) b.
      by apply: btBlockchain_largest => //.
    by case; [move => ->
             |move => H; apply: (@FCR_trans _ (rcons (btBlockchain bt) b)); split => //];
    rewrite -cats1; apply: FCR_ext. 
Qed. *)

Lemma btBlockchain_in_good_blockchains :
  forall (bt : BlockTree),
    valid_bt bt -> has_gb bt ->
    btBlockchain bt \in good_blockchains bt.
Proof.
  rewrite /good_blockchains => bt V G.
  rewrite mem_filter; apply /andP; split; last by apply: btBlockchain_in_all_blockchains.
  apply /andP; split; first by apply: btBlockchain_good.
    by apply: btBlockchain_valid.
Qed.

Lemma with_new_helper :
  forall (cbt bt : BlockTree) (bs : seq Block) (b : Block),
    valid_bt cbt -> has_gb cbt ->
    valid_bt bt -> has_gb bt ->
    good_bt cbt -> #b b \notin cbt ->
    good_bt cbt.[#b b <- b] ->
    btBlockchain bt.[#b b <- b] >b btBlockchain cbt ->
    cbt = foldl bt_upd bt bs ->
    btBlockchain bt.[#b b <- b] = btBlockchain cbt.[#b b <- b].
Proof.
  move => cbt bt bs b Vc Gc V G Hc Nin Hcu Gt Ext.
  have Eq : forall bt, bt.[#b b <- b] = bt_upd bt b by done.
  have Ingood : btBlockchain bt.[#b b <- b] \in good_blockchains cbt.[#b b <- b].
  rewrite Ext Eq Eq !bt_updE foldl_comm /=.
  apply: good_blockchains_foldl_btupd_subset.
    by apply: btupd_validP.
    rewrite mem_filter; apply /andP; split.
      by apply /andP; split; [apply: btBlockchain_good|apply: btBlockchain_valid].
      by apply: btBlockchain_in_all_blockchains; apply: btupd_gbP.
  have Gt1 : btBlockchain bt.[#b b <- b] >b [:: GenesisBlock].
  move: (btBlockchain_in_good_blockchains Vc Gc).
  rewrite mem_filter; case /andP; case /andP => /good_blockchain_geq_gb.
    by move => /(FCR_gt_geq_trans Gt).
  move: (good_blockchain_split_perm Vc Gc Hc Nin Hcu) => P.
  move: Ingood; move /perm_mem: (P) => /(_ (btBlockchain bt.[#b b <- b])) -> Ingood.
  have I : [:: GenesisBlock] \in good_blockchains cbt.
  rewrite mem_filter init_valid_blockchain /= eqxx /=.
    by apply: all_blockchains_gb.
  rewrite {2}/btBlockchain in Gt; rewrite {2}/btBlockchain.
  rewrite (perm_foldr_take_better _ P).
    by rewrite (@best_element_in _ _ [::] _ Gt1 Gt Ingood).
Qed.  
  
Lemma btupd_with_new :
  forall (cbt bt : BlockTree) (bs : seq Block) (b : Block),
    valid_bt cbt -> has_gb cbt ->
    valid_bt bt -> has_gb bt ->
    good_bt cbt -> good_bt cbt.[#b b <- b] ->
    btBlockchain bt.[#b b <- b] >b btBlockchain cbt ->
    cbt = foldl bt_upd bt bs ->
    btBlockchain bt.[#b b <- b] = btBlockchain cbt.[#b b <- b].
Proof.
  move => cbt bt bs b CanV CanG V G CanH UpdH Gt Hc.
  case B: (#b b \in cbt); last first.
    by apply: with_new_helper => //; [rewrite B|rewrite Hc].
  have Q : cbt = cbt.[#b b <- b] by rewrite btupd_in_noeffect.
  move: Gt; rewrite Q Hc.
  have E : forall bt, bt.[#b b <- b] = bt_upd bt b by done.
  rewrite !E [bt_upd (foldl _ _ _) b]bt_updE foldl_comm /=.
  move => /FCR_ngeq => contra.
    by move: (btBlockchain_geq bs (btupd_validP V) (btupd_gbP b G)) => /contra.
Qed.
    
Lemma within_helper :
  forall (cbt bt : BlockTree) (b : Block) (bs : seq Block),
    valid_bt cbt -> has_gb cbt ->
    valid_bt bt -> has_gb bt ->
    good_bt cbt -> good_bt cbt.[#b b <- b] ->
    VAF b -> all [pred t | commTxsValid t (btBlockchain bt)] (comm_txs b) ->
    btBlockchain cbt >=b btBlockchain bt.[#b b <- b] ->
    prev_blk b = #b last_blk (btBlockchain bt) ->
    cbt = foldl bt_upd bt bs ->
    btBlockchain cbt.[#b b <- b] >b btBlockchain cbt ->
    #b b \in cbt.
Proof.
  move => cbt bt b bs Vc Gc V G Hc Hcu Vb A Geq P Ext Gt.
  apply /negPn /negP => C.
  move: (good_blockchain_split_perm Vc Gc Hc C Hcu) => Perm.
  case: (btupd_mint_goodness V G (btBlockchain_good bt) Vb A P) => Gbc Vbc.
  move: (FCR_gt_geq_trans Gt Geq) => Gt'.
  have H1 : compute_blockchain bt.[#b b <- b] b \in good_blockchains bt.[#b b <- b].
  rewrite /good_blockchains mem_filter Gbc Vbc /= /all_blockchains.
  apply /mapP; exists b => //.
  apply /mapP; exists (#b b); first by rewrite dom_setf fset1U1.
    by rewrite /get_block fnd_set eqxx.
  move: (btBlockchain_largest H1) => {H1} /(FCR_gt_geq_trans Gt') H.    
  have W : forall bt, bt.[#b b <- b] = bt_upd bt b by done.
  have Eq : compute_blockchain bt.[#b b <- b] b = compute_blockchain cbt.[#b b <- b] b.
  rewrite Ext !W !bt_updE foldl_comm /=.
  apply /esym; apply: good_bt_add_seq_same_chain;
    by [apply btupd_validP|apply btupd_gbP| rewrite -W].
  move: H; rewrite Eq /btBlockchain (perm_foldr_take_better _ Perm).
  rewrite /= {1}/take_better_bc.
  case: ifP; first by move => _; apply: FCR_nrefl.
  move => /FCR_ngtT; case; first by move => ->; apply: FCR_nrefl.
  move => contra _.
  move: Gt; rewrite {1}/btBlockchain (perm_foldr_take_better _ Perm) -Eq.
  rewrite /= {1}/take_better_bc.
  case: ifP.
    by move => Y _; move: (FCR_trans Y contra); rewrite Eq => /FCR_nrefl.
    by move => _ /FCR_nrefl.
Qed.

Lemma btupd_within :
  forall (cbt bt : BlockTree) (b : Block) (bs : seq Block),
    valid_bt cbt -> has_gb cbt ->
    valid_bt bt -> has_gb bt ->
    good_bt cbt -> good_bt cbt.[#b b <- b] ->
    VAF b -> all [pred t | commTxsValid t (btBlockchain bt)] (comm_txs b) ->
    btBlockchain cbt >=b btBlockchain bt.[#b b <- b] ->
    prev_blk b = #b last_blk (btBlockchain bt) ->
    cbt = foldl bt_upd bt bs ->
    ~ btBlockchain cbt.[#b b <- b] >b btBlockchain cbt.
Proof.
  move => cbt bt b bs Vc Gc V G Hc Hcu Vb A Geq P Ext C.
  case Nin: (#b b \in cbt); first by move: C; rewrite btupd_in_noeffect => //; apply: FCR_nrefl.
  move: (within_helper Vc Gc V G Hc Hcu Vb A Geq P Ext C).
    by rewrite Nin.
Qed.

End btBlockchain.
