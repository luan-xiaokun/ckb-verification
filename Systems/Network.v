From mathcomp Require Import all_ssreflect.

From mathcomp Require Import finmap finset finfun fintype.

From CKB Require Import Types Parameters Forest Setfs Messages States.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* define global state *)
Record GState :=
  mkGState {
      user_state : {fsfun UserId -> UState for initUState};
      inflight_msg : seq Packet;
      consumed_msg : seq Packet;
    }.

(* some property holds for some users *)
Definition holds (u : UserId) (gs : GState) (property : UState -> Prop) :=
  property (user_state gs u).

(* global state well defined *)
Definition Coh (gs : GState) :=
  [/\ forall (u : UserId),
       holds u gs (fun us => uniq (peers us)),
     forall (u : UserId),
       holds u gs (fun us => valid_bt (btree us)) &
     forall (u : UserId),
       holds u gs (fun us => has_gb (btree us))
  ].

(* record to form scheduler *)
Record Schedule :=
  mkS {
      ts : Time;           (* time stamp *)
      allowed : UserId;    (* a user is allowed to perform transition *)
    }.

(* global system transition *)
Inductive system_step (gs gs' : GState) (s : Schedule) : Prop :=
| Idle of Coh gs /\ gs = gs'
| Deliver (p : Packet) of
          Coh gs & (dst p) = allowed s &
          p \in inflight_msg gs &
          let: (us', ms) := proc_msg (user_state gs (dst p)) (src p) (msg p) (ts s) in
          gs' = mkGState (setfs (user_state gs) (dst p) us')
                         (seq.rem p (inflight_msg gs) ++ ms)
                         (rcons (consumed_msg gs) p)
| Intern (u : UserId) (t : InternalTransition) of
         Coh gs & u = allowed s &
         let: (us', ms) := proc_int (user_state gs u) t (ts s) in
         gs' = mkGState (setfs (user_state gs) u us')
                        (ms ++ (inflight_msg gs))
                        (consumed_msg gs).

Definition Scheduler := seq Schedule.

(* define reachability relation *)
Inductive reachable_state : GState -> GState -> Prop :=
| reach_refl : forall gs, reachable_state gs gs
| reach_step : forall gs1 gs2 s, system_step gs1 gs2 s -> reachable_state gs1 gs2
| reach_tran : forall gs1 gs2 gs3, reachable_state gs1 gs2-> reachable_state gs2 gs3 -> reachable_state gs1 gs3.

Fixpoint reachable_rec (s : Scheduler) (gs gs' : GState) : Prop :=
  if s is (fs :: tls) then
    exists (via : GState), reachable_rec tls gs via /\ system_step via gs' fs
  else gs = gs'.

Definition rechable (gs gs' : GState) :=
  exists (s : Scheduler), reachable_rec s gs gs'.

(* define initial global state *)
Definition initGState := mkGState [fsfun for initUState] [::] [::].

Lemma initGState_user :
  forall (u : UserId),
    user_state initGState u = initUState u.
Proof. by move => u; rewrite /= fsfun_dflt; last rewrite in_finsupp0. Qed.
  
(* property that holds for inital UState should also holds for inital GState *)
Lemma holds_init_state : forall (P : UState -> Prop) (u : UserId),
  P (initUState u) ->
  holds u initGState P.
Proof.
  move => P u HP.
  have H_in: u \in enum userid_finType by rewrite mem_enum.
  have H_unq: uniq (enum userid_finType) by apply: enum_uniq.
  move: H_in H_unq; elim: (enum userid_finType) => //=.  
  move => u' utl IH; rewrite inE. move /orP; case; last first.
  - move => H_in /andP [_ H_unq].
      by apply: IH.      
  - move /eqP => H_eq.
    rewrite H_eq; move /andP => [H_in H_unq].
    rewrite /holds.
      by rewrite /initGState fsfunE -H_eq.
Qed.

(* the initial GState is coherent *)
Lemma Coh_init : Coh initGState.
Proof.
  split; move => u; apply holds_init_state; rewrite /initUState /initBlockTree /btree.
  - by rewrite rem_uniq // enum_uniq.  
  - move => h b; rewrite /valid_bt.
    rewrite fnd_set; case E: (h == #b GenesisBlock).
      by case => <-; move /eqP: E ->.
    by rewrite fnd_fmap0.
  - by rewrite /has_gb fnd_set eqxx.
Qed.

(* processing messages preserve peer uniqness *)
Lemma proc_msg_peers_uniq :
  forall (us us' : UState) (from : UserId) (msg : Message) (t : Time) p,
  (proc_msg us from msg t) = (us', p) -> 
  uniq (peers us) -> uniq (peers us').
Proof.
  case => u prs bt txp us' from. case => //=.
  - move => b t p.
    case V: (VAF b); last by case => <-.
    case P: (prop_missing b _); case => <- //.
  - move => tx t p.
    case A: (already_have_transactions tx _); first by case => <-.
      by case => <-.
  - move => hs t p.
      by case => <-.
Qed.

(* internal transitions preserve peer uniqness *)
Lemma proc_int_peers_uniq :
  forall (us us' : UState) (int : InternalTransition) (t : Time) p,
  (proc_int us int t) = (us', p) -> 
  uniq (peers us) -> uniq (peers us').
Proof.
  case => u prs bt txp us'. case => //=.
  - move => b t p.
      by case => <-.
  - move => t p.
    case G: (genProof u _ _ _) => [pf|].
    case: ifP => V; by case => <-.
      by case => <-.
Qed.

(* processing messages preserve hash validity *)
Lemma proc_msg_hash_valid :
  forall (us us' : UState) (from : UserId) (msg : Message) (t : Time) p,
    (proc_msg us from msg t) = (us', p) ->
    valid_bt (btree us) ->
    valid_bt (btree us').
Proof.
  case => u prs bt txp us' from; case => /=.
  - move => b t p.
    case V: (VAF b); last by case => <-.
    case P: (prop_missing b _); case => <- // _ H h0 b0; rewrite /btree fnd_set;
      do? [case I: (h0 == #b b); [by case => <-; move /eqP: I => -> | apply: H]].
  - move => tx t p.
    case A: (already_have_transactions tx _); first by case => <-.
      by case => <-.
  - move => hs t p.
      by case => <-.
Qed.

(* internal transitions preserve hash validity *)
Lemma proc_int_hash_valid :
  forall (us us' : UState) (int : InternalTransition) (t : Time) p,
    (proc_int us int t) = (us', p) ->
    valid_bt (btree us) ->
    valid_bt (btree us').
Proof.
  case => u prs bt txp us'. case => //=.
  - move => ts t p.
      by case => <-.
  - move => t p.
    case G: (genProof u _ _ _) => [pf|]; last by case => <-.
    case: ifP => V; case => <- _ H h0 b0.
    rewrite /btree fnd_set; case I: (h0 == #b _); [by case => <-; move /eqP: I => -> | apply: H].
      by apply: H.
Qed.

(* processing messages preserve btree goodness *)
Lemma proc_msg_btree_good :
  forall (us us' : UState) (from : UserId) (msg : Message) (t : Time) p,
    (proc_msg us from msg t) = (us', p) ->
    has_gb (btree us) -> has_gb (btree us').
Proof.
  case => u prs bt txp us' from. case => /=; rewrite /has_gb.
  - move => b t p.
    case V: (VAF b); last by case => <-.
    case P: (prop_missing b _); case => <- _ H; rewrite /btree;
    rewrite fnd_set; case E: (#b GenesisBlock == #b b);
      by [move /eqP: E => /hashB_inj <- | apply: H].
  - move => ts t p.
    case A: (already_have_transactions ts _); by case => <-.
  - move => hs t p.
      by case => <-.
Qed.

(* internal transitions preserve btree goodness *)
Lemma proc_int_btree_good :
  forall (us us' : UState) (int : InternalTransition) (t : Time) p,
    (proc_int us int t) = (us', p) ->
    has_gb (btree us) -> has_gb (btree us').
Proof.
  case => u prs bt txp us'. case => /=; rewrite /has_gb.
  - move => ts t p.
    by case => <-.
  - move => t p.
    case G: (genProof u _ _ _) => [pf|]; last by case => <-.
    case: ifP => V; last by case => <- H.
    case => <- _ H; rewrite /btree fnd_set.
    case E: (#b GenesisBlock == #b _);
      by [move /eqP: E => /hashB_inj <- | apply: H].
Qed. 
    
(* next step is coherent *)
Lemma Coh_step (gs gs' : GState) (s : Schedule) :
  system_step gs gs' s -> Coh gs'.
Proof.
  move => H; (have: system_step gs gs' s by done) => H'.
  case: H'.
  (* Idle *)
  - by case => Hw <-.
  (* Deliver *)
  - move => p [H1 H2 H3] Hallow Hflight.
    case P: (proc_msg _ _ _) => [us' ps] => ->.
    split; rewrite /holds /user_state => u; rewrite setfsNK; case E: (u == dst p);
                                           try by [apply: H1 | apply: H2 | apply: H3].
    (* peers uniq *)
    suff Hsuff:
      uniq (peers (user_state gs (dst p))) by apply: (proc_msg_peers_uniq P).
      by apply: H1.
    (* hash valid *)
    suff Hsuff:
       valid_bt (btree (user_state gs (dst p))). by apply: (proc_msg_hash_valid P).
      by apply: H2.
    (* btree goodness *)
    suff Hsuff:
      has_gb (btree (user_state gs (dst p))). by apply: (proc_msg_btree_good P).
      by apply: H3.
  (* InternalTransition *)
  - move => u int [H1 H2 H3] Hallow.
    case P: (proc_int _ _ _) => [us' ps] => ->.
    split; rewrite /holds /user_state => u'; rewrite setfsNK; case E: (u' == u);
                                           try by [apply: H1 | apply: H2 | apply: H3].
    (* peers uniq *)
    suff Hsuff:
      uniq (peers (user_state gs u)) by apply: (proc_int_peers_uniq P).
      by apply: H1.
    (* hash valid *)
    suff Hsuff:
      valid_bt (btree (user_state gs u)) by apply: (proc_int_hash_valid P).
      by apply: H2.
    (* btree goodness *)
    suff Hsuff:
      has_gb (btree (user_state gs u)) by apply: (proc_int_btree_good P).
      by apply: H3.
Qed.

(* global step means taking local step *)
Lemma system_step_local_step (gs gs' : GState) (s : Schedule) (u : UserId) :
  system_step gs gs' s -> local_step (user_state gs u) (user_state gs' u).
Proof.
  case.
  (* Idle *)
  - by move => [_] <-; constructor 1.
  (* Deliver *)
  - move => p [H1 H2 H3] Hallow Hflight.
    case P: (proc_msg _ _ _) => [us ps] => ->.
    rewrite /user_state setfsNK; case E: (u == dst p).
    move /eqP: E => E; subst u.
      by constructor 2 with (src p) (msg p) (ts s); rewrite P.
    by constructor 1.
  (* InternalTransition *)
  - move => u' int [H1 H2 H3] Hallow.
    case P: (proc_int _ _ _) => [us ps] => ->.
    rewrite /user_state setfsNK; case E: (u == u').
    move /eqP: E => E; subst u.
      by constructor 3 with int (ts s); rewrite P.
    by constructor 1.
Qed.     

