From mathcomp.ssreflect Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* strict prefix *)
Definition sprefix {T : eqType} (s1 s2 : seq T) :=
  exists b s, s2 = s1 ++ (b :: s).
Notation "'[' s1 '<<<' s2 ']'" := (sprefix s1 s2).

(* no sequence is strict prefix of nil *)
Lemma not_nil_sprefix {T : eqType} (s : seq T) : ~ sprefix s [::].
Proof. by case => b [s']; case: s. Qed.

(* strict prefix relation is non-reflexive *)
Lemma sprefix_nrefl {T : eqType} (s : seq T) : ~ sprefix s s.
Proof.
  move => [b] [s']; elim: s => //= => a t IH.
    by case.
Qed.    

(* strict prefix relation is transitive *)
Lemma sprefix_trans {T : eqType} (s1 s2 s3 : seq T) :
  [s1 <<< s2] -> [s2 <<< s3] -> [s1 <<< s3].
Proof.
  case => b1 [t1] ->; case => b2 [t2] ->.
  rewrite -catA cat_cons.
  by exists b1, (t1 ++ b2 :: t2).
Qed.

(* strict prefix, bool version *)
Fixpoint sprefixb {T : eqType} (s1 s2 : seq T) :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then
      (x == y) && sprefixb s1' s2'
    else true
  else false.

(* strict prefix reflection view *)
Lemma sprefixP {T : eqType} (s1 s2 : seq T) :
  reflect [s1 <<< s2] (sprefixb s1 s2).
Proof.
  elim: s2 s1 => //= [|b2 s2 IH] s1.
  case: s1 => //= [|b1 s1]; first by constructor 2; apply: not_nil_sprefix.
    by constructor 2; apply: not_nil_sprefix.
  case: s1 => //= [|b1 s1]; first by constructor 1; exists b2, s2.
    case Heq: (b1 == b2) => /=; last first.
    - constructor 2 => [[a] [s3]] /=; rewrite -cat_cons; case => Hneq; subst b2.
        by rewrite eqxx in Heq.
    - move /eqP: Heq => ->.
      case: IH => H; [constructor 1 | constructor 2].
        by  case: H => a [s3] ->; exists a, s3; rewrite cat_cons.
      case => a [s3]; rewrite cat_cons; case => Hspre; subst s2.
        by apply: H; exists a, s3.
Qed.

(* non-strict prefix *)
Definition prefix {T : eqType} (s1 s2 : seq T) :=
  exists s, s2 = s1 ++ s.
Notation "'[' s1 '<<=' s2 ']'" := (prefix s1 s2).

(* nil is always non-strict prefix *)
Lemma nil_prefix {T : eqType} (s : seq T) : [[::] <<= s].
Proof. by exists s. Qed.

(* prefix of nil is nil *)
Lemma prefix_mt {T : eqType} (s : seq T) : [s <<= [::]] -> s = [::].
Proof.
  case: s => //= [b s]. by case => t.
Qed.

(* non-strict prefix relation is reflexive *)
Lemma prefix_refl {T : eqType} (s : seq T) : [s <<= s].
Proof. by exists [::]; rewrite cats0. Qed.

(* non-strict prefix relation is transitive *)
Lemma prefix_trans {T : eqType} (s1 s2 s3 : seq T) :
  [s1 <<= s2] -> [s2 <<= s3] -> [s1 <<= s3].
Proof.
  case => [t1] ->; case => [t2].
    by rewrite -catA; exists (t1 ++ t2).
Qed.

(* non-strict prefix, bool version *)
Fixpoint prefixb {T : eqType} (s1 s2 : seq T) :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then
      (x == y) && prefixb s1' s2'
    else true
  else s1 == [::].

(* prefix of nil is nil *)
Lemma prefixb_mt {T : eqType} (s : seq T) :
  prefixb s [::] -> s == [::].
Proof. by case: s. Qed.

(* non-strict prefix reflection view *)
Lemma prefixP {T : eqType} (s1 s2 : seq T) :
  reflect [s1 <<= s2] (prefixb s1 s2).
Proof.
  elim: s2 s1 => //= [|b s2 IH] s1.
  case H: (prefixb s1 [::]) => //=; [constructor 1 | constructor 2].
    by move /prefixb_mt/eqP: H ->; apply: nil_prefix.
      by case: s1 H => //b s1 /= _ [x].
  case: s1 => //= [|a s1]; first by constructor 1; apply: nil_prefix.
  case H: (a == b) => //=; last first.
  constructor 2 => [[s]]; rewrite cat_cons.
  case => Heq; subst b.
    by rewrite eqxx in H.
  move /eqP :H => H; subst b.
  case: IH => H; [constructor 1 | constructor 2].
    by case: H => s ->; exists s; rewrite cat_cons.
  case => s; rewrite cat_cons. case => Heq; subst s2.
    by apply: H; exists s.
Qed.

(* strict prefix imply non-strict prefix *)
Lemma prefix_impl_sprefix {T : eqType} (s1 s2 : seq T) :
  [s1 <<< s2] -> [s1 <<= s2].
Proof.
  case => b [s] ->.
    by exists (b :: s).
Qed.

(* non-strict prefix imply strict prefix or equal *)
Lemma sprefix_impl_prefix_or_eq {T : eqType} (s1 s2 : seq T) :
  [s1 <<= s2] -> [s1 <<< s2] \/ s1 = s2.
Proof.
  case; case; first by rewrite cats0 => ->; right.
    by move => b s ->; left; exists b, s.
Qed.

(* non-strict prefix relation is antisymmetric *)
Lemma prefix_asym {T : eqType} (s1 s2 : seq T) :
  [s1 <<= s2] -> [s2 <<= s1] -> s1 = s2.
Proof.
  move => H1 H2; move: (sprefix_impl_prefix_or_eq H1) (sprefix_impl_prefix_or_eq H2).
  clear H1 H2; case => H1; case => H2; try by [].
    by move: (sprefix_nrefl (sprefix_trans H1 H2)).
Qed.

(* strict prefix relation is not symmetric *)
Lemma sprefix_nsym {T : eqType} (s1 s2 : seq T) :
  sprefixb s1 s2 -> sprefixb s2 s1 -> False.
Proof.
  move /sprefixP => A /sprefixP => B. by move: (sprefix_nrefl (sprefix_trans A B)).
Qed.

(* prefix equivelance *)
Lemma prefix_equiv {T : eqType} (s1 s2 : seq T) :
  prefixb s1 s2 = (s1 == s2) || (sprefixb s1 s2).
Proof.
  apply /Bool.eq_iff_eq_true; split.
  move /prefixP => [s] ->. case: s => [|b s]; first by rewrite cats0 eqxx.
    by apply /orP; right; apply /sprefixP; exists b, s.
  move /orP; case.
    by move /eqP => ->; apply /prefixP; apply: prefix_refl.
    by move /sprefixP => [b] [s] ->; apply /prefixP; exists (b :: s).
Qed.

(* decidable fork *)
Definition forkb {T : eqType} (s1 s2 : seq T) :=
  ~~[|| sprefixb s1 s2, sprefixb s2 s1 | s1 == s2].

Definition fork {T : eqType} (s1 s2 : seq T) :=
  ~ ([s1 <<= s2] \/ [s2 <<= s1]).

(* fork reflection view *)
Lemma forkP {T : eqType} (s1 s2 : seq T) :
  reflect (fork s1 s2) (forkb s1 s2).
Proof.
  case H: (forkb s1 s2); [constructor 1 | constructor 2].
  move /negP: H => H. rewrite /fork => G. apply: H.
  case: G; case => s; case: s => [| x s]; rewrite ?cats0 => ->.
  do? [by rewrite eqxx ![_ || true] orbC].
      by apply /orP; left; apply /sprefixP; exists x, s.
        by apply /orP; right; apply /orP; right.
          by apply /orP; right; apply /orP; left; apply /sprefixP; exists x, s.
  move => G. move /negP: H => H; apply: H. rewrite /fork in G.
  case /orP.
  move /sprefixP => [x] [s] Heq; apply: G; subst s2.
    by left; exists (x :: s).
  rewrite orbC eq_sym -prefix_equiv => P; apply: G.
    by right; apply /prefixP.
Qed.

(* fork means not equal *)
Lemma fork_neq {T : eqType} (s1 s2 : seq T) :
  forkb s1 s2 -> s1 != s2.
Proof.
  move => H. apply /negP => /eqP G; subst s2.
    by case /orP: H; right; rewrite orbC eqxx.
Qed.

(* fork relation is not reflexive *)
Lemma fork_nrefl {T : eqType} (s : seq T) :
  ~ forkb s s.
Proof. by move => H; move: (fork_neq H) => /eqP. Qed.

(* fork relation is symmetric *)
Lemma fork_sym {T : eqType} (s1 s2 : seq T) :
  forkb s1 s2 -> forkb s2 s1.
Proof. by rewrite /forkb eq_sym orbCA. Qed.

(* if s1 and s2 fork, and s2 is prefix of s3, then s1 and s3 fork *)
Lemma fork_prefix {T : eqType} (s1 s2 s3 : seq T) :
  forkb s1 s2 -> [s2 <<= s3] -> forkb s1 s3.
Proof.
  move /forkP => H G; apply /forkP; move: H G.
  move /Decidable.not_or.
  case => H2 H1 [s] ->.
  elim: s s2 H1 H2 => [|x s IH] s2 H1 H2.
    by rewrite cats0; case.
  rewrite -cat_rcons; apply: IH => H.
  apply: H1; case: H => y ->; rewrite cat_rcons.
    by exists (x :: y).
  rewrite /prefix in H H1 H2.
  case: H => z. elim /last_ind: z => [|zs z IH].
  rewrite cats0 => G; subst s1.
    by apply: H1; exists [:: x]; rewrite cats1.
  rewrite -rcons_cat => /eqP. rewrite eqseq_rcons.
  move /andP => [/eqP G] /eqP P.
    by subst x s2; apply: H2; exists zs.
Qed.

Inductive bc_rel {T : eqType} (bc1 bc2 : seq T) : bool -> bool -> bool -> bool -> Set :=
| CmpBcEq of bc1 == bc2 : bc_rel bc1 bc2 true false false false
| CmpBcFork of forkb bc1 bc2 : bc_rel bc1 bc2 false true false false
| CmpBcSpreL of sprefixb bc1 bc2 : bc_rel bc1 bc2 false false true false
| CmpBcSpreR of sprefixb bc2 bc1 : bc_rel bc1 bc2 false false false true.

Lemma bc_relP {T : eqType} (bc1 bc2 : seq T) :
  bc_rel bc1 bc2 (bc1 == bc2) (forkb bc1 bc2) (sprefixb bc1 bc2) (sprefixb bc2 bc1).
Proof.
  case E: (bc1 == bc2); case F: (forkb bc1 bc2);
  case SL: (sprefixb bc1 bc2); case SR: (sprefixb bc2 bc1);
    do? by [
            constructor |
            contradict E; move: (fork_neq F) => /eqP => A B; apply: A; move /eqP in B |
            contradict E; move: (sprefix_nsym SL SR) |
            contradict SL; move /eqP: E => <- => /sprefixP; apply: sprefix_nrefl |
            contradict SR; move /eqP : E => <- => /sprefixP; apply: sprefix_nrefl
          ].
    by contradict F; move /norP => [] C; rewrite SL in C.
    by contradict F; move /norP => [] _ => /norP; elim => C; rewrite SR in C.
    by contradict F; rewrite /forkb E SL SR.
Qed.  
