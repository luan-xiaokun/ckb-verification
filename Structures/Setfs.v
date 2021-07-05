From mathcomp Require Import all_ssreflect.

From mathcomp Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.
Open Scope fset_scope.

Section SetFs.

Variables (K : choiceType) (V : eqType).

Variable (default : K -> V).

Definition setfs_fmap (fm : {fmap K -> V}) (k : K) (v : V) : {fmap K -> V} :=
  if v == default k then
    if k \in fm then fm.[~ k]
    else fm
  else fm.[k <- v].

Lemma setfs_not_default_remove (fs : {fsfun K -> V for default}) (k : K) (v : V) :
  [forall k0, (setfs_fmap (fmap_of_fsfun fs) k v) k0 != default (fsval k0)].
Proof.
  case: fs => fs /=.
  move /forallP => Hx; apply /forallP.
  rewrite /= /setfs_fmap.
  case Heq: (v == default k).
  - move /eqP: Heq => Heq.
    case Hif: (k \in fs) => //.
    case => k' Hk; move: (Hk) => Hk'; rewrite mem_remf1 in Hk.
    move /andP: Hk => [Hneq Hin]; apply /eqP.
    have Hxx := (Hx (FSetSub Hin)); rewrite /= in Hxx.
    rewrite [default _] /= => Hd. case /eqP: Hxx. rewrite -Hd.
    suff Hsuff: Some fs.[Hin] = Some (fs.[~ k] [` Hk']) by case: Hsuff.
      by rewrite -!in_fnd fnd_rem1 Hneq.
  - move /eqP: Heq => Heq x.
    rewrite ffunE. apply /eqP => Heqx; move: Heqx.
    case Heqk: (eqtype.val x == k); first by move /eqP: Heqk => ->.
    move /eqP: Heqk => Heqk /eqP.
    move: x Heqk => /=; case => /= k0.
    rewrite in_fsetU in_fset1.
    case /orP; first by move /eqP.
    move => Hk0 /eqP => Heqk /eqP Heqv.
    have Hxx := (Hx (FSetSub Hk0)).
    case /eqP: Hxx. rewrite /= -Heqv /odflt /oapp.
      by rewrite in_fnd.
Qed.

Definition setfs (fs : {fsfun K -> V for default}) (k : K) (v : V) : {fsfun K -> V for default} :=
  @Fsfun K V default (setfs_fmap (fmap_of_fsfun fs) k v) (setfs_not_default_remove _ _ _).

Local Arguments Fsfun : clear implicits.

Lemma getfs_set (fs : {fsfun K -> V for default}) (k : K) (v : V) :
  setfs fs k v k = v.
Proof.
  case: fs => fm /=; rewrite /setfs /= => i.
  move: (setfs_not_default_remove _ _ _) => /=.
  rewrite /setfs_fmap /=.
  case Heq: (v == default k); first case Hk: (k \in fm).
  - move => Hkk.
    move /eqP: Heq => ->.
    rewrite /fun_of_fsfun /fmap_of_fsfun /=.
    rewrite /odflt /oapp /= not_fnd //=.
    rewrite inE /=.
    rewrite in_fsetE /= inE.
    apply /negP => /andP [Hmem Hmemk].
    move: Hmemk.
    rewrite in_fsetD inE /=.
    move /andP => [Heqk Hdomf].
      by move /eqP: Heqk.
  - move => Hkk.
    move /eqP: Heq => ->.
    rewrite /fun_of_fsfun /fmap_of_fsfun /=.
    rewrite /odflt /oapp /= not_fnd //=.
      by rewrite Hk.
  -  move => Hkk.
     rewrite /fun_of_fsfun.
     rewrite in_fnd /=.
     rewrite inE /=.
     apply /orP; left.
       by rewrite in_fset1.
     move => Hk.
     rewrite ffunE /=.
     case Heqk: (k == k) => //.
       by move /eqP: Heqk.
Qed.

Lemma setfsNK (fs : {fsfun K -> V for default}) (k k' : K) (v : V) :
  setfs fs k v k' = if k' == k then v else fs k'.
Proof.
  case Hk: (k' == k); first by move /eqP: Hk => ->; rewrite getfs_set.
  case: fs => fm /=; rewrite /setfs /= => i.
  move: (setfs_not_default_remove _ _ _) => /=.
  rewrite /setfs_fmap /=.
  case Heq: (v == default k); first case Hkk: (k \in fm).
  - move => Hk0.
    rewrite /fun_of_fsfun /fmap_of_fsfun /=.
    case Hkk': (k' \in fm).
    rewrite (in_fnd Hkk') /=.
    rewrite in_fnd /=; first by rewrite inE /= inE in_fsetD1 Hkk' Hk.
    move => Hkk''.
    set fm' := [ffun x => _].
    suff Hsuff: Some fm'.[Hkk''] = Some (fm.[Hkk']) by case: Hsuff.
      by rewrite -!in_fnd fnd_rem1 Hk.
    move /negP /negP: Hkk' => Hkk'.
    rewrite (not_fnd Hkk') /=.
    rewrite not_fnd //.
    rewrite /finmap_of_finfun /= inE /=.
    rewrite in_fsetE /= inE in_fsetD /=.
    apply /andP => Hk'.
    move: Hk' => [Hk1 Hk2].
    move: Hk2.
    move /andP => [Heqk Hdk].
      by rewrite Hdk in Hkk'.
  - by move => Hkk'.
  - move => Hkk'.
    rewrite /fun_of_fsfun /fmap_of_fsfun /=.
    case Hk': (k' \in fm).
    rewrite (in_fnd Hk') /=.
    rewrite in_fnd /=; first by rewrite in_fset1U Hk' Hk.
    move => Hk'0.
      by rewrite ffunE /= Hk (in_fnd Hk').
    move /negP /negP: Hk' => Hk'.
    rewrite (not_fnd Hk') /=.
    rewrite not_fnd //=.
      by rewrite inE /= in_fset1U /= Hk Hk'.
Qed.

Lemma setfs_nupd (fs : {fsfun K -> V for default}) (k : K) (v : V) :
  fs k = v -> setfs fs k v = fs.
Proof.  
  rewrite -fsfunP => Heq x.
  rewrite setfsNK; case E: (x == k); last by done.
    by move /eqP: E => ->.
Qed.
End SetFs.
