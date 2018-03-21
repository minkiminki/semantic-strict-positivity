Require Import FunctionalExtensionality.
Require Import Program.
Require Import paco.

Set Implicit Arguments.
Set Primitive Projections.

Require Import index wf pullback_sfunctor Functor SPFunctor.

Section COINDUCTIVE.

  Variable F : Type -> Type.
  Context `{H : SPFunctor F}.

  CoInductive Nu : Type :=
   cCon' { cDes' : Container (@degree _ H) Nu }.

  Definition cCon (fx : F Nu) : Nu := cCon' (NT _ fx).

  Definition cDes (m : Nu) : F Nu := NTinv _ (cDes' m).

  Lemma c_eta_expand1 : forall (x : F Nu), cDes (cCon x) = x.
  Proof.
    intros. unfold cDes, cCon.
    rewrite <- BIJECTION1.
    destruct (NT Nu x). reflexivity.
  Qed.

  Definition bsm_gen' bsm' (n1 : Nu) (n2 : Nu) :=
    rel bsm' (cDes' n1) (cDes' n2).
  Hint Unfold bsm_gen'.

  Definition bsm' n1 n2 := paco2 bsm_gen' bot2 n1 n2.
  Hint Unfold bsm'.

  Goal True. apply I. Qed.

  Lemma bsm_gen_mon' : monotone2 bsm_gen'.
  Proof.
    unfold monotone2. intros.
    apply (REL_MONOTONE r r' LE _ _ IN).
  Qed.
  Hint Resolve bsm_gen_mon' : paco.

  Definition bsm_gen bsm (n1 : Nu) (n2 : Nu) :=
    rel bsm (cDes n1) (cDes n2).
  Hint Unfold bsm_gen.

  Definition bsm n1 n2 := paco2 bsm_gen bot2 n1 n2.
  Hint Unfold bsm.

  Lemma bsm_gen_mon : monotone2 bsm_gen.
  Proof.
    unfold monotone2. intros.
    apply (REL_MONOTONE _ _ LE _ _ IN).
  Qed.
  Hint Resolve bsm_gen_mon : paco.

  Lemma bsm_bsm'_gen_eq R (n1 n2 : Nu) : bsm_gen R n1 n2 <-> bsm_gen' R n1 n2.
  Proof.
    split; intro.
    - apply REL_COMMUTE_R in H0. apply H0.
    - unfold bsm_gen', bsm_gen in *.
      apply REL_COMMUTE_R. apply H0.
  Qed.

  Lemma eq_bsm' : forall (n : Nu), bsm' n n.
  Proof.
    pcofix CIH. intros. pfold. unfold bsm_gen'.
    destruct (cDes' n). constructor.
    intros. right. apply CIH.
  Qed.

  Axiom bsm'_eq : forall (n1 n2 : Nu), bsm' n1 n2 -> n1 = n2.

  Lemma bsm_bsm' (n1 n2 : Nu) : bsm n1 n2 <-> bsm' n1 n2.
  Proof.
    split; revert n1 n2; pcofix EQ; intros; pfold;
      punfold H1; apply bsm_bsm'_gen_eq in H1.
    - eapply (REL_MONOTONE _ _ _ _ _ H1). Unshelve.
      intros. right. destruct H0 as [R|[]]. apply EQ, R.
    - eapply (REL_MONOTONE _ _ _ _ _ H1). Unshelve.
      intros. right. destruct H0 as [R|[]]. apply EQ, R.
  Qed.

  Lemma eq_bsm : forall (n : Nu), bsm n n.
  Proof.
    intros. apply bsm_bsm'. apply eq_bsm'.
  Qed.

  Lemma bsm_eq : forall (n1 n2 : Nu), bsm n1 n2 <-> n1 = n2.
  Proof.
    intros; split; intro.
    - apply bsm'_eq, bsm_bsm', H0.
    - subst. apply bsm_bsm', eq_bsm'.
  Qed.

  Lemma bsm_prim (R : Nu -> Nu -> Prop) :
    (forall n1 n2, R n1 n2 -> rel R (cDes n1) (cDes n2)) ->
    (forall n1 n2, R n1 n2 -> bsm n1 n2).
  Proof.
    intro COFIX. pcofix CIH.
    intros n1 n2 REL. pfold. unfold bsm_gen.
    apply (REL_MONOTONE R).
    - intros n1' n2' REL'. right. apply CIH. apply REL'.
    - apply COFIX, REL.
  Qed.

  Lemma eta_expand2': forall (x : Nu), cCon' (cDes' x) = x.
  Proof.
    intros. apply bsm'_eq. pfold.
    apply (REL_MONOTONE eq).
    - intros. subst. left. apply eq_bsm'.
    - apply (REL_EQ_EQ _). reflexivity.
  Qed.
  
  Lemma c_eta_expand2: forall (x : Nu), cCon (cDes x) = x.
  Proof.
    unfold cCon, cDes. intros. rewrite BIJECTION2. apply eta_expand2'.
  Qed.  

  Lemma cCon_injective (fx1 fx2 : F Nu) (EQ : cCon fx1 = cCon fx2) :
    fx1 = fx2.
  Proof.
    unfold cCon in *. apply (INJECTIVE (H1 := ISO)).
    inversion EQ. reflexivity.
  Qed.

  Lemma cDes_injective (n1 n2 : Nu) (EQ : cDes n1 = cDes n2) :
    n1 = n2.
  Proof.
    apply (f_equal cCon) in EQ.
    repeat rewrite c_eta_expand2 in EQ. apply EQ.
  Qed.

  Lemma c_simple_destruct (P : Nu -> Prop)
             (FIX : forall (fx : F Nu), P (cCon fx)) :
    forall (n : Nu), P n.
  Proof.
    intros. rewrite <- c_eta_expand2.
    apply FIX.
  Qed.

  Lemma nu_eq_eq : forall (n1 n2 : Nu),
      n1 = n2 <-> rel eq (cDes n1) (cDes n2).
  Proof.
    intros. split; intro EQ.
    - apply (REL_EQ_EQ _). f_equal. apply EQ.
    - apply (REL_EQ_EQ _) in EQ. apply cDes_injective, EQ.
  Qed.

  CoFixpoint corec' (T : Type)
             (FIX : T -> Container (@degree _ H) T) :
    T -> Nu :=
    fun t =>  (cCon' (map (corec' FIX) (FIX t))).

  Lemma corec'_red (T : Type)
        (FIX : T -> Container (@degree _ H) T) (t : T) :
    cDes' (corec' FIX t) = map (corec' FIX) (FIX t).
  Proof.
    reflexivity.
  Qed.

  Definition corec (T : Type)
             (FIX : T -> F T) :
    T -> Nu := corec' (fun t => NT _ (FIX t)).

  Lemma corec_red (T : Type)
        (FIX : T -> F T) (t : T) :
    cDes (corec FIX t) = map (corec FIX) (FIX t).
  Proof.
    unfold corec, cDes. rewrite corec'_red.
    rewrite <- MAP_COMMUTE. apply BIJECTION1.
  Qed.

  Lemma cofun_bsm_unique (T : Type) (f1 f2 : T -> Nu)
        (FIX : T -> F T) :
    (forall (t : T), cDes (f1 t) = map f1 (FIX t)) ->
    (forall (t : T), cDes (f2 t) = map f2 (FIX t)) ->
    forall (t : T), bsm (f1 t) (f2 t).
  Proof.
    intros COM1 COM2. pcofix BSM.
    intros. pfold. unfold bsm_gen at 1. rewrite COM1. rewrite COM2.
    rewrite <- (MAP_REL _).
    apply (REL_MONOTONE eq).
    - intros. subst. right. apply BSM.
    - apply (REL_EQ_EQ _). reflexivity.
  Qed.

  Lemma cofun_eq_unique (T : Type) (f1 f2 : T -> Nu)
        (FIX : T -> F T) :
    (forall (t : T), cDes (f1 t) = map f1 (FIX t)) ->
    (forall (t : T), cDes (f2 t) = map f2 (FIX t)) ->
    forall (t : T), f1 t = f2 t.
  Proof.
    intros. apply bsm_eq. apply (cofun_bsm_unique _ _ _ H0 H1).
  Qed.

  Lemma nu_universal (T : Type)
        (FIX : T -> F T) :
    exists! (f : T -> Nu),
      (forall (t : T), cDes (f t) = map f (FIX t)).
  Proof.
    exists (corec FIX). split.
    - apply corec_red.
    - intros f EQ. extensionality t.
      apply cofun_eq_unique with (FIX := FIX); [apply corec_red | apply EQ].
  Qed.

  Lemma c_inj_preserve (T : Type) (f : T -> Nu)
        (FIX : T -> F T)
        (INJ : forall t1 t2, FIX t1 = FIX t2 -> t1 = t2) :
    (forall (t : T), cDes (f t) = map f (FIX t)) ->
    (forall t1 t2, f t1 = f t2 -> t1 = t2).
  Proof.
    intro COM.
    set (



    intros. apply (f_equal cDes) in H0.
    rewrite COM in H0. rewrite COM in H0.
  Abort. (* is it true...? *)

End COINDUCTIVE.
