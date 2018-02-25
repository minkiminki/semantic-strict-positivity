Require Import FunctionalExtensionality.
Require Import Program.
Require Import paco.

Set Implicit Arguments.
Set Primitive Projections.

Require Import index wf IFunctor ISPFunctor.

Section COINDUCTIVE.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.

  CoInductive Nu (o : O) : Type :=
   cCon' { cDes' : Container (@P _ _ (H o)) Nu }.

  Definition cCon o (fx : F o Nu) : Nu o := cCon' o (NT _ fx).

  Definition cDes o (m : Nu o) : F o Nu := NTinv _ (cDes' m).

  Lemma c_eta_expand1 : forall o (x : F o Nu), cDes (cCon x) = x.
  Proof.
    intros. unfold cDes, cCon.
    rewrite <- BIJECTION1.
    destruct (NT Nu x). reflexivity.
  Qed.

  Definition bsm_gen' bsm' o (n1 : Nu o) (n2 : Nu o) :=
    rel bsm' (cDes' n1) (cDes' n2).
  Hint Unfold bsm_gen'.

  Definition bsm' o n1 n2 := paco3 bsm_gen' bot3 o n1 n2.
  Hint Unfold bsm'.

  Lemma bsm_gen_mon' : monotone3 bsm_gen'.
  Proof.
    unfold monotone3. intros.
    apply (REL_MONOTONE_C _ LE IN).
  Qed.
  Hint Resolve bsm_gen_mon' : paco.

  Definition bsm_gen bsm o (n1 : Nu o) (n2 : Nu o) :=
    rel bsm (cDes n1) (cDes n2).
  Hint Unfold bsm_gen.

  Definition bsm o n1 n2 := paco3 bsm_gen bot3 o n1 n2.
  Hint Unfold bsm.

  Lemma bsm_gen_mon : monotone3 bsm_gen.
  Proof.
    unfold monotone3. intros.
    apply (REL_MONOTONE _ _ _ _ LE _ _ IN).
  Qed.
  Hint Resolve bsm_gen_mon : paco.

  Lemma bsm_bsm'_gen_eq o R (n1 n2 : Nu o) : bsm_gen R n1 n2 <-> bsm_gen' R n1 n2.
  Proof.
    split; intro.
    - apply REL_COMMUTE_R in H0. apply H0.
    - unfold bsm_gen', bsm_gen in *.
      apply REL_COMMUTE_R. apply H0.
  Qed.

  Lemma eq_bsm' : forall o (n : Nu o), bsm' n n.
  Proof.
    pcofix CIH. intros. pfold. unfold bsm_gen'.
    destruct (cDes' n). constructor.
    intros. right. apply CIH.
  Qed.

  Axiom bsm'_eq : forall o (n1 n2 : Nu o), bsm' n1 n2 -> n1 = n2.

  Lemma bsm_bsm' o (n1 n2 : Nu o) : bsm n1 n2 <-> bsm' n1 n2.
  Proof.
    split; revert o n1 n2; pcofix EQ; intros; pfold;
      punfold H1; apply bsm_bsm'_gen_eq in H1.
    - eapply (REL_MONOTONE_C _ _ H1). Unshelve.
      intros. right. destruct H0 as [R|[]]. apply EQ, R.
    - eapply (REL_MONOTONE _ _ _ _ _ _ _ H1). Unshelve.
      intros. right. destruct H0 as [R|[]]. apply EQ, R.
  Qed.

  Lemma eq_bsm : forall o (n : Nu o), bsm n n.
  Proof.
    intros. apply bsm_bsm'. apply eq_bsm'.
  Qed.

  Lemma bsm_eq : forall o (n1 n2 : Nu o), bsm n1 n2 <-> n1 = n2.
  Proof.
    intros; split; intro.
    - apply bsm'_eq, bsm_bsm', H0.
    - subst. apply bsm_bsm', eq_bsm'.
  Qed.

  Lemma eta_expand2': forall o (x : Nu o), cCon' o (cDes' x) = x.
  Proof.
    intros. apply bsm'_eq. pfold.
    apply REL_MONOTONE_C with (R := fun _ => eq).
    - intros. subst. left. apply eq_bsm'.
    - apply REL_EQ_EQ_C. reflexivity.
  Qed.
  
  Lemma c_eta_expand2: forall o (x : Nu o), cCon (cDes x) = x.
  Proof.
    unfold cCon, cDes. intros. rewrite BIJECTION2. apply eta_expand2'.
  Qed.  

  Lemma cCon_injective o (fx1 fx2 : F o Nu) (EQ : cCon fx1 = cCon fx2) :
    fx1 = fx2.
  Proof.
    unfold cCon in *. apply (INJECTIVE (H1 := ISO)).
    inversion EQ. reflexivity.
  Qed.

  Lemma cDes_injective o (n1 n2 : Nu o) (EQ : cDes n1 = cDes n2) :
    n1 = n2.
  Proof.
    apply f_equal with (f := @cCon _) in EQ.
    repeat rewrite c_eta_expand2 in EQ. apply EQ.
  Qed.

  Lemma c_simple_destruct (P : forall o, Nu o -> Prop)
             (FIX : forall o1 (fx : F o1 Nu), P _ (cCon fx)) :
    forall o (m : Nu o), P o m.
  Proof.
    intros. rewrite <- c_eta_expand2.
    apply FIX.
  Qed.

  Lemma nu_eq_eq : forall o (n1 n2 : Nu o),
      n1 = n2 <-> rel (fun _ => eq) (cDes n1) (cDes n2).
  Proof.
    intros. split; intro EQ.
    - apply REL_EQ_EQ. f_equal. apply EQ.
    - apply REL_EQ_EQ in EQ. apply cDes_injective, EQ.
  Qed.

  CoFixpoint corec' (T : O -> Type)
             (FIX : forall o, T o -> Container (@P _ _ (H o)) T) :
    forall o, T o -> Nu o :=
    fun o t =>  (cCon' _ (map (corec' FIX) (FIX _ t))).

  Lemma corec'_red (T : O -> Type)
        (FIX : forall o, T o -> Container (@P _ _ (H o)) T) o (t : T o) :
    cDes' (corec' FIX o t) = map (corec' FIX) (FIX o t).
  Proof.
    reflexivity.
  Qed.

  Definition corec (T : O -> Type)
             (FIX : forall o, T o -> F o T) :
    forall o, T o -> Nu o := corec' (fun o t => NT _ (FIX o t)).

  Lemma corec_red (T : O -> Type)
        (FIX : forall o, T o -> F o T) o (t : T o) :
    cDes (corec FIX o t) = map (corec FIX) (FIX o t).
  Proof.
    unfold corec, cDes. rewrite corec'_red.
    rewrite <- MAP_COMMUTE. apply BIJECTION1.
  Qed.

  Lemma cofun_bsm_unique (T : O -> Type) (f1 f2 : forall o, T o -> Nu o)
        (FIX : forall o, T o -> F o T) :
    (forall o (t : T o), cDes (f1 o t) = map f1 (FIX o t)) ->
    (forall o (t : T o), cDes (f2 o t) = map f2 (FIX o t)) ->
    forall o (t : T o), bsm (f1 o t) (f2 o t).
  Proof.
    intros COM1 COM2. pcofix BSM.
    intros. pfold. unfold bsm_gen at 1. rewrite COM1. rewrite COM2.
    rewrite <- MAP_REL.
    apply REL_MONOTONE with (R := fun _ => eq). 
    - intros. subst. right. apply BSM.
    - apply REL_EQ_EQ. reflexivity.
  Qed.

  Lemma cofun_eq_unique (T : O -> Type) (f1 f2 : forall o, T o -> Nu o)
        (FIX : forall o, T o -> F o T) :
    (forall o (t : T o), cDes (f1 o t) = map f1 (FIX o t)) ->
    (forall o (t : T o), cDes (f2 o t) = map f2 (FIX o t)) ->
    forall o (t : T o), f1 o t = f2 o t.
  Proof.
    intros. apply bsm_eq. apply (cofun_bsm_unique _ _ _ H0 H1).
  Qed.

  Lemma nu_universal (T : O -> Type)
        (FIX : forall o, T o -> F o T) :
    exists! (f : forall o, T o -> Nu o),
      (forall o (t : T o), cDes (f o t) = map f (FIX o t)).
  Proof.
    exists (corec FIX). split.
    - apply corec_red.
    - intros f EQ. extensionality o. extensionality t.
      apply cofun_eq_unique with (FIX := FIX); [apply corec_red | apply EQ].
  Qed.

  Lemma c_inj_preserve (T : O -> Type) (f : forall o, T o -> Nu o)
        (FIX : forall o, T o -> F o T)
        (INJ : forall o t1 t2, FIX o t1 = FIX o t2 -> t1 = t2) :
    (forall o (t : T o), cDes (f o t) = map f (FIX o t)) ->
    (forall o t1 t2, f o t1 = f o t2 -> t1 = t2).
  Proof.
    intro COM.
    intros. apply (f_equal (@cDes _)) in H0.
    rewrite COM in H0. rewrite COM in H0.
  Abort. (* is it true...? *)

End COINDUCTIVE.
