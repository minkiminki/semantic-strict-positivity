Require Import FunctionalExtensionality.
Require Import Program.
Require Import paco.


Set Implicit Arguments.

Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor.

Section INDUCTIVE.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.
  Variable X : (iType O).

  CoInductive Nu : O -> Type :=
  | Con' o : Container (@P _ _ (H o)) Nu -> Nu o.

  Definition Con o (fx : F o Nu) : Nu o := Con' o (NT _ fx).

  Definition Des' o (m : Nu o) : Container (@P _ _ (H o)) Nu :=
    match m with
    | Con' o s => s end.

  Definition Des o (m : Nu o) : F o Nu := NTinv _ (Des' m).

  Lemma eta_expand2 : forall o (x : Nu o), Con (Des x) = x.
  Proof.
    intros. unfold Des, Con. rewrite BIJECTION2.
    destruct x. reflexivity.
  Qed.

  Lemma eta_expand1 : forall o (x : F o Nu), Des (Con x) = x.
  Proof.
    intros. unfold Des, Con.
    rewrite <- BIJECTION1.
    destruct (NT Nu x). reflexivity.
  Qed.

  CoFixpoint corec' T (COFIX : forall o, T o -> Container (@P _ _ (H o)) T)
             o (t : T o) : Nu o :=
    Con' o (map (corec' COFIX) (COFIX o t)).

  Lemma corec_red' T (COFIX : forall o, T o -> Container (@P _ _ (H o)) T)
        o (t : T o) :
    Des' (corec' COFIX o t) = map (corec' COFIX) (COFIX o t).
  Proof.
    reflexivity.
  Qed.

  Definition corec T (COFIX : forall o, T o -> F o T)
             : forall o (t : T o), Nu o :=
    corec' (fun o t => NT _ (COFIX o t)).

  Lemma corec_red T (COFIX : forall o, T o -> F o T) o (t : T o) :
    Des (corec COFIX o t) = map (corec COFIX) (COFIX o t).
  Proof.
    unfold Des, corec. rewrite corec_red'.
    rewrite <- MAP_COMMUTE. apply BIJECTION1.
  Qed.


  Inductive bsm_gen' bsm' : forall o, Nu o -> Nu o -> Prop :=
  | _bsm_gen' : forall o (c1 c2 : Container (@P _ _ (H o)) Nu) (R: rel bsm' c1 c2),
      bsm_gen' bsm' (Con' o c1) (Con' o c2).
  Hint Constructors bsm_gen'.

  Definition bsm' o n1 n2 := paco3 bsm_gen' bot3 o n1 n2.
  Hint Unfold bsm'.

  Lemma bsm_gen_mon' : monotone3 bsm_gen'.
  Proof.
    unfold monotone3. intros. destruct IN. constructor.
    apply (CONTAINER_REL_MONOTONE _ LE R).
  Qed.
  Hint Resolve bsm_gen_mon' : paco.

  Lemma eq_bsm' : forall o (n : Nu o), bsm' n n.
  Proof.
    pcofix CIH. intros. pfold.
    destruct n. constructor. simpl.
    destruct c. constructor.
    intros. right. apply CIH.
  Qed.

  Inductive bsm_gen bsm : forall o, Nu o -> Nu o -> Prop :=
  | _bsm_gen : forall o (c1 c2 : F o Nu) (R: rel bsm c1 c2),
      bsm_gen bsm (Con c1) (Con c2).
  Hint Constructors bsm_gen.

  Definition bsm o n1 n2 := paco3 bsm_gen bot3 o n1 n2.
  Hint Unfold bsm.

  Lemma bsm_gen_mon : monotone3 bsm_gen.
  Proof.
    unfold monotone3. intros. destruct IN. constructor.
    apply (REL_MONOTONE _ _ _ _ LE _ _ R).
  Qed.
  Hint Resolve bsm_gen_mon : paco.

  Lemma bsm_bsm'_gen_eq o R (n1 n2 : Nu o) : bsm_gen R n1 n2 <-> bsm_gen' R n1 n2.
  Proof.
    split; intro.
    - destruct H0. constructor.
      apply REL_COMMUTE, R0.
    - destruct H0. revert R0.
      destruct (BIJECTION2 _ c1), (BIJECTION2 _ c2).
      intro. constructor.
      apply REL_COMMUTE in R0. apply R0.
  Qed.

  Lemma bsm_bsm' o (n1 n2 : Nu o) : bsm n1 n2 <-> bsm' n1 n2.
  Proof.
  Admitted.

  Axiom bsm'_eq : forall o (n1 n2 : Nu o), bsm' n1 n2 -> n1 = n2.

  Lemma bsm_eq : forall o (n1 n2 : Nu o), bsm n1 n2 <-> n1 = n2.
  Proof.
    intros; split; intro.
    - apply bsm'_eq, bsm_bsm', H0.
    - subst. apply bsm_bsm', eq_bsm'.
  Qed.

End INDUCTIVE.