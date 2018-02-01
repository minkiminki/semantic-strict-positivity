Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf IFunctor.


Section CONTAINER.

  Variable C S : Type.
  Variable P : S -> C -> Type.
  
  Definition Container (X : iType C) : Type
    := sigT (fun (s : S) => forall (i : C), P s i -> X i).

  Inductive container_rel X Y
            (R: forall i, X i -> Y i -> Prop) : Container X -> Container Y -> Prop :=
  | Container_rel s (f1 : forall i, P s i -> X i) (f2 : forall i, P s i -> Y i) :
      (forall i p, R i (f1 i p) (f2 i p)) ->
      container_rel R (existT _ s f1) (existT _ s f2)
  .

  Goal True. apply I. Qed.

  Global Program Instance Functor_Container
    : Functor Container :=
    Build_Functor _
                  (fun X Y f fx => (sigTimply _ (fun s (fn : forall i : C, P s i -> X i)
                                                     i p => f i (fn i p)) fx))
                  (fun X fx i x => exists p, projT2 fx i p = x)
                  container_rel
                  (fun X fx => existT _ _ (fun i p => existI _ (ex_intro _ p eq_refl)))
                  _.
  Next Obligation.
    destruct fx. reflexivity.
  Qed.

  Lemma CONTAINER_EQ X (fx fy : Container X) :
    fx = fy <-> container_rel (fun _ => eq) fx fy.
  Proof.
    split; intros.
    - subst. destruct fy.
      eapply Container_rel. reflexivity.
    - destruct H. f_equal.
      extensionality i. extensionality p.
      apply H.
  Qed.


  Arguments existT {A} {P} x p.

  Lemma CONTAINER_REL X Y (R: forall i, X i -> Y i -> Prop) x y :
    container_rel R x y <->
    exists s f1 f2, (existT s f1 = x) /\ (existT s f2 = y) /\
                    (forall i p, R i (f1 i p) (f2 i p)).
  Proof.
    split.
    - intro. destruct H.
      exists s. exists f1. exists f2. auto.
    - intro. destruct H as [s [f1 [f2 [EQ1 [EQ2 H]]]]].
      subst. apply Container_rel. apply H.
  Qed.    

  Lemma CONTAINER_REL2 X Y (R: forall i, X i -> Y i -> Prop) c1 c2 :
    container_rel R c1 c2 <->
    exists (e : projT1 c2 = projT1 c1), forall (i : C) (p : P (projT1 c1) i),
        R i ((projT2 c1) i p) ((eq_rect (projT1 c2) (fun s => forall i, P s i -> Y i) (projT2 c2) (projT1 c1) e) i p).
  Proof.
    split; intros.
    - apply CONTAINER_REL in H.
      destruct H as [s [f1 [f2 [EQ1 [EQ2 H]]]]].
      destruct EQ1, EQ2. simpl.
      exists (eq_refl _). apply H.
    - destruct H. destruct c1, c2. simpl in *. subst. apply Container_rel.
      apply H.
  Qed.

  Lemma CONTAINER_REL_MONOTONE X Y (R R' : forall (i: C), X i -> Y i -> Prop)
        (MON : forall i x y, R i x y -> R' i x y) fx fy :
    container_rel R fx fy -> container_rel R' fx fy.
  Proof.
    intro. destruct H. constructor.
    intros. apply MON, H.
  Qed.

End CONTAINER.


Section ISPFUNCTOR.

  Arguments NatIso {C} F G {H H0}.

  Class SPFunctor C (F : (C -> Type) -> Type)
    := {
        Fn :> Functor F;
        S : Type;
        P : S -> C -> Type;
        ISO :> @NatIso _ F (Container P) _ _;
       }.

End ISPFUNCTOR.

Section SPFUNCTOR_FACTS.

  Variable C : Type.
  Variable (F : iType C -> Type).
  Context `{SPFunctor _ F}.

  Lemma INJECTIVE (X : iType C) (fx fy : F X) (EQ : NT _ fx = NT _ fy) :
    fx = fy.
  Proof.
    apply f_equal with (f := NTinv _) in EQ.
    repeat rewrite BIJECTION1 in EQ.
    apply EQ.
  Qed.

  Lemma MAP_COMPOSE (X Y Z: iType C) (f: forall i, X i -> Y i)
        (g: forall i, Y i -> Z i) (fx : F X) :
    map g (map f fx) = map (fun i x => g i (f i x)) fx.
  Proof.
    apply INJECTIVE. repeat rewrite MAP_COMMUTE.
    destruct (NT X fx). reflexivity.
  Qed.

  Lemma MAP_ID (X : iType C) (fx : F X) :
    (map (fun _ x => x) fx) = fx.
  Proof.
    apply INJECTIVE. repeat rewrite MAP_COMMUTE.
    destruct (NT X fx). reflexivity.
  Qed.

  Lemma MEM_MAP (X Y : iType C) (f: forall i, X i -> Y i) (fx : F X) i (x : X i) :
    mem fx x -> mem (map f fx) (f _ x).
  Proof.        
    intros. apply MEM_COMMUTE. apply MEM_COMMUTE in H0.
    rewrite MAP_COMMUTE. destruct H0 as [p EQ].
    exists p. rewrite <- EQ. reflexivity. 
  Qed.

  Lemma REL_EQ_EQ X (fx fy : F X) :
    fx = fy <-> rel (fun _ => eq) fx fy.
  Proof.
    rewrite REL_COMMUTE. simpl. rewrite <- CONTAINER_EQ.
    split; intros.
    - subst. reflexivity.
    - apply INJECTIVE, H0.
  Qed.

  Lemma REL_MONOTONE X Y (R R' : forall (i: C), X i -> Y i -> Prop)
        (MON : forall i x y, R i x y -> R' i x y) (fx : F X) (fy : F Y) :
    rel R fx fy -> rel R' fx fy.
  Proof.
    intro. apply REL_COMMUTE. apply REL_COMMUTE in H0.
    apply (CONTAINER_REL_MONOTONE _ MON H0).
  Qed.

End SPFUNCTOR_FACTS.