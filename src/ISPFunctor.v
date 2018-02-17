Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf IFunctor hott.


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

  Global Program Instance Functor_Container
    : Functor Container :=
    Build_Functor _
                  (fun X Y f fx => (sigTimply _ (fun s (fn : forall i : C, P s i -> X i)
                                                     i p => f i (fn i p)) fx))
                  (fun X fx i x => exists p, projT2 fx i p = x)
                  container_rel
                  (fun X fx => existT _ _ (fun i p => existI _ (ex_intro _ p eq_refl))).

  Goal True. constructor. Qed.
  
  Lemma REL_EQ_EQ_C X (fx fy : Container X) :
    fx = fy <-> rel (fun _ => eq) fx fy.
  Proof.
    split; intros.
    - subst. destruct fy. constructor.
      intros. reflexivity.
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

  Lemma REL_MONOTONE_C X Y (R R' : forall (i: C), X i -> Y i -> Prop)
        (MON : forall i x y, R i x y -> R' i x y) fx fy :
    container_rel R fx fy -> container_rel R' fx fy.
  Proof.
    intro. destruct H. constructor.
    intros. apply MON, H.
  Qed.

  Lemma MAP_COMPOSE_C (X Y Z: iType C) (f: forall i, X i -> Y i)
        (g: forall i, Y i -> Z i) (fx : Container X) :
    map g (map f fx) = map (fun i x => g i (f i x)) fx.
  Proof.
    reflexivity.
  Qed.

  Lemma MAP_ID_C (X : iType C) (fx : Container X) :
    (map (fun _ x => x) fx) = fx.
  Proof.
    rewrite sigT_eta. reflexivity.
  Qed.

  Lemma MEM_MAP_C (X Y : iType C) (f: forall i, X i -> Y i) (fx : Container X)
        i (x : X i) :
    mem fx x -> mem (map f fx) (f _ x).
  Proof.
    intro. destruct H. simpl.
    exists x0. rewrite H. reflexivity.
  Qed.

  Lemma MAP_REL_C X1 Y1 X2 Y2 (f: forall i, X1 i -> X2 i) (g: forall i, Y1 i -> Y2 i)
        (R : forall i, X2 i -> Y2 i -> Prop) (fx : Container X1) (fy : Container Y1) 
    : rel (fun i (x : X1 i) (y : Y1 i) => R i (f i x) (g i y)) fx fy <->
      rel R (map f fx) (map g fy).
  Proof.
    split; intro.
    - destruct H. simpl. unfold sigTimply. simpl.
      constructor. apply H.
    - apply CONTAINER_REL2 in H. destruct H. simpl in *.
      apply CONTAINER_REL2. exists x.
      intros. specialize (H i p).
      rewrite eq_rect_fun in H.
      rewrite eq_rect_fun2 in H.
      rewrite eq_rect_const in H.
      rewrite eq_rect_fun.
      rewrite eq_rect_fun2.
      rewrite eq_rect_const. apply H.
  Qed.

  Lemma REL_EQ_C X Y (R R' : forall (i: C), X i -> Y i -> Prop)
        (EQ : forall i x y, R i x y <-> R' i x y)
        (fx : Container X) (fy : Container Y) :
    rel R fx fy <-> rel R' fx fy.
  Proof.
    split; apply REL_MONOTONE_C; apply EQ.
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
        TAG X (fx: F X) : map (@projI1 _ _ _) (tag _ fx) = fx;
       }.

End ISPFUNCTOR.

Section SPFUNCTOR_FACTS.

  Variable C : Type.
  Variable (F : iType C -> Type).
  Context `{SPFunctor _ F}.

  Lemma MAP_COMPOSE (X Y Z: iType C) (f: forall i, X i -> Y i)
        (g: forall i, Y i -> Z i) (fx : F X) :
    map g (map f fx) = map (fun i x => g i (f i x)) fx.
  Proof.
    apply (INJECTIVE (H1 := ISO)). repeat rewrite MAP_COMMUTE.
    apply MAP_COMPOSE_C.
  Qed.

  Lemma MAP_ID (X : iType C) (fx : F X) :
    (map (fun _ x => x) fx) = fx.
  Proof.
    apply (INJECTIVE (H1 := ISO)). repeat rewrite MAP_COMMUTE.
    apply MAP_ID_C.
  Qed.

  Lemma MEM_MAP (X Y : iType C) (f: forall i, X i -> Y i) (fx : F X) i (x : X i) :
    mem fx x -> mem (map f fx) (f _ x).
  Proof.
    intro. apply MEM_COMMUTE. rewrite MAP_COMMUTE.
    apply MEM_MAP_C. apply MEM_COMMUTE. apply H0.
  Qed.

  Lemma REL_EQ_EQ X (fx fy : F X) :
    fx = fy <-> rel (fun _ => eq) fx fy.
  Proof.
    split; intro.
    - apply REL_COMMUTE. apply REL_EQ_EQ_C.
      subst. reflexivity.
    - apply (INJECTIVE (H1 := ISO)). apply REL_EQ_EQ_C.
      apply REL_COMMUTE. apply H0.
  Qed.

  Lemma REL_MONOTONE X Y (R R' : forall (i: C), X i -> Y i -> Prop)
        (MON : forall i x y, R i x y -> R' i x y) (fx : F X) (fy : F Y) :
    rel R fx fy -> rel R' fx fy.
  Proof.
    intro. apply REL_COMMUTE. apply REL_COMMUTE in H0.
    apply (REL_MONOTONE_C _ MON H0).
  Qed.

  Lemma MAP_REL X1 Y1 X2 Y2 (f : forall i, X1 i -> X2 i) (g : forall i, Y1 i -> Y2 i)
        (R : forall (i : C), X2 i -> Y2 i -> Prop) (fx : F X1) (fy : F Y1) :
    rel (fun i (x : X1 i) (y : Y1 i) => R i (f i x) (g i y)) fx fy <->
    rel R (map f fx) (map g fy).
  Proof.
    split; intro; apply REL_COMMUTE; apply REL_COMMUTE in H0.
    - repeat rewrite MAP_COMMUTE.
      apply MAP_REL_C in H0. apply H0.
    - repeat rewrite MAP_COMMUTE in H0.
      apply MAP_REL_C. apply H0.
  Qed.

  Lemma REL_EQ X Y (R R' : forall (i: C), X i -> Y i -> Prop)
        (EQ : forall i x y, R i x y <-> R' i x y) (fx : F X) (fy : F Y) :
    rel R fx fy <-> rel R' fx fy.
  Proof.
    split; apply REL_MONOTONE; apply EQ.
  Qed.

End SPFUNCTOR_FACTS.