Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf IFunctor JMeq.

(*
Goal True. auto. Qed.

Lemma JMeq_eq_eq1 X Y (x : X) (y : Y) : x ~= y -> X = Y.
Proof.
  intros.
  inversion H. reflexivity.
Defined.

Lemma JMeq_eq_eq2 X Y (x : X) (y : Y) (JEQ : x ~= y) :
  (eq_rect _ _ x _ (JMeq_eq_eq1 JEQ)) = y.
Proof.
  inversion JEQ. subst. destruct JEQ.
  compute. reflexivity.
Defined.

Definition JMeq_rect_T X (P : X -> Type) (Q : forall x, P x -> Type) :
  forall (x y : X) (p : P x) (q : P y), p ~= q -> Q x p -> Q y q.
  intros.
  inversion H.
  set (JMeq_eq_eq2 H). 
  rewrite <- e.
  clear e H1 H2 H3.
  


compute in *.
  destruct (JMeq_eq_eq1 H).


  fun x y p q e s =>
    match e as e' return (Q _ b) with
    | JMeq_refl => s end. 

eq_rect

Proof.
  intros. inversion H.
  eq_dep_JMeq
  eq_rect

 fix 2.
  

  fun x y p q e =>
    match e with
    | JMeq_refl p => Q _ p 


Proof.
  intros. 
*)

Section CONTAINER.

  Variable C S : Type.
  Variable P : S -> C -> Type.
  
  Definition Container (X : iType C) : Type
    := sigT (fun (s : S) => forall (i : C), P s i -> X i).

  Definition container_map X Y
             (f: forall (i: C), X i -> Y i) (fx : Container X) : Container Y :=
    existT (fun s : S => forall i : C, P s i -> Y i) (projT1 fx)
           (fun (i : C) (p : P (projT1 fx) i) => f i (projT2 fx i p)).

  Inductive container_mem  X :
    Container X -> forall (i : C), X i -> Prop :=
  | Container_mem s i p (f : forall i, P s i -> X i)
    : container_mem (existT _ s f) _  (f i p)
  .

  Inductive container_rel X Y
            (R: forall i, X i -> Y i -> Prop) : Container X -> Container Y -> Prop :=
  | Container_rel s (f1 : forall i, P s i -> X i) (f2 : forall i, P s i -> Y i) :
      (forall i p, R i (f1 i p) (f2 i p)) ->
      container_rel R (existT _ s f1) (existT _ s f2)
  .

  Definition container_tag X (fx: Container X)
    : Container (sigI (container_mem fx)) :=
    match fx with
    | existT _ s f =>
      existT _ s (fun (i : C) (p : P s i) =>
                    existI (f i p : X i) (Container_mem X p f))
    end.

  Global Program Instance Functor_Container
    : Functor Container := Build_Functor _
                                             container_map
                                             container_mem
                                             container_rel
                                             container_tag
                                             _.
  Next Obligation.
    destruct fx. reflexivity.
  Qed.

  Lemma CONTAINER_EQ X (fx fy : Container X) :
    fx = fy <-> container_rel (fun _ => eq) fx fy.
  Proof.
    split; intros.
    - subst. destruct fy.
      eapply Container_rel. auto.
    - destruct H. f_equal.
      extensionality i. extensionality p.
      apply H.
  Qed.


  Arguments existT {A} {P} x p.

  Lemma CONTAINER_MEM X i (x : X i) s f:
     (container_mem (existT s f) _ x) <-> (exists p, f i p = x).
  Proof.
    split; intro.
    - inversion H.
      exists p. reflexivity.
    - destruct H as [p H].
      rewrite <- H. apply Container_mem.
  Qed.

  Lemma CONTAINER_REL X Y (R: forall i, X i -> Y i -> Prop) x y :
    container_rel R x y <->
    exists s f1 f2, (existT s f1 = x) /\ (existT s f2 = y) /\
                    (forall i p, R i (f1 i p) (f2 i p)).
  Proof.
    split.
    - intro. destruct H.
      exists s. exists f1. exists f2. auto.
    - intro. destruct H. destruct H. destruct H. destruct H. destruct H0.
      subst. apply Container_rel. apply H1.
  Qed.    

  Lemma CONTAINER_REL2 X Y (R: forall i, X i -> Y i -> Prop) s1 s2
    (f1 : forall i, P s1 i -> X i) (f2 : forall i, P s2 i -> Y i) :
    container_rel R (@existT _ _ s1 f1) (@existT _ _ s2 f2) <->
    exists (e : s2 = s1), forall (i : C) (p : P s1 i),
        R i (f1 i p) ((eq_rect s2 (fun s => forall i, P s i -> Y i) f2 s1 e) i p).
  Proof.
    split; intros.
    - apply CONTAINER_REL in H.
      destruct H. destruct H. destruct H.
      destruct H. destruct H0.
      inversion H. inversion H0. clear H4 H6.
      subst.
      exists (eq_refl _).
      intros. simpl.
      apply H1.
    - destruct H. subst. apply Container_rel.
      simpl in H. apply H.
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

  Goal True. apply I. Qed.

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
    rewrite MAP_COMMUTE. destruct (NT X fx). simpl in *.
    apply CONTAINER_MEM in H0. destruct H0.
    apply CONTAINER_MEM. exists x2. subst. reflexivity.
  Qed.

  Lemma REL_EQ_EQ X (fx fy : F X) :
    fx = fy <-> rel (fun _ => eq) fx fy.
  Proof.
    rewrite REL_COMMUTE. simpl. rewrite <- CONTAINER_EQ.
    split; intros.
    - subst. reflexivity.
    - apply INJECTIVE, H0.
  Qed.

End SPFUNCTOR_FACTS.