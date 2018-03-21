Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf Functor hott pullback_sfunctor.

Section CONTAINER.

  Variable S : Type.
  Variable P : S -> Type.
  
  Definition Container (X : Type) : Type
    := sigT (fun (s : S) => P s -> X).

  Inductive container_rel X Y
            (R: X -> Y -> Prop) : Container X -> Container Y -> Prop :=
  | Container_rel s (f1 : P s -> X) (f2 : P s -> Y) :
      (forall p, R (f1 p) (f2 p)) -> container_rel R (existT _ s f1) (existT _ s f2)
  .

  Global Program Instance Functor_Container
    : SFunctor Container :=
    Build_SFunctor (Build_Functor _
      (fun X Y f fx =>
                          (sigTimply _ (fun s (fn : P s -> X)
                                            p => f (fn p)) fx)))
      (fun X fx x => exists p, projT2 fx p = x)
      container_rel
      (fun X fx => existT _ (projT1 fx) (fun p => exist _ (projT2 fx p) (ex_intro _ p eq_refl))).

  Lemma CONTAINER_REL X Y (R: X -> Y -> Prop) x y :
    container_rel R x y <->
    exists s f1 f2, (forall p, R (f1 p) (f2 p)) /\
               (existT _ s f1 = x) /\ (existT _ s f2 = y).
  Proof.
    split.
    - intro. destruct H.
      exists s. exists f1. exists f2. auto.
    - intro. destruct H as [s [f1 [f2 [H [EQ1 EQ2 ]]]]].
      subst. apply Container_rel. apply H.
  Qed.    

  Lemma CONTAINER_REL2 X Y (R: X -> Y -> Prop) c1 c2 :
    container_rel R c1 c2 <->
    exists (e : projT1 c2 = projT1 c1), forall (p : P (projT1 c1)),
        R ((projT2 c1) p) ((eq_rect (projT1 c2) (fun s => P s -> Y) (projT2 c2) (projT1 c1) e) p).
  Proof.
    split; intros.
    - apply CONTAINER_REL in H.
      destruct H as [s [f1 [f2 [H [EQ1 EQ2 ]]]]].
      destruct EQ1, EQ2. simpl.
      exists (eq_refl _). apply H.
    - destruct H. destruct c1, c2. simpl in *. subst. apply Container_rel.
      apply H.
  Qed.

  Definition pullback_C A (X : A -> Type) C (fx : forall a, Container (X a)) (fc : Container C)
             (f : forall a, X a -> C) (EQ : forall a, fc = map (f a) (fx a)) :
    Container (sig (fun (x : forall a, X a) => forall a1 a2, f a1 (x a1) = f a2 (x a2))).
  Proof.
    exists (projT1 fc). intro p.
    exists (fun a => projT2 (fx a) (eq_rect _ P p _ (f_equal (projT1 (P := fun s => P s -> C)) (EQ a)))).
    intros a1 a2.
    apply eq_trans with (y := projT2 fc p); simpl.
    - remember (EQ a1). clear EQ Heqe. subst. reflexivity.
    - remember (EQ a2). clear EQ Heqe. subst. reflexivity.
  Defined.

  Lemma FUN_UNIQUE_C A (a0 : A) (X : A -> Type) (fp1 fp2 : Container  (forall a, X a))
        (EQ : forall a, map (fun f => f a) fp1 = map (fun f => f a) fp2) :
    fp1 = fp2.
  Proof.
  (* it needs axiom k *)
  (*
    destruct fp1 as [s1 f1]. destruct fp2 as [s2 f2].
    apply sig_eq. simpl.
    unfold sigTimply in EQ. simpl in EQ. 
    
    set (f_equal (@projT1 _ _) (EQ a0)). simpl in e.

    exists e. simpl. *)
  Admitted.

  Global Program Instance PBFunctor_Container : PB_SFunctor Container :=
    Build_PB_SFunctor _ _ _ pullback_C _ FUN_UNIQUE_C _ _ _.
  Next Obligation.
    destruct fx. reflexivity.
  Defined.
  Next Obligation.
    unfold pullback_C, sigTimply in *. simpl in *.
    remember (EQ a). subst. simpl. symmetry. apply sigT_eta. 
  Qed.
  Next Obligation.
    destruct fx. reflexivity.
  Qed.
  Next Obligation.
    split.
    - intros H x MEM. destruct H as [[s f] EQ]. destruct EQ.
      destruct MEM as [p []].
      apply (proj2_sig (f p)).
    - intro H.
      exists (map (fun x : sig (mem fx) =>
           exist Pr (proj1_sig x)
             (H (proj1_sig  x)
                (@proj2_sig X (@mem Container Functor_Container X fx) x))) (tag _ fx)).
      destruct fx. reflexivity.
  Qed.
  Next Obligation.
    split; intro.
    - destruct H as [fr [[] []]].
      constructor. intro p. apply (proj2_sig (projT2 fr p)).
    - destruct H. unfold allR. unfold Container.
      exists (existT (fun s0 => P s0 -> {xy | R (fst xy) (snd xy)}) s (fun p => exist _ (f1 p, f2 p) (H p))).
      split; reflexivity.
  Qed.

  Definition MAP_COMPOSE_ASSOC_C (X Y Z W: Type) (f: X -> Y)
             (g: Y -> Z) (h: Z -> W) (fx : Container X) :
    eq_trans (f_equal (map h) (MAP_COMPOSE f g fx))
             (eq_sym (MAP_COMPOSE (fun (x : X) => g (f x)) h fx))
    = 
    eq_trans (MAP_COMPOSE g h (map f fx))
             (MAP_COMPOSE f (fun (y : Y) => h (g y)) fx).
  Proof.
    reflexivity.
  Qed.

  Definition MAP_ID_UNIT1_C (X Y : Type) (f: X -> Y)
             (fx : Container X) :
    MAP_COMPOSE id f fx
    =
    f_equal (map f) (MAP_ID _ fx).
  Proof.
    destruct fx. reflexivity.
  Qed.

  Definition MAP_ID_UNIT2_C (X Y : Type) (f: X -> Y)
             (fx : Container X) :
    MAP_COMPOSE f id fx
    =
    MAP_ID _ (map f fx).
  Proof.
    destruct fx. reflexivity.
  Qed.

End CONTAINER.

Arguments NatIso F G {H H0}.

Class SPFunctor (F : Type -> Type)
  := {
      Fn :> SFunctor F;
      shape : Type;
      degree : shape -> Type;
      ISO :> @NatIso F (Container degree) _ _;
      TAG X (fx: F X) : map (@proj1_sig _ _) (tag _ fx) = fx;
    }.

Section SPFUNCTOR_FACTS.

  Variable (F : Type -> Type).
  Context `{SPF : SPFunctor F}.

  Definition pullback_F A (X : A -> Type) C (fx : forall a, F (X a)) (fc : F C)
             (f : forall a, X a -> C) (EQ : forall a, fc = map (f a) (fx a)) :
    F (sig (fun (x : forall a, X a) => forall a1 a2, f a1 (x a1) = f a2 (x a2))) :=
    NTinv _ (pullback_C X (fun a => NT _ (fx a)) f
                        (fun a => eq_trans (f_equal (NT C) (EQ a)) (MAP_COMMUTE (f a) (fx a)))).

  Global Program Instance PBFunctor_SPFunctor : PB_SFunctor F :=
    Build_PB_SFunctor _ _ _ pullback_F _ _ _ _ _.
  Next Obligation.
    apply eq_trans with (NTinv _ (NT _ (map g (map f fx)))).
    symmetry. apply BIJECTION1.
    apply eq_trans with (NTinv _ (NT _ (map (fun x => g (f x)) fx))).
    apply (f_equal (NTinv _)).
    apply eq_trans with (map g (NT _ (map f fx))).
    apply MAP_COMMUTE.
    apply eq_trans with (map g (map f (NT _ fx))).
    apply (f_equal (map g)).
    apply MAP_COMMUTE.
    apply eq_trans with (map (fun x : X => g (f x)) (NT _ fx)).
    apply MAP_COMPOSE.
    symmetry. apply MAP_COMMUTE.
    apply BIJECTION1.
  Defined.
  Next Obligation.    
    apply eq_trans with (NTinv _ (NT _ (map id fx))).
    symmetry. apply BIJECTION1.
    apply eq_trans with (NTinv _ (NT _ fx)).
    apply (f_equal (NTinv _)).
    apply eq_trans with (map id (NT _ fx)).
    apply MAP_COMMUTE.
    apply (MAP_ID (PB_SFunctor:=PBFunctor_Container _)).
    apply BIJECTION1.
  Defined.
  Next Obligation.
    unfold pullback_F. rewrite <- MAP_COMMUTE_R. apply eq_trans with (NTinv _ (NT _ (fx a))).
    apply (f_equal (NTinv _)).
    set (PULLBACK X (fun a0 : A => NT (X a0) (fx a0)) f
                  (fun a0 : A => eq_trans (f_equal (NT C) (EQ a0)) (MAP_COMMUTE (f a0) (fx a0))) a). apply e.
    apply BIJECTION1.
  Qed.
  Next Obligation.
    apply eq_trans with (NTinv _ (NT _ fp1)). symmetry. apply BIJECTION1.
    apply eq_trans with (NTinv _ (NT _ fp2)). apply (f_equal (NTinv _)).
    apply (FUN_UNIQUE a0).
    intro a.
    apply eq_trans with (NT _ (map (fun f : forall x : A, X x => f a) fp1)).
    symmetry. apply MAP_COMMUTE.
    apply eq_trans with (NT _ (map (fun f : forall x : A, X x => f a) fp2)).
    apply (f_equal (NT _)). apply EQ.
    apply MAP_COMMUTE.
    apply BIJECTION1.
  Qed.
  Next Obligation.
    apply TAG.
  Qed.
  Next Obligation.
    split; intro.
    - intros x MEM. apply MEM_COMMUTE in MEM.
      apply (proj1 (ALLP_EQ Pr (NT _ fx))); [| apply MEM].
      destruct H as [fp EQ]. exists (NT _ fp).
      apply eq_trans with (NT _ (map (@proj1_sig _ _) fp)).
      + symmetry. apply MAP_COMMUTE.
      + apply (f_equal (NT _) EQ).
    - destruct (proj2 (ALLP_EQ Pr (NT _ fx))
                      (fun x MEM => H x (proj2 (MEM_COMMUTE fx x) MEM))) as [fp EQ].
      exists (NTinv _ fp).
      rewrite <- MAP_COMMUTE_R. apply eq_trans with (NTinv X (NT X fx)).
      apply (f_equal (NTinv _) EQ). apply BIJECTION1.
  Qed.
  Next Obligation.
    split; intro.
    - apply REL_COMMUTE. apply ALLR_EQ.
      destruct H as [fr [[] []]].
      exists (NT _ fr). split; symmetry; apply MAP_COMMUTE.
    - apply REL_COMMUTE in H. apply ALLR_EQ in H.
      destruct H as [fr [EQ1 EQ2]].
      exists (NTinv _ fr). split.
      + rewrite <- MAP_COMMUTE_R.
        apply (eq_trans (f_equal (NTinv _) EQ1)). apply BIJECTION1.
      + rewrite <- MAP_COMMUTE_R.
        apply (eq_trans (f_equal (NTinv _) EQ2)). apply BIJECTION1.
  Qed.

End SPFUNCTOR_FACTS.
