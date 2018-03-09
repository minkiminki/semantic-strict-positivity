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
    : SFunctor Container :=
    Build_SFunctor (Build_Functor _
      (fun X Y f fx =>
                          (sigTimply _ (fun s (fn : forall i : C, P s i -> X i)
                                            i p => f i (fn i p)) fx)))
      (fun X fx i x => exists p, projT2 fx i p = x)
      container_rel
      (fun X fx => existT _ _ (fun i p => existI _ (ex_intro _ p eq_refl))).
  
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
    exists s f1 f2, (forall i p, R i (f1 i p) (f2 i p)) /\
                    (existT s f1 = x) /\ (existT s f2 = y).
  Proof.
    split.
    - intro. destruct H.
      exists s. exists f1. exists f2. auto.
    - intro. destruct H as [s [f1 [f2 [H [EQ1 EQ2 ]]]]].
      subst. apply Container_rel. apply H.
  Qed.    

  Lemma CONTAINER_REL2 X Y (R: forall i, X i -> Y i -> Prop) c1 c2 :
    container_rel R c1 c2 <->
    exists (e : projT1 c2 = projT1 c1), forall (i : C) (p : P (projT1 c1) i),
        R i ((projT2 c1) i p) ((eq_rect (projT1 c2) (fun s => forall i, P s i -> Y i) (projT2 c2) (projT1 c1) e) i p).
  Proof.
    split; intros.
    - apply CONTAINER_REL in H.
      destruct H as [s [f1 [f2 [H [EQ1 EQ2 ]]]]].
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
  Defined.

  Lemma MAP_ID_C (X : iType C) (fx : Container X) :
    (map (fun _ x => x) fx) = fx.
  Proof.
    destruct fx. reflexivity.
  Defined.

  Lemma MEM_MAP_C (X Y : iType C) (f: forall i, X i -> Y i) (fx : Container X)
        i (x : X i) :
    mem fx x -> mem (map f fx) (f _ x).
  Proof.
    intro. destruct H. simpl.
    exists x0. rewrite H. reflexivity.
  Qed.

  Lemma MEM_MAP_INJECTIVE_C (X Y : iType C) (f: forall i, X i -> Y i)
        (INJ : forall i (x1 x2 : X i), f i x1 = f i x2 -> x1 = x2)
        (fx : Container X) i (x : X i) :
    mem (map f fx) (f _ x) -> mem fx x.
  Proof.
    intro. destruct H. exists x0. 
    apply INJ. apply H.
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

  Lemma MAP_POINTWISE_C X Y (f1 f2 : forall i, X i -> Y i) (fx : Container X)
        (PW : forall i (x : X i), mem fx x -> f1 i x = f2 i x)
    : map f1 fx = map f2 fx.
  Proof.
    simpl. unfold sigTimply. f_equal.
    extensionality i. extensionality p.
    apply PW. exists p. reflexivity.
  Qed.

  Lemma MAP_INJECTIVE_C X Y (f : forall i, X i -> Y i)
        (INJ : forall i (x1 x2 : X i), f i x1 = f i x2 -> x1 = x2) :
    forall fx1 fx2, map f fx1 = map f fx2 -> fx1 = fx2.
  Proof.
    intros. simpl in *. unfold sigTimply in *.
    apply EqdepFacts.eq_sigT_sig_eq in H. destruct H.
    rewrite (sigT_eta fx1). rewrite (sigT_eta fx2).
    apply EqdepFacts.eq_sigT_sig_eq. exists x.
    extensionality i. extensionality p. 
    apply equal_f_dep with (x0 := i) in e.
    apply equal_f_dep with (x0 := p) in e. 
    rewrite eq_rect_fun in e. rewrite eq_rect_fun2 in e. rewrite eq_rect_const in e. 
    apply INJ in e.
    rewrite eq_rect_fun. rewrite eq_rect_fun2. rewrite eq_rect_const.
    apply e.
  Qed.

  Lemma TAG_C X (fx: Container X) : map (@projI1 _ _ _) (tag _ fx) = fx.
  Proof.
    destruct fx; reflexivity.
  Qed.

  Lemma ALLP_EQ_C X (Pr : forall i, X i -> Prop) :
    forall (fx: Container X),
      allP _ Pr fx <-> (forall i x, mem fx x -> Pr i x).
  Proof.
    intro; split.
    - intros H i x MEM. destruct H as [[s f] EQ].
      rewrite <- EQ in MEM. destruct MEM as [p e]. 
      rewrite <- e. apply (projI2 (f i p)).
    - intro H.
      exists (map (fun i x => existI (projI1 x) (H _ _ (projI2 x))) (tag _ fx)).
      rewrite MAP_COMPOSE_C. unfold projI1 at 1. apply TAG_C.
  Qed.

  Lemma ALLR_EQ_C X Y (R : forall i, X i -> Y i -> Prop) :
    forall (fx : Container X) (fy : Container Y),
      allR _ _ R fx fy <-> rel R fx fy.
  Proof.
    intros. split.
    - intro H. destruct H as [fr [EQ1 EQ2]].
      rewrite <- EQ1. rewrite <- EQ2. destruct fr. constructor.
      intros. apply (proj2I3 (s i p)).
    - intro H. destruct H.
      exists (existT (P:=fun s => forall i : C, P s i -> sig2I X Y R i) s
                     (fun i p => exist2I _ _ _ _ (f1 i p) (f2 i p) (H i p))).
      split; reflexivity.
  Qed.  

  Lemma MEM_EQ_C X (fx : Container X) i (x : X i) :
    mem fx x <-> (forall Pr, allP _ Pr fx -> Pr i x).
  Proof.
    split.
    - intros MEM Pr H. apply (ALLP_EQ_C _ fx).
      + apply H.
      + apply MEM.
    - intro H. apply (H (@mem _ _ _ _ fx)).
      apply ALLP_EQ_C. apply (fun _ _ => id).
  Qed.

  Lemma MAP_MEM_INJECTIVE_C X Y (f : forall i, X i -> Y i) (fx : Container X)
        (INJ : forall i (x : X i), mem fx x -> forall x', f i x = f i x' -> x = x')
    : forall fx', map f fx = map f fx' -> fx = fx'.
  Proof.
    intros. simpl in *. unfold sigTimply in *.
    apply EqdepFacts.eq_sigT_sig_eq in H. destruct H.
    rewrite (sigT_eta fx). rewrite (sigT_eta fx').
    apply EqdepFacts.eq_sigT_sig_eq. exists x.
    extensionality i. extensionality p. 
    apply equal_f_dep with (x0 := i) in e.
    apply equal_f_dep with (x0 := p) in e. 
    rewrite eq_rect_fun in e. rewrite eq_rect_fun2 in e. rewrite eq_rect_const in e. 
    apply INJ in e; eauto.
    rewrite eq_rect_fun. rewrite eq_rect_fun2. rewrite eq_rect_const.
    apply e.
  Qed.

  Definition MAP_COMPOSE_ASSOC_C (X Y Z W: iType C) (f: forall i, X i -> Y i)
             (g: forall i, Y i -> Z i) (h: forall i, Z i -> W i) (fx : Container X) :
    eq_trans (f_equal (map h) (MAP_COMPOSE_C Y Z f g fx))
             (eq_sym (MAP_COMPOSE_C Z W (fun (i : C) (x : X i) => g i (f i x)) h fx))
    = 
    eq_trans (MAP_COMPOSE_C Z W g h (map f fx))
             (MAP_COMPOSE_C Y W f (fun (i : C) (x : Y i) => h i (g i x)) fx).
  Proof.
    reflexivity.
  Qed.

  Definition MAP_ID_UNIT1_C (X Y : iType C) (f: forall i, X i -> Y i)
             (fx : Container X) :
    MAP_COMPOSE_C X Y (fun (i : C) (x : X i) => x) f fx
    =
    f_equal (map f) (MAP_ID_C fx).
  Proof.
    destruct fx. reflexivity.
  Qed.

  Definition MAP_ID_UNIT2_C (X Y : iType C) (f: forall i, X i -> Y i)
             (fx : Container X) :
    MAP_COMPOSE_C Y Y f (fun (i : C) (y : Y i) => y) fx
    =
    MAP_ID_C (map f fx).
  Proof.
    destruct fx. reflexivity.
  Qed.

End CONTAINER.

Section ISPFUNCTOR.

  Arguments NatIso {C} F G {H H0}.

  Class SPFunctor C (F : (C -> Type) -> Type)
    := {
        Fn :> SFunctor F;
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

  Lemma MEM_MAP_INJECTIVE (X Y : iType C) (f: forall i, X i -> Y i)
        (INJ : forall i (x1 x2 : X i), f i x1 = f i x2 -> x1 = x2)
        (fx : F X) i (x : X i) :
    mem (map f fx) (f _ x) -> mem fx x.
  Proof.
    intro MEM. apply MEM_COMMUTE. 
    apply (MEM_MAP_INJECTIVE_C INJ). 
    rewrite <- MAP_COMMUTE. apply MEM_COMMUTE.
    apply MEM.
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

  Lemma MAP_POINTWISE X Y (f1 f2 : forall i, X i -> Y i) (fx : F X)
        (PW : forall i (x : X i), mem fx x -> f1 i x = f2 i x)
    : map f1 fx = map f2 fx.
  Proof.
    apply (INJECTIVE (H1 := ISO)). repeat rewrite MAP_COMMUTE.
    apply MAP_POINTWISE_C. intros. apply PW.
    apply MEM_COMMUTE. apply H0.
  Qed.

  Lemma MAP_INJECTIVE X Y (f : forall i, X i -> Y i)
        (INJ : forall i (x1 x2 : X i), f i x1 = f i x2 -> x1 = x2) :
    forall (fx1 fx2 : F X), map f fx1 = map f fx2 -> fx1 = fx2.
  Proof.
    intros. apply (INJECTIVE (H1 := ISO)).
    apply (MAP_INJECTIVE_C INJ).
    repeat rewrite <- MAP_COMMUTE. 
    f_equal. apply H0.
  Qed.    

(*
  Lemma ALLP_EQ X (Pr : forall i, X i -> Prop) :
    forall (fx: F X),
      allP _ Pr fx <-> (forall i x, mem fx x -> Pr i x).
  Proof.
    intro; split.
    - intros ALLP i x MEM.
      apply (ALLP_EQ_C Pr (NT _ fx)). 
      + apply ALLP_COMMUTE. apply ALLP.
      + apply MEM_COMMUTE. apply MEM.
    - intro. apply (ALLP_COMMUTE _).
      apply ALLP_EQ_C. intros i x MEM.
      apply H0. apply MEM_COMMUTE. apply MEM.
  Qed.

  Lemma ALLR_EQ X Y (R : forall i, X i -> Y i -> Prop) :
    forall (fx: F X) (fy : F Y),
      allR _ _ R fx fy <-> rel R fx fy.
  Proof.
    intro; split; intro.
    - apply REL_COMMUTE. apply ALLR_EQ_C.
      apply ALLR_COMMUTE. apply H0.
    - apply (ALLR_COMMUTE _). apply ALLR_EQ_C.
      apply REL_COMMUTE. apply H0.
  Qed.

  Lemma MEM_EQ X (fx : F X) i (x : X i) :
    mem fx x <-> (forall Pr, allP _ Pr fx -> Pr i x).
  Proof.
    split.
    - intros MEM Pr ALLP.
      apply (MEM_EQ_C (NT X fx)).
      + apply MEM_COMMUTE. apply MEM.
      + apply ALLP_COMMUTE. apply ALLP.
    - intro.
      apply MEM_COMMUTE. apply MEM_EQ_C.
      intros Pr ALLP. apply H0.
      apply (ALLP_COMMUTE _). apply ALLP.
  Qed.

  Lemma REL_EQ_EQ2 X (fx fy : F X) :
    fx = fy <-> rel (fun _ => eq) fx fy.
  Proof.
    split; intro.
    - apply ALLR_EQ. destruct H0.
      exists (map (fun i x => exist2I _ _ (fun i : C => eq) i x x eq_refl) fx).
      split; rewrite MAP_COMPOSE; apply MAP_ID.
    - apply ALLR_EQ in H0. destruct H0 as [fr [EQ1 EQ2]].
      rewrite <- EQ1. rewrite <- EQ2. f_equal.
      extensionality i. extensionality x. apply (proj2I3 x).
  Qed.
    
  Lemma REL_MONOTONE2 X Y (R R' : forall (i: C), X i -> Y i -> Prop)
        (MON : forall i x y, R i x y -> R' i x y) (fx : F X) (fy : F Y) :
    rel R fx fy -> rel R' fx fy.
  Proof.
    intro REL. apply ALLR_EQ. apply ALLR_EQ in REL.
    destruct REL as [fr [EQ1 EQ2]]. rewrite <- EQ1. rewrite <- EQ2.
    exists (map (fun i r => exist2I _ _ R' i _ _ (MON _ _ _ (proj2I3 r))) fr).
    split; apply MAP_COMPOSE.
  Qed.

  Lemma MAP_POINTWISE2 X Y (f1 f2 : forall i, X i -> Y i) (fx : F X)
        (PW : forall i (x : X i), mem fx x -> f1 i x = f2 i x)
    : map f1 fx = map f2 fx.
  Proof.
    apply ALLP_EQ in PW. destruct PW as [fp EQ].
    rewrite <- EQ. rewrite MAP_COMPOSE. rewrite MAP_COMPOSE. f_equal.
    extensionality i. extensionality p. apply (projI2 p).
  Qed.

  Lemma MAP_MEM_INJECTIVE X Y (f : forall i, X i -> Y i) (fx : F X)
        (INJ : forall i (x : X i), mem fx x -> forall x', f i x = f i x' -> x = x')
    : forall fx', map f fx = map f fx' -> fx = fx'.
  Proof.
    apply ALLP_EQ in INJ. apply (ALLP_COMMUTE _) in INJ.
    intros fx' EQ. apply (INJECTIVE (H1 := ISO)).
    apply (f_equal (NT Y)) in EQ.
    rewrite MAP_COMMUTE in EQ. rewrite MAP_COMMUTE in EQ.
    apply (MAP_MEM_INJECTIVE_C (proj1 (ALLP_EQ_C _ (NT X fx)) INJ) EQ).
  Qed.
*)

(* tag2? pullback? equalizer? *)

(*
  Lemma MEM_MAP1 (X Y : iType C) (f: forall i, X i -> Y i) (fx : F X) i (x : X i) :
    mem fx x -> mem (map f fx) (f _ x).

  Lemma MAP_REL2 X1 Y1 X2 Y2 (f : forall i, X1 i -> X2 i) (g : forall i, Y1 i -> Y2 i)
        (R : forall (i : C), X2 i -> Y2 i -> Prop) (fx : F X1) (fy : F Y1) :
    rel (fun i (x : X1 i) (y : Y1 i) => R i (f i x) (g i y)) fx fy <->
    rel R (map f fx) (map g fy).

  Lemma MAP_INJECTIVE X Y (f : forall i, X i -> Y i)
        (INJ : forall i (x1 x2 : X i), f i x1 = f i x2 -> x1 = x2) :
    forall (fx1 fx2 : F X), map f fx1 = map f fx2 -> fx1 = fx2.
  Proof.
    intros. apply (INJECTIVE (H1 := ISO)).
    apply (MAP_INJECTIVE_C INJ).
    repeat rewrite <- MAP_COMMUTE. 
    f_equal. apply H0.
  Qed.    

  Definition MAP_COMPOSE_ASSOC (X Y Z W: iType C) (f: forall i, X i -> Y i)
             (g: forall i, Y i -> Z i) (h: forall i, Z i -> W i) (fx : F X) :
    eq_trans (f_equal (map h) (MAP_COMPOSE Y Z f g fx))
             (eq_sym (MAP_COMPOSE Z W (fun (i : C) (x : X i) => g i (f i x)) h fx))
    = 
    eq_trans (MAP_COMPOSE Z W g h (map f fx))
             (MAP_COMPOSE Y W f (fun (i : C) (x : Y i) => h i (g i x)) fx).
  Proof.
    reflexivity.
  Qed.

  Definition MAP_ID_UNIT1_C (X Y : iType C) (f: forall i, X i -> Y i)
             (fx : F X) :
    MAP_COMPOSE X Y (fun (i : C) (x : X i) => x) f fx
    =
    f_equal (map f) (MAP_ID fx).
  Proof.
    destruct fx. reflexivity.
  Qed.

  Definition MAP_ID_UNIT2 (X Y : iType C) (f: forall i, X i -> Y i)
             (fx : F X) :
    MAP_COMPOSE Y Y f (fun (i : C) (y : Y i) => y) fx
    =
    MAP_ID (map f fx).
  Proof.
    destruct fx. reflexivity.
  Qed.

*)

End SPFUNCTOR_FACTS.

(*x
Section SIMPLE_SPF.

  Variable C : Type.
  Variable F : iType C -> Type.
  Context `{H : Functor _ F}.

  Variable S : Type.
  Variable P : S -> C -> Type.

  Variable (N : forall X, F X -> Container P X).
  Variable (NI : forall X, Container P X -> F X).
  Variable (COMMUTE : forall X1 X2 (f: forall i, X1 i -> X2 i) fx,
              N (map f fx) = (map f) (N fx)).
  Variable BIJ1 : forall X (fx : F X), NI (N fx) = fx.
  Variable BIJ2 : forall X (gx : Container P X), N (NI gx) = gx.

*)