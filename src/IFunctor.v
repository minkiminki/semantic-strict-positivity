Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf.

Section IFUNCTOR.

  Class Functor C (F: iType C -> Type) : Type :=
    {
      map {X Y: iType C} (f: forall i, X i -> Y i) : F X -> F Y;
      mem {X} : F X -> forall {i}, X i -> Prop;
      rel {X Y} (R: forall {i}, X i -> Y i -> Prop) (fx: F X) (fy: F Y) : Prop;
      tag X (fx: F X) : F (sigI (@mem _ fx));

      TAG X (fx: F X) : map (@projI1 _ _ _) (tag fx) = fx;
(*
      TAG X (fx: F X)
          (MAP_COMPOSE : forall X Y Z (f: forall i, X i -> Y i) (g: forall i, Y i -> Z i)
                                fx, map g (map f fx) = map (fun i x => g i (f i x)) fx)
      : map (@projI1 _ _ _) (tag fx) = fx;
*)
    }.

  Definition MAP_COMPOSE C (F : iType C -> Type) `{Functor _ F} : Prop :=
    forall (X Y Z: iType C) (f: forall i, X i -> Y i) (g: forall i, Y i -> Z i) fx,
      map g (map f fx) = map (fun i x => g i (f i x)) fx.

  Definition MAP_ID C (F : iType C -> Type) `{Functor _ F} : Prop :=
    forall (X: iType C) fx, map (fun i (x : X i) => x) fx = fx.

  Class NatIso C (F G: iType C -> Type) `{Functor _ F} `{Functor _ G} : Type :=
    {
      NT :> forall (X: iType C), F X -> G X;
      NTinv : forall (X: iType C), G X -> F X;
      MAP_COMMUTE : forall X1 X2 (f: forall i, X1 i -> X2 i) fx,
          NT (map f fx) = (map f) (NT fx);
      MEM_COMMUTE : forall X i (fx: F X) (x: X i),
          mem fx x <-> mem (NT fx) x;
      REL_COMMUTE : forall X Y (R: forall i, X i -> Y i -> Prop) (fx : F X) (fy : F Y),
          rel R fx fy <-> rel R (NT fx) (NT fy);
      BIJECTION1 : forall X (fx: F X), NTinv (NT fx) = fx;
      BIJECTION2 : forall X (gx: G X), NT (NTinv gx) = gx;
    }.
  Arguments NatIso {C} F G {H H0}.
  Arguments NT {C F G H H0 NatIso X}.
  Arguments NTinv {C F G H H0 NatIso X}.
  (* instances *)

  Program Definition Symmetric_NatIso C (F G: iType C -> Type) `{NatIso _ F G} : NatIso G F
    := Build_NatIso _ _ (@NTinv _ _ _ _ _ _ ) (@NT _ _ _ _ _ _ ) _ _ _ _ _.
  Next Obligation.
    destruct H1. simpl.
    rewrite <- (BIJECTION3 _ (map f (NTinv0 X1 fx))).
    rewrite MAP_COMMUTE0. rewrite BIJECTION4.
    reflexivity.
  Qed.
  Next Obligation.
    destruct H1. simpl.
    rewrite <- (BIJECTION4 _ fx). rewrite BIJECTION3.
    symmetry. apply MEM_COMMUTE0.
  Qed.
  Next Obligation.
    destruct H1. simpl.
    rewrite <- (BIJECTION4 _ fx). rewrite <- (BIJECTION4 _ fy).
    repeat rewrite BIJECTION3.
    symmetry. apply REL_COMMUTE0.
  Qed.
  Next Obligation.
    destruct H1. auto.
  Qed.
  Next Obligation.
    destruct H1. auto.
  Qed.
  
  Program Definition Reflexive_NatIso C (F : iType C -> Type) `{Functor _ F} : NatIso F F
    := Build_NatIso _ _ (fun _ => id) (fun _ => id) _ _ _ _ _.
  Next Obligation.  
    tauto.
  Qed.
  Next Obligation.  
    tauto.
  Qed.

  Program Definition Tranitive_NatIso C (F G H: iType C -> Type)
          `{FnF : Functor _ F} `{FnG : Functor _ G} `{FnH : Functor _ H}
          `{@NatIso _ _ _ FnF FnG} `{@NatIso _ _ _ FnG FnH}: NatIso F H
    := Build_NatIso _ _ (fun _ fx => NT (NT fx)) (fun _ hx => NTinv (NTinv hx)) _ _ _ _ _.
  Next Obligation.
    simpl.
    repeat rewrite MAP_COMMUTE. auto.
  Defined.
  Next Obligation.
    simpl.
    repeat rewrite MEM_COMMUTE. tauto.
  Defined.
  Next Obligation.
    simpl.
    repeat rewrite REL_COMMUTE. tauto.
  Defined.
  Next Obligation.
    simpl.
    repeat rewrite BIJECTION1. auto.
  Defined.
  Next Obligation.
    simpl.
    repeat rewrite BIJECTION2. auto.
  Defined.

End IFUNCTOR.
