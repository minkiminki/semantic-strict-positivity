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
    }.

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

  Lemma INJECTIVE C (F G: iType C -> Type) `{NatIso _ F G} (X : iType C)
        (fx fy : F X) (EQ : NT fx = NT fy) : fx = fy.
  Proof.
    apply f_equal with (f := NTinv) in EQ.
    repeat rewrite BIJECTION1 in EQ.
    apply EQ.
  Qed.

  Lemma MAP_COMMUTE_R C (F G: iType C -> Type) `{NatIso _ F G} X1 X2
        (f : forall i, X1 i -> X2 i) (fx : G X1) :
    NTinv (map f fx) = (map f) (NTinv fx).
  Proof.
    apply (INJECTIVE (H1 := H1)).
    rewrite MAP_COMMUTE.
    repeat rewrite BIJECTION2. reflexivity.
  Qed.    

  Lemma MEM_COMMUTE_R C (F G: iType C -> Type) `{NatIso _ F G} X i (fx : G X) (x : X i)
    : mem fx x <-> mem (NTinv fx) x.
  Proof.
    rewrite <- (BIJECTION2 _ fx). rewrite BIJECTION1.
    symmetry. apply MEM_COMMUTE.
  Qed.    

  Lemma REL_COMMUTE_R C (F G: iType C -> Type) `{NatIso _ F G} X Y R
        (fx : G X) (fy : G Y) :
    rel R fx fy <-> rel R (NTinv fx) (NTinv fy).
  Proof.
    rewrite <- (BIJECTION2 _ fx). rewrite <- (BIJECTION2 _ fy).
    repeat rewrite BIJECTION1.
    symmetry. apply REL_COMMUTE.
  Qed.    


  Program Definition Symmetric_NatIso C (F G: iType C -> Type) `{NatIso _ F G} : NatIso G F
    := Build_NatIso _ _
                    (@NTinv _ _ _ _ _ _ )
                    (@NT _ _ _ _ _ _ )
                    (@MAP_COMMUTE_R _ _ _ _ _ _) 
                    (@MEM_COMMUTE_R _ _ _ _ _ _)
                    (@REL_COMMUTE_R _ _ _ _ _ _) 
                    (@BIJECTION2 _ _ _ _ _ _)
                    (@BIJECTION1 _ _ _ _ _ _).
  
  Program Definition Reflexive_NatIso C (F : iType C -> Type) `{Functor _ F} : NatIso F F
    := Build_NatIso _ _ (fun _ => id) (fun _ => id) _ _ _ _ _.
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.  
    reflexivity.
  Qed.

  Program Definition Transitive_NatIso C (F G H: iType C -> Type)
          `{FnF : Functor _ F} `{FnG : Functor _ G} `{FnH : Functor _ H}
          `{@NatIso _ _ _ FnF FnG} `{@NatIso _ _ _ FnG FnH}: NatIso F H
    := Build_NatIso _ _ (fun _ fx => NT (NT fx)) (fun _ hx => NTinv (NTinv hx)) _ _ _ _ _.
  Next Obligation.
    repeat rewrite MAP_COMMUTE. reflexivity.
  Defined.
  Next Obligation.
    repeat rewrite MEM_COMMUTE. reflexivity.
  Defined.
  Next Obligation.
    repeat rewrite REL_COMMUTE. reflexivity.
  Defined.
  Next Obligation.
    repeat rewrite BIJECTION1. reflexivity.
  Defined.
  Next Obligation.
    repeat rewrite BIJECTION2. reflexivity.
  Defined.

End IFUNCTOR.
