Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf.

Section IFUNCTOR.

  Class Functor C (F: iType C -> Type) : Type :=
    {
      map {X Y: iType C} (f: forall i, X i -> Y i) : F X -> F Y;
    }.

  Definition allR C (F: iType C -> Type) `{Functor _ F}
             X Y (R : forall i, X i -> Y i -> Prop) : F X -> F Y -> Prop :=
    fun fx fy => exists (fr : F (sig2I _ _ R)),
        map (proj2I1 (R := R)) fr = fx /\
        map (proj2I2 (R := R)) fr = fy.

  Definition allP C (F: iType C -> Type) `{Functor _ F} X
             (P : forall i, X i -> Prop) : F X -> Prop :=
    fun fx => exists (fx' : F (sigI P)), map (projI1 (P := P)) fx' = fx.

  Definition default_mem C (F: iType C -> Type) `{Functor _ F} X
             (fx : F X) i (x : X i) : Prop :=
    forall Pr, allP _ Pr fx -> Pr i x.

  Class SFunctor C (F: iType C -> Type) : Type :=
    {
      Fn :> Functor F;
      mem {X} : F X -> forall {i}, X i -> Prop;
      rel {X Y} (R: forall {i}, X i -> Y i -> Prop) (fx: F X) (fy: F Y) : Prop;
      tag X (fx: F X) : F (sigI (@mem _ fx));
    }.

  Class NatTr C (F G: iType C -> Type) `{SFunctor _ F} `{SFunctor _ G} : Type :=
    {
      NT :> forall (X: iType C), F X -> G X;
      MAP_COMMUTE : forall X1 X2 (f: forall i, X1 i -> X2 i) fx,
          NT (map f fx) = (map f) (NT fx);
      MEM_COMMUTE : forall X i (fx: F X) (x: X i),
        mem fx x <-> mem (NT fx) x;
      REL_COMMUTE : forall X Y (R: forall i, X i -> Y i -> Prop)
                           (fx : F X) (fy : F Y),
          rel R fx fy <-> rel R (NT fx) (NT fy);
    }.


(*
  Class SNatTr C (F G: iType C -> Type) `{SFunctor _ F} `{SFunctor _ G}
        `{NatTr _ F G}: Type :=
    {
      MEM_COMMUTE : forall X i (fx: F X) (x: X i),
        mem fx x <-> mem (NT _ fx) x;
      REL_COMMUTE : forall X Y (R: forall i, X i -> Y i -> Prop)
                           (fx : F X) (fy : F Y),
          rel R fx fy <-> rel R (NT _ fx) (NT _ fy);
    }.
*)

  Class NatIso C (F G: iType C -> Type) `{SFunctor _ F} `{SFunctor _ G} : Type :=
    {
      Tr :> @NatTr C F G _ _;
      NTinv : forall (X: iType C), G X -> F X;
      BIJECTION1 : forall X (fx: F X), NTinv (NT _ fx) = fx;
      BIJECTION2 : forall X (gx: G X), NT _ (NTinv gx) = gx;
    }.

  Arguments NatTr {C} F G {H H0}.
  Arguments NatIso {C} F G {H H0}.
  Arguments NT {C F G H H0 NatTr X}.
  Arguments NTinv {C F G H H0 NatIso X}.
  (* instances *)

  Definition NatEmbed C (F G : iType C -> Type) `{SFunctor _ F} `{SFunctor _ G}
             (N : NatTr F G) : Prop :=
    forall X (x1 x2 : F X), NT (NatTr:=N) x1
                            = NT (NatTr:=N) x2 -> x1 = x2.

  Lemma INJECTIVE C (F G: iType C -> Type) `{NatIso _ F G} (X : iType C)
        (fx fy : F X) (EQ : NT fx = NT fy) : fx = fy.
  Proof.
    apply (eq_trans (eq_sym (BIJECTION1 _ fx))
                    (eq_trans (f_equal NTinv EQ) (BIJECTION1 _ fy))).
  Qed.

  Lemma NatIso_Embed C (F G : iType C -> Type) `{SFunctor _ F} `{SFunctor _ G}
        (N : NatIso F G) : NatEmbed (@Tr _ _ _ _ _ N).
  Proof.
    intro X. apply INJECTIVE.
  Qed.

  Lemma INJECTIVE_R C (F G: iType C -> Type) `{NatIso _ F G} (X : iType C)
        (gx gy : G X) (EQ : NTinv gx = NTinv gy) : gx = gy.
  Proof.
    apply (eq_trans (eq_sym (BIJECTION2 _ gx))
                    (eq_trans (f_equal NT EQ) (BIJECTION2 _ gy))).
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
    := Build_NatIso (Build_NatTr _ _
                                 (@NTinv _ _ _ _ _ _)
                                 (@MAP_COMMUTE_R _ _ _ _ _ _)
                                 (@MEM_COMMUTE_R _ _ _ _ _ _)
                                 (@REL_COMMUTE_R _ _ _ _ _ _))
                    (@NT _ _ _ _ _ _ )
                    (@BIJECTION2 _ _ _ _ _ _)
                    (@BIJECTION1 _ _ _ _ _ _).

  Definition Reflexive_NatTr C (F : iType C -> Type) `{SFunctor _ F} : NatTr F F
    := Build_NatTr _ _ (fun _ => id)
                   (fun _ _ _ _ => eq_refl)
                   (fun _ _ _ _ => iff_refl _)
                   (fun _ _ _ _ _ => iff_refl _).

  Definition Reflexive_NatIso C (F : iType C -> Type) `{SFunctor _ F} : NatIso F F
    := Build_NatIso Reflexive_NatTr
                    (fun _ => id)
                    (fun _ _ => eq_refl)
                    (fun _ _ => eq_refl).

  Goal True. apply I. Qed.

  Program Definition Transitive_NatTr C (F G H: iType C -> Type)
          `{FnF : SFunctor _ F} `{FnG : SFunctor _ G} `{FnH : SFunctor _ H}
          `{@NatTr _ _ _ FnF FnG} `{@NatTr _ _ _ FnG FnH}: NatTr F H
    := Build_NatTr _ _ (fun _ fx => NT (NT fx)) _ _ _.
  Next Obligation.
    apply eq_trans with (y := NT (map f (NT fx))).
    - f_equal. apply MAP_COMMUTE.
    - apply MAP_COMMUTE.
  Qed.
  Next Obligation.
    apply iff_trans with (B := mem (NT fx) x); apply MEM_COMMUTE.
  Qed.
  Next Obligation.
    apply iff_trans with (B := rel R (NT fx) (NT fy)); apply REL_COMMUTE.
  Qed.

  Program Definition Transitive_NatIso C (F G H: iType C -> Type)
          `{FnF : SFunctor _ F} `{FnG : SFunctor _ G} `{FnH : SFunctor _ H}
          `{@NatIso _ _ _ FnF FnG} `{@NatIso _ _ _ FnG FnH}: NatIso F H
    := Build_NatIso Transitive_NatTr (fun _ hx => NTinv (NTinv hx)) _ _.
  Next Obligation.
    apply eq_trans with (y := NTinv (NT fx)).
    - f_equal. apply BIJECTION1.
    - apply BIJECTION1.
  Qed.
  Next Obligation.
    apply eq_trans with (y := NT (NTinv gx)).
    - f_equal. apply BIJECTION2.
    - apply BIJECTION2.
  Qed.

End IFUNCTOR.
