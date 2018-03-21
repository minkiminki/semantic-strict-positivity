Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf.

Section FUNCTOR.

  Class Functor (F: Type -> Type) : Type :=
    {
      map {X Y} (f: X -> Y) : F X -> F Y;
    }.

  Definition allR (F: Type -> Type) `{Functor F}
             X Y (R : X -> Y -> Prop) : F X -> F Y -> Prop :=
    fun fx fy => exists (fr : F (sig (fun xy : X * Y => R (fst xy) (snd xy)))),
        map (fun xy => fst (proj1_sig xy)) fr = fx /\
        map (fun xy => snd (proj1_sig xy)) fr = fy.

  Definition allNR (F: Type -> Type) `{Functor F}
             A (T : A -> Type) (R : (forall a, T a) -> Prop) :
    (forall a, F (T a)) -> Type :=
    fun fx =>
      sig (fun fr : F (sig R) => forall a, map (fun f => proj1_sig f a) fr = fx a). 

  Definition allP (F: Type -> Type) `{Functor F} X
             (P : X -> Prop) : F X -> Prop :=
    fun fx => exists (fx' : F (sig P)), map (proj1_sig (P := P)) fx' = fx.

  Definition default_mem (F: Type -> Type) `{Functor F} X
             (fx : F X) (x : X) : Prop :=
    forall Pr, allP Pr fx -> Pr x.
  
  Class SFunctor (F: Type -> Type) : Type :=
    {
      Fn :> Functor F;
      mem {X} : F X -> X -> Prop;
      rel {X Y} (R: X -> Y -> Prop) : F X -> F Y -> Prop;
      tag X (fx: F X) : F (sig (@mem _ fx));
    }.

  Class NatTr (F G: Type -> Type) `{SFunctor F} `{SFunctor G} : Type :=
    {
      NT :> forall X, F X -> G X;
      MAP_COMMUTE : forall X1 X2 (f: X1 -> X2) fx,
          NT (map f fx) = (map f) (NT fx);
      MEM_COMMUTE : forall X (fx: F X) (x: X),
        mem fx x <-> mem (NT fx) x;
      REL_COMMUTE : forall X Y (R: X -> Y -> Prop)
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

  Class NatIso (F G: Type -> Type) `{SFunctor F} `{SFunctor G} : Type :=
    {
      Tr :> @NatTr F G _ _;
      NTinv : forall X, G X -> F X;
      BIJECTION1 : forall X (fx: F X), NTinv (NT _ fx) = fx;
      BIJECTION2 : forall X (gx: G X), NT _ (NTinv gx) = gx;
    }.

  Arguments NatTr F G {H H0}.
  Arguments NatIso F G {H H0}.
  Arguments NT {F G H H0 NatTr X}.
  Arguments NTinv {F G H H0 NatIso X}.

  Definition NatEmbed (F G : Type -> Type) `{SFunctor F} `{SFunctor G}
             (N : NatTr F G) : Prop :=
    forall X (x1 x2 : F X), NT (NatTr:=N) x1
                       = NT (NatTr:=N) x2 -> x1 = x2.

  Lemma INJECTIVE (F G: Type -> Type) `{NatIso F G} (X : Type)
        (fx fy : F X) (EQ : NT fx = NT fy) : fx = fy.
  Proof.
    apply (eq_trans (eq_sym (BIJECTION1 _ fx))
                    (eq_trans (f_equal NTinv EQ) (BIJECTION1 _ fy))).
  Qed.

  Lemma NatIso_Embed (F G : Type -> Type) `{SFunctor F} `{SFunctor G}
        (N : NatIso F G) : NatEmbed (@Tr _ _ _ _ N).
  Proof.
    intro X. apply INJECTIVE.
  Qed.

  Lemma INJECTIVE_R (F G: Type -> Type) `{NatIso F G} (X : Type)
        (gx gy : G X) (EQ : NTinv gx = NTinv gy) : gx = gy.
  Proof.
    apply (eq_trans (eq_sym (BIJECTION2 _ gx))
                    (eq_trans (f_equal NT EQ) (BIJECTION2 _ gy))).
  Qed.

  Lemma MAP_COMMUTE_R (F G: Type -> Type) `{NatIso F G} X1 X2
        (f : X1 -> X2) (fx : G X1) :
    NTinv (map f fx) = (map f) (NTinv fx).
  Proof.
    apply (INJECTIVE (H1 := H1)).
    rewrite MAP_COMMUTE.
    repeat rewrite BIJECTION2. reflexivity.
  Qed.

  Lemma MEM_COMMUTE_R (F G: Type -> Type) `{NatIso F G} X (fx : G X) (x : X)
    : mem fx x <-> mem (NTinv fx) x.
  Proof.
    rewrite <- (BIJECTION2 _ fx). rewrite BIJECTION1.
    symmetry. apply MEM_COMMUTE.
  Qed.

  Lemma REL_COMMUTE_R (F G: Type -> Type) `{NatIso F G} X Y R
        (fx : G X) (fy : G Y) :
    rel R fx fy <-> rel R (NTinv fx) (NTinv fy).
  Proof.
    rewrite <- (BIJECTION2 _ fx). rewrite <- (BIJECTION2 _ fy).
    repeat rewrite BIJECTION1.
    symmetry. apply REL_COMMUTE.
  Qed.    

  Program Definition Symmetric_NatIso (F G: Type -> Type) `{NatIso F G} : NatIso G F
    := Build_NatIso (Build_NatTr _ _
                                 (@NTinv _ _ _ _ _)
                                 (@MAP_COMMUTE_R _ _ _ _ _)
                                 (@MEM_COMMUTE_R _ _ _ _ _)
                                 (@REL_COMMUTE_R _ _ _ _ _))
                    (@NT _ _ _ _ _ )
                    (@BIJECTION2 _ _ _ _ _)
                    (@BIJECTION1 _ _ _ _ _).

  Definition Reflexive_NatTr (F : Type -> Type) `{SFunctor F} : NatTr F F
    := Build_NatTr _ _ (fun _ => id)
                   (fun _ _ _ _=> eq_refl)
                   (fun _ _ _ => iff_refl _)
                   (fun _ _ _ _ _ => iff_refl _).

  Definition Reflexive_NatIso (F : Type -> Type) `{SFunctor F} : NatIso F F
    := Build_NatIso Reflexive_NatTr
                    (fun _ => id)
                    (fun _ _ => eq_refl)
                    (fun _ _ => eq_refl).

  Program Definition Transitive_NatTr (F G H: Type -> Type)
          `{FnF : SFunctor F} `{FnG : SFunctor G} `{FnH : SFunctor H}
          `{@NatTr _ _ FnF FnG} `{@NatTr _ _ FnG FnH}: NatTr F H
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

  Program Definition Transitive_NatIso (F G H: Type -> Type)
          `{FnF : SFunctor F} `{FnG : SFunctor G} `{FnH : SFunctor H}
          `{@NatIso _ _ FnF FnG} `{@NatIso _ _ FnG FnH}: NatIso F H
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

End FUNCTOR.
