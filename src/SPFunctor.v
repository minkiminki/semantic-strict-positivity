Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor.


(* Categories *)

Section UniversalFunctor.
  Variable (Sh1 Sh2: Type).

  Definition UF := Expn Sh1 (Coprod Ident (Const Sh2)).

  Definition UF_sFunctor : SFunctorData UF :=
    function_sFunctorData Sh1 (coproduct_sFunctorData id_sFunctorData
                                                      (const_sFunctorData Sh2)).

  Definition UF_FunctorProp : FunctorProp UF_sFunctor.
  Proof.
    constructor.
    - intro. extensionality s. extensionality s1. simplify.
      destruct (s s1) eqn : EQ; auto.
    - intros. extensionality s. simplify.
      destruct (x1 s); auto.
  Qed.
  Hint Resolve UF_FunctorProp.

  Program Definition UF_SFunctorProp : SFunctorProp UF_sFunctor.
  Proof.
    constructor.
    intros. inv MEM. apply Function_mem with (d := d). simplify.
    destruct (fx d); simplify; subst; auto.
  Qed.

  Lemma UF_map_injective X Y (f: X -> Y) (u1 u2: UF X) 
        (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
        (EQ: UF_sFunctor.(map) f u1 = UF_sFunctor.(map) f u2):
    u1 = u2.
  Proof.
    extensionality s. apply equal_f with (x:=s) in EQ. simplify. 
    destruct (u1 s), (u2 s); inv EQ; auto.
    apply INJ in H0. subst; auto.
  Qed.

  Lemma UF_map_pointwise X Y (u: UF X) (f g: X -> Y)
        (ALL: forall x, UF_sFunctor.(mem) u x -> f x = g x):
    UF_sFunctor.(map) f u = UF_sFunctor.(map) g u.
  Proof.
    extensionality s. simplify.
    destruct (u s) eqn : EQ; auto. simplify.
    specialize (ALL i). f_equal. apply ALL.
    econstructor. simplify. rewrite EQ. constructor.
  Qed.

  Lemma UF_rel_monotone X (u1 u2: UF X) (r r': X -> X -> Prop)
        (LE: forall x0 x1: X, r x0 x1 -> r' x0 x1) (R: UF_sFunctor.(rel) r u1 u2)
        : UF_sFunctor.(rel) r' u1 u2.
  Proof.
    simplify. intro d. specialize (R d).
    inv R; constructor; simplify; auto.
  Qed.

  Lemma UF_map_mem X Y (f: X -> Y) (u: UF X) (x: X) (MEM: UF_sFunctor.(mem) u x)
        : UF_sFunctor.(mem) (UF_sFunctor.(map) f u) (f x).
  Proof.
    inv MEM. econstructor. instantiate (1:=d). simplify.
    destruct (u d); inversion MEM0. constructor.
  Qed.

End UniversalFunctor.

Class SPFunctor (F : Type -> Type)
  := {
      Fn :> SFunctorData F;
      Sh1 : Type;
      Sh2 : Type;
      emb : NatTrans Fn (UF_sFunctor Sh1 Sh2);
      emb_s_prop : SNatTransProp _ _ emb;
      INJECTIVE : forall T (x1 x2 : F T) (EQ : emb _ x1 = emb _ x2), x1 = x2;
    }.

Section ddd.
  Variable F : Type -> Type.

  Coercion toSFunctor (x: SPFunctor F) : SFunctorData F := @Fn _ x.
End ddd.

Print Coercions.

Section SPFunctorFacts.

  Variable F : Type -> Type.
  Context `{Fn : SPFunctor F}.

  Definition toFunctorProp : FunctorProp Fn.
  Proof.
    constructor.
    - intros. extensionality s.
      apply INJECTIVE.
      rewrite MAP_COMMUTE. rewrite (UF_FunctorProp _ _).(MAP_ID). auto.
    - intros. apply INJECTIVE.
      repeat rewrite MAP_COMMUTE. rewrite (UF_FunctorProp _ _).(MAP_COMPOSE). auto.
  Qed.

  Definition toSFunctorProp : SFunctorProp Fn.
  Proof.
    constructor. intros.
    apply (@MEM_COMMUTE _ _ _ _ _ (@emb_s_prop _ _)).
    apply (@MEM_COMMUTE _ _ _ _ _ (@emb_s_prop _ _)) in MEM.
    rewrite (@MAP_COMMUTE _ _ _ _ (@emb _ Fn)).
    apply (UF_SFunctorProp _ _).(MAP_MEM). auto.
  Qed.

  Lemma map_injective X Y (f: X -> Y) (u1 u2: F X)
        (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
        (EQ: Fn.(map) f u1 = Fn.(map) f u2):
    u1 = u2.
  Proof.
    apply INJECTIVE. apply (UF_map_injective INJ).
    repeat rewrite <- MAP_COMMUTE. simplify.
    setoid_rewrite EQ. auto.
  Qed.

  Lemma map_pointwise X Y (f g: X -> Y) (m: F X)
        (ALL: forall x, Fn.(mem) m x -> f x = g x):
    Fn.(map) f m = Fn.(map) g m.
  Proof.
    apply INJECTIVE.  repeat rewrite MAP_COMMUTE.
    apply UF_map_pointwise.
    intros. apply ALL. 
    apply (@MEM_COMMUTE _ _ _ _ _ (@emb_s_prop _ _)). assumption.
  Qed.
  
  Lemma rel_monotone X (u1 u2: F X) (r r': X -> X -> Prop)
        (LE: forall x0 x1: X, r x0 x1 -> r' x0 x1) (R: Fn.(rel) r u1 u2)
    : Fn.(rel) r' u1 u2.
  Proof.
    apply (@REL_COMMUTE _ _ _ _ _ (@emb_s_prop _ _)).
    apply (@REL_COMMUTE _ _ _ _ _ (@emb_s_prop _ _)) in R.
    apply (UF_rel_monotone _ LE). auto.
  Qed.

End SPFunctorFacts.
