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
  Hint Unfold UF.

  Global Instance UF_FunctorData : FunctorData UF.
  Proof.
    unfold UF. auto.
  Defined.

  Global Instance UF_SFunctorData : @SFunctorData UF UF_FunctorData
    := function_sFunctorData Sh1 (Coprod Ident (Const Sh2)).

  Hint Resolve UF_FunctorData UF_SFunctorData.


  Global Instance UF_FunctorProp : FunctorProp UF.
  Proof.
    constructor.
    - intro. extensionality s. extensionality s1. simplify.
      destruct (s s1) eqn : EQ; auto.
    - intros. extensionality s. simplify.
      destruct (x1 s); auto.
  Qed.
  Hint Resolve UF_FunctorProp.

  Global Instance UF_SFunctorProp : SFunctorProp UF.
  Proof.
    constructor.
    intros. inv MEM. apply Function_mem with (d := d). simplify.
    destruct (fx d); simplify; subst; auto.
  Qed.

  Lemma UF_map_injective X Y (f: X -> Y) (u1 u2: UF X) 
        (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
        (EQ: map f u1 = map f u2):
    u1 = u2.
  Proof.
    extensionality s. apply equal_f with (x:=s) in EQ. simplify. 
    destruct (u1 s), (u2 s); inv EQ; auto.
    apply INJ in H0. subst; auto.
  Qed.

  Lemma UF_map_pointwise X Y (u: UF X) (f g: X -> Y)
        (ALL: forall x, mem u x -> f x = g x):
    map f u = map g u.
  Proof.
    extensionality s. simplify.
    destruct (u s) eqn : EQ; auto. simplify.
    specialize (ALL i). f_equal. apply ALL.
    econstructor. simplify. rewrite EQ. constructor.
  Qed.

  Lemma UF_rel_monotone X (u1 u2: UF X) (r r': X -> X -> Prop)
        (LE: forall x0 x1: X, r x0 x1 -> r' x0 x1) (R: rel r u1 u2)
        : rel r' u1 u2.
  Proof.
    simplify. intro d. specialize (R d).
    inv R; constructor; simplify; auto.
  Qed.

  Lemma UF_map_mem X Y (f: X -> Y) (u: UF X) (x: X) (MEM: mem u x)
        : mem (map f u) (f x).
  Proof.
    inv MEM. econstructor. instantiate (1:=d). simplify.
    destruct (u d); inversion MEM0. constructor.
  Qed.

End UniversalFunctor.

Class SPFunctor (F : Type -> Type) `{SFunctorData F}
  := {
      Sh1 : Type;
      Sh2 : Type;
      emb :> @NatTrans F (UF Sh1 Sh2) _ _;
      emb_s_prop :> @SNatTransProp F (UF Sh1 Sh2) _ _ _ _ emb;
      INJECTIVE : forall T (x1 x2 : F T) (EQ : emb _ x1 = emb _ x2), x1 = x2;
      TAG : forall X (x: F X), map (@projT1 X _) (tag x) = x;
    }.                      
Arguments SPFunctor F {H} {H0}.

Section SPFunctorFacts.

  Context {F : Type -> Type}.
  Context `{SPFunctor F}.

  Global Instance toFunctorProp : FunctorProp F.
  Proof.
    constructor.
    - intros. extensionality s.
      apply INJECTIVE.
      rewrite MAP_COMMUTE. rewrite MAP_ID. auto.
    - intros. apply INJECTIVE.
      repeat rewrite MAP_COMMUTE. rewrite MAP_COMPOSE. auto.
  Qed.

  Global Instance toSFunctorProp : SFunctorProp F.
  Proof.
    constructor; intros.
    apply MEM_COMMUTE. apply MEM_COMMUTE in MEM.
    rewrite MAP_COMMUTE. apply (MAP_MEM f _ _ MEM).
  Qed.

  Lemma map_injective X Y (f: X -> Y) (u1 u2: F X)
        (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
        (EQ: map f u1 = map f u2):
    u1 = u2.
  Proof.
    apply INJECTIVE. apply (UF_map_injective INJ).
    repeat rewrite <- MAP_COMMUTE.
    rewrite EQ. auto.
  Qed.

  Lemma map_pointwise X Y (f g: X -> Y) (m: F X)
        (ALL: forall x, mem m x -> f x = g x):
    map f m = map g m.
  Proof.
    apply INJECTIVE.  repeat rewrite MAP_COMMUTE.
    apply UF_map_pointwise.
    intros. apply ALL, MEM_COMMUTE, H2.
  Qed.
  
  Lemma rel_monotone X (u1 u2: F X) (r r': X -> X -> Prop)
        (LE: forall x0 x1: X, r x0 x1 -> r' x0 x1) (R: rel r u1 u2)
    : rel r' u1 u2.
  Proof.
    apply REL_COMMUTE. apply REL_COMMUTE in R.
    apply (UF_rel_monotone _ LE). auto.
  Qed.

  Lemma MAP_DEP X Y fx (f: forall x (MEM:mem fx x), Y) (g: Y -> X)
        (INV: forall x r, g (f x r) = x) : map g (map_dep fx f) = fx.
  Proof.
    unfold map_dep. rewrite MAP_COMPOSE. unfold compose.
    replace (fun x : {H2 : X & mem fx H2} => g (let (x0, m) := x in f x0 m)) with
        (@projT1 X (mem fx)).
    - apply TAG.
    - extensionality s. destruct s. auto.
  Qed.

End SPFunctorFacts.
