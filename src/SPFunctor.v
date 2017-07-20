Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor.


(* Classical *)

Theorem dependent_unique_choice :
  forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
    (forall x:A, exists! y : B x, R x y) ->
    { f : forall x:A, B x | forall x:A, R x (f x) }.
Proof.
  intros A B R H.
  assert (Hexuni:forall x, exists! y, R x y).
  intro x. apply H.
  econstructor. instantiate (1 := (fun x => proj1_sig (constructive_definite_description (R x) (Hexuni x)))).
  intro x.
  apply (proj2_sig (constructive_definite_description (R x) (Hexuni x))).
Defined.

Theorem unique_choice :
  forall (A B:Type) (R:A -> B -> Prop),
    (forall x:A,  exists! y : B, R x y) ->
    { f : A -> B | forall x:A, R x (f x) }.
Proof.
  intros A B.
  apply dependent_unique_choice with (B:=fun _:A => B).
Defined.


(* Categories *)

Section UniversalFunctor.
  Variable (Sh1 Sh2: Type).

  Definition UF T := Sh1 -> T + Sh2.

  Definition UF_functorMixin: Functor.mixin_of UF :=
    function_functorMixin Sh1 (coproduct_functorType id_functorType (const_functorType Sh2)).
  Definition UF_sFunctorMixin: SFunctor.mixin_of UF UF_functorMixin.(Functor.map) :=
    function_sFunctorMixin Sh1 (coproduct_sFunctorType id_sFunctorType (const_sFunctorType Sh2)).

  Canonical Structure UF_FunctorType := FunctorType UF_functorMixin.
  Canonical Structure UF_SFunctorType := SFunctorType UF_FunctorType UF_sFunctorMixin.
  Hint Unfold UF_FunctorType.
  Hint Unfold UF_SFunctorType.

  Lemma UF_map_injective X Y (u1 u2: UF X) (f: X -> Y)
        (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
        (EQ: fmap f u1 = fmap f u2):
    u1 = u2.
  Proof.
    extensionality s. apply equal_f with (x:=s) in EQ. simplify. 
    destruct (u1 s), (u2 s); inv EQ; auto.
    apply INJ in H0. subst; auto.
  Qed.

  Lemma UF_map_pointwise X Y (u: UF X) (f g: X -> Y)
        (ALL: forall x, fmem u x -> f x = g x):
    fmap f u = fmap g u.
  Proof.
    extensionality s. simplify.
    destruct (u s) eqn : EQ; auto.
    specialize (ALL x). f_equal. apply ALL.
    econstructor. simplify. rewrite EQ. auto.
  Qed.

End UniversalFunctor.


Module SPFunctor.
  Program Record mixin_of (F: Type -> Type)
          (F_map:forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2)
          (F_mem:forall X, F X -> X -> Prop)
          (F_rel:forall X Y (rel: X -> Y -> Prop) (fx:F X) (fy:F Y), Prop)
  : Type := Mixin {
    Sh1: Type;
    Sh2: Type;
    embedding: forall T (x: F T), UF Sh1 Sh2 T;

    _INJECTIVE: forall T x1 x2 (EQ: @embedding T x1 = @embedding T x2), x1 = x2;
    _NATURAL_MAP:
      forall T1 T2 (f: T1 -> T2) fx1,
        embedding (F_map _ _ f fx1) = fmap f (embedding fx1);
    _NATURAL_MEM: forall X fx x, F_mem X fx x <-> fmem (embedding fx) x;
    _NATURAL_REL:
      forall T1 T2 (r: T1 -> T2 -> Prop) fx1 fx2,
        frel r (embedding fx1) (embedding fx2) <-> (F_rel _ _ r fx1 fx2);
  }.

  Record class_of (F: Type -> Type): Type := Class {
    base :> SFunctor.class_of F;
    ext :> mixin_of F base.(SFunctor.base).(Functor.map)
                      base.(SFunctor.ext).(SFunctor.mem) base.(SFunctor.ext).(SFunctor.rel);
  }.

  Structure type: Type := Pack {
    sort :> Type -> Type;
    class :> class_of sort;
    _: Type -> Type;
  }.

  Definition unpack K (k: forall T (c: class_of T), K T c) cF :=
    match cF return K _ (class cF) with
    | Pack c _ => k _ c
    end.

  Definition pack :=
    let k T c m := Pack (Class c m) T in
    SFunctor.unpack _ k.

  Coercion sFunctorType cF := SFunctor.Pack (class cF) cF.
  Coercion functorType cF := Functor.Pack (class cF).(base).(SFunctor.base) cF.

End SPFunctor.

Notation SPFunctorType := SPFunctor.type.
Notation spFunctorType := SPFunctor.pack.
Canonical Structure SPFunctor.sFunctorType.
Canonical Structure SPFunctor.functorType.
Definition functor_embedding F := SPFunctor.embedding (SPFunctor.class F).
Notation "'femb' fx" := (@functor_embedding _ _ fx) (at level 0).
Hint Unfold functor_embedding.

Module SPFunctorFacts.

  Lemma INJECTIVE (PF: SPFunctorType) T (x1 x2: PF T) (EQ: femb x1 = femb x2) :
    x1 = x2.
  Proof.
    apply PF.(SPFunctor._INJECTIVE). apply EQ.
  Qed.

  Lemma NATURAL_MAP (PF: SPFunctorType) T1 T2 (f: T1 -> T2) (fx: PF T1) :
    femb (fmap f fx) = fmap f (femb fx).
  Proof.
    apply SPFunctor._NATURAL_MAP.
  Qed.

  Lemma NATURAL_MEM (PF: SPFunctorType) X (fx: PF X) (x: X) :
    fmem fx x <-> fmem (femb fx) x.
  Proof.
    apply SPFunctor._NATURAL_MEM.
  Qed.

  Lemma NATURAL_REL (PF: SPFunctorType) T1 T2 (r: T1 -> T2 -> Prop)
        (fx1: PF T1) (fx2: PF T2) : 
    frel r fx1 fx2 <-> frel r (femb fx1) (femb fx2).
  Proof.
    split; intros.
    - apply SPFunctor._NATURAL_REL. apply H.
    - apply SPFunctor._NATURAL_REL in H. apply H.
  Qed.

  Lemma map_injective (PF: SPFunctorType) X Y (u1 u2: PF X) (f: X -> Y)
         (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
         (EQ: fmap f u1 = fmap f u2):
     u1 = u2.
  Proof.
    apply (SPFunctorFacts.INJECTIVE PF). apply (UF_map_injective INJ).
    repeat rewrite <- SPFunctorFacts.NATURAL_MAP.
    rewrite EQ. auto.
  Qed.

  Lemma map_pointwise (PF: SPFunctorType) X Y (f g: X -> Y) (m: PF X)
        (ALL: forall x, fmem m x -> f x = g x):
    fmap f m = fmap g m.
  Proof.
    apply SPFunctorFacts.INJECTIVE. 
    repeat rewrite SPFunctorFacts.NATURAL_MAP.
    apply UF_map_pointwise.
    intros. apply ALL, NATURAL_MEM, H.
  Qed.

End SPFunctorFacts.

(* Fixpoint *)
