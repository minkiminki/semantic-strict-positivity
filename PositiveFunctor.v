Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.

Require Import Category.

Set Implicit Arguments.
Set Automatic Coercions Import.


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
   Definition UF_pFunctorMixin: PFunctor.mixin_of UF UF_functorMixin.(Functor.map) :=
     function_pFunctorMixin Sh1 (coproduct_pFunctorType id_pFunctorType (const_pFunctorType Sh2)).
End UniversalFunctor.

Canonical Structure UF_FunctorType Sh1 Sh2 := FunctorType (UF_functorMixin Sh1 Sh2).
Canonical Structure UF_PFunctorType Sh1 Sh2 := PFunctorType (UF_FunctorType Sh1 Sh2) (UF_pFunctorMixin Sh1 Sh2).
Hint Unfold UF_FunctorType.
Hint Unfold UF_PFunctorType.


Module PositiveFunctor.
  Program Record mixin_of (F: Type -> Type)
          (F_map:forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2)
          (F_mem:forall X, F X -> X -> Type)
          (F_rel:forall X Y (rel: X -> Y -> Prop) (fx:F X) (fy:F Y), Prop)
  : Type := Mixin {
    Sh1: Type;
    Sh2: Type;
    embedding: forall T (x: F T), UF Sh1 Sh2 T;

    INJECTIVE: forall T x1 x2 (EQ: @embedding T x1 = @embedding T x2), x1 = x2;
    NATURAL_MAP:
      forall T1 T2 (f: T1 -> T2) fx1,
        embedding (F_map _ _ f fx1) = fmap f (embedding fx1);
    NATURAL_MEM1: forall X fx x, F_mem X fx x -> fmem (embedding fx) x;
    NATURAL_MEM2: forall X fx x, fmem (embedding fx) x -> F_mem X fx x;
    NATURAL_REL:
      forall T1 T2 (r: T1 -> T2 -> Prop) fx1 fx2,
        frel r (embedding fx1) (embedding fx2) <-> (F_rel _ _ r fx1 fx2);
  }.

  Record class_of (F: Type -> Type): Type := Class {
    base :> PFunctor.class_of F;
    ext :> mixin_of F base.(PFunctor.base).(Functor.map)
                      base.(PFunctor.ext).(PFunctor.mem) base.(PFunctor.ext).(PFunctor.rel);
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
    PFunctor.unpack _ k.

  Coercion pFunctorType cF := PFunctor.Pack (class cF) cF.
  Coercion functorType cF := Functor.Pack (class cF).(base).(PFunctor.base) cF.
End PositiveFunctor.

Notation positiveFunctorType := PositiveFunctor.type.
Notation PositiveFunctorType := PositiveFunctor.pack.
Canonical Structure PositiveFunctor.pFunctorType.
Canonical Structure PositiveFunctor.functorType.
Definition functor_embedding F := PositiveFunctor.embedding (PositiveFunctor.class F).
Notation "'femb' fx" := (@functor_embedding _ _ fx) (at level 0).
Hint Unfold functor_embedding.


(* Fixpoint *)

Section MFix.
  Variable PF: positiveFunctorType.

  Inductive ufix: Type :=
  | Ufix: UF PF.(PositiveFunctor.Sh1) PF.(PositiveFunctor.Sh2) ufix -> ufix
  .

  Inductive range: forall (u:ufix), Type :=
  | Range
      (m: PF ufix)
      (MEM: forall u, fmem (femb m) u -> range u):
      range (Ufix (femb m))
  .

  Definition mfix := sigT range.

  Definition mfix_to_ufix (m:mfix): ufix := projT1 m.

  Lemma range_injective m:
    exists! m', Ufix (femb m') = mfix_to_ufix m.
  Proof.
    destruct m. destruct r. simplify.
    econstructor. econstructor; eauto.
    intros. inv H. eapply PositiveFunctor.INJECTIVE; eauto.
  Qed.

  Program Definition Mfix (m: PF mfix) : mfix :=
    @existT _ _ (Ufix (femb (fmap mfix_to_ufix m))) _.
  Next Obligation.
    constructor. intros. simplify.
    rewrite PositiveFunctor.NATURAL_MAP in X. inv X.
    unfold functor_mem in MEM. simplify.
    destruct (PositiveFunctor.embedding PF mfix m d) eqn:EQ; [|inv MEM].
    subst. destruct m0. auto.
  Qed.

  Definition mfix_des0 u (R:range u): PF ufix :=
    match R with
    | Range m _ => m
    end.

  Definition mfix_des1 u (R:range u) x (MEM: fmem (mfix_des0 R) x): mfix.
  Proof.
    econstructor. destruct R. simplify.
    eapply PositiveFunctor.NATURAL_MEM1 in MEM. simplify.
    apply MEM0. apply MEM.
  Defined.

  (* TODO: mfix_des *)

  Inductive ufix_ord: forall (x y:ufix), Prop :=
  | Ufix_ord x u (IN: fmem u x): ufix_ord x (Ufix u)
  .

  Lemma ufix_ord_wf: well_founded ufix_ord.
  Proof.
    unfold well_founded. fix 1. intro. destruct a.
    constructor. intros.
    inv H. inversion IN. simplify.
    destruct (u d).
    - specialize (ufix_ord_wf u0).
      rewrite MEM in ufix_ord_wf.
      apply ufix_ord_wf.
    - inv MEM.
  Defined.

  Inductive mfix_ord: forall (x y:mfix), Prop :=
  | Mfix_ord x y PX PY (ORD: ufix_ord x y): mfix_ord (@existT _ _ x PX) (@existT _ _ y PY)
  .

  Lemma mfix_ord_ufix_ord x y (ORD: mfix_ord x y):
    ufix_ord (mfix_to_ufix x) (mfix_to_ufix y).
  Proof.
    inv ORD. auto.
  Qed.
End MFix.


(* Instances *)

Program Definition id_positiveFunctorMixin :=
  @PositiveFunctor.Mixin
    id id_functorMixin.(Functor.map) id_pFunctorMixin.(PFunctor.mem) id_pFunctorMixin.(PFunctor.rel)
    () Empty_set
    (fun _ x _ => inl x)
    _ _ _ _ _.
Next Obligation.
  eapply fapp in EQ; [|apply ()]. inv EQ. auto.
Qed.
Next Obligation.
  econstructor; [apply ()|].
  econstructor.
Qed.
Next Obligation.
  inv X0. inv MEM. auto.
Qed.
Next Obligation.
  simplify. constructor; intros.
  - specialize (H ()). inv H. auto.
  - econstructor. auto.
Qed.
Canonical Structure id_positiveFunctorType := PositiveFunctorType _ id_positiveFunctorMixin.


Program Definition option_positiveFunctorMixin :=
  @PositiveFunctor.Mixin
    option option_functorMixin.(Functor.map) option_pFunctorMixin.(PFunctor.mem) option_pFunctorMixin.(PFunctor.rel)
    () ()
    (fun _ x _ =>
       match x with
       | Some x => inl x
       | None => inr ()
       end)
    _ _ _ _ _.
Next Obligation.
  destruct x1, x2; simplify; auto.
  - eapply fapp in EQ; [|apply ()]. inv EQ. auto.
  - eapply fapp in EQ; [|apply ()]. inv EQ.
  - eapply fapp in EQ; [|apply ()]. inv EQ.
Qed.
Next Obligation.
  destruct fx1; auto.
Qed.
Next Obligation.
  econstructor; [apply ()|].
  econstructor.
Qed.
Next Obligation.
  inv X0. destruct fx; simplify; inv MEM; auto.
Qed.
Next Obligation.
  destruct fx1, fx2; simplify; auto; constructor; intros;
    repeat (match goal with
            | [H: () -> _ |- _] => specialize (H ())
            | [H: option_frel _ _ _ |- _] => inv H
            | [H: coproduct_rel _ _ _ _ _ |- _] => inv H
            | [|- option_frel _ _ _] => econstructor
            | [|- coproduct_rel _ _ _ _ _] => econstructor
            end; auto).
  econstructor.
Qed.
Canonical Structure option_positiveFunctorType := PositiveFunctorType _ option_positiveFunctorMixin.
