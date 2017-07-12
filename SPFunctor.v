Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.

Require Import Functor.

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
   Definition UF_sFunctorMixin: SFunctor.mixin_of UF UF_functorMixin.(Functor.map) :=
     function_sFunctorMixin Sh1 (coproduct_sFunctorType id_sFunctorType (const_sFunctorType Sh2)).
End UniversalFunctor.

Canonical Structure UF_FunctorType Sh1 Sh2 := FunctorType (UF_functorMixin Sh1 Sh2).
Canonical Structure UF_SFunctorType Sh1 Sh2 := SFunctorType (UF_FunctorType Sh1 Sh2) (UF_sFunctorMixin Sh1 Sh2).
Hint Unfold UF_FunctorType.
Hint Unfold UF_SFunctorType.


Module SPFunctor.
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


(* Fixpoint *)

Section FFix.
  Variable PF: SPFunctorType.

  Inductive ufix: Type :=
  | Ufix: UF PF.(SPFunctor.Sh1) PF.(SPFunctor.Sh2) ufix -> ufix
  .

  Inductive range: forall (u:ufix), Type :=
  | Range
      (m: PF ufix)
      (MEM: forall u, fmem (femb m) u -> range u):
      range (Ufix (femb m))
  .

  Definition ffix := sigT range.

  Definition ffix_to_ufix (x:ffix): ufix := projT1 x.

  Lemma range_injective x:
    exists! x', Ufix (femb x') = ffix_to_ufix x.
  Proof.
    destruct x. destruct r. simplify.
    econstructor. econstructor; eauto.
    intros. inv H. eapply SPFunctor.INJECTIVE; eauto.
  Qed.

  Program Definition Ffix (x: PF ffix) : ffix :=
    @existT _ _ (Ufix (femb (fmap ffix_to_ufix x))) _.
  Next Obligation.
    constructor. intros. simplify.
    rewrite SPFunctor.NATURAL_MAP in X. inv X. simplify.
    destruct (SPFunctor.embedding PF ffix x d) eqn:EQ; [|inv MEM].
    subst. destruct f. auto.
  Qed.

  Definition ffix_des0 u (R:range u): PF ufix :=
    match R with
    | Range m _ => m
    end.

  Definition ffix_des1 u (R:range u) x (MEM: fmem (ffix_des0 R) x): ffix.
  Proof.
    econstructor. destruct R. simplify.
    eapply SPFunctor.NATURAL_MEM1 in MEM. simplify.
    apply MEM0. apply MEM.
  Defined.

  Program Definition ffix_des (f:ffix): PF ffix :=
    fmap_dep _ (ffix_des1 (projT2 f)).

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

  Inductive ffix_ord: forall (x y:ffix), Prop :=
  | Ffix_ord x y PX PY (ORD: ufix_ord x y): ffix_ord (@existT _ _ x PX) (@existT _ _ y PY)
  .

  Lemma ffix_ord_ufix_ord x y (ORD: ffix_ord x y):
    ufix_ord (ffix_to_ufix x) (ffix_to_ufix y).
  Proof.
    inv ORD. auto.
  Qed.

  Lemma acc_preserve X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
        (H: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2))
        (WF: well_founded Ry) y
    : forall x, y = f x /\ Acc Ry y -> Acc Rx x.
  Proof.
    apply (@Fix Y Ry WF (fun a =>  forall x : X, a = f x /\ Acc Ry a -> Acc Rx x)).
    intros. destruct H1. subst.
    constructor. intros. eauto.
  Qed.

  Lemma sub_wellorder X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
        (H: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2)) (WF: well_founded Ry) 
    : well_founded Rx.
  Proof.
    unfold well_founded. intros. apply (@acc_preserve _ _ f Rx _ H WF (f a)). auto.
  Qed.

  Lemma ffix_ord_wf: well_founded ffix_ord.
  Proof.
    apply (sub_wellorder _ _ ffix_ord_ufix_ord ufix_ord_wf).
  Qed.

  Lemma ffix_induction
        (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord x y -> P x) -> P y)
        x:
    P x.
  Proof.
    apply (Fix ffix_ord_wf). apply STEP.
  Qed.
End FFix.


(* Instances *)

Program Definition id_SPFunctorMixin :=
  @SPFunctor.Mixin
    id id_functorMixin.(Functor.map) id_sFunctorMixin.(SFunctor.mem) id_sFunctorMixin.(SFunctor.rel)
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
Canonical Structure id_SPFunctorType := spFunctorType _ id_SPFunctorMixin.


Program Definition option_SPFunctorMixin :=
  @SPFunctor.Mixin
    option option_functorMixin.(Functor.map) option_sFunctorMixin.(SFunctor.mem) option_sFunctorMixin.(SFunctor.rel)
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
Canonical Structure option_SPFunctorType := spFunctorType _ option_SPFunctorMixin.
