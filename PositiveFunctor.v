Require Import FunctionalExtensionality.
Require Import Program.

Require Import Category.

Set Implicit Arguments.
Set Automatic Coercions Import.


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
  Program Record mixin_of (F: Type -> Type) (F_map:forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2): Type := Mixin {
    Sh1: Type;
    Sh2: Type;
    embedding: forall T (x: F T), UF Sh1 Sh2 T;

    INJECTIVE: forall T x1 x2 (EQ: @embedding T x1 = @embedding T x2), x1 = x2;
    NATURAL:
      forall T1 T2 (f: T1 -> T2) fx1,
        embedding (F_map _ _ f fx1) = fmap f (embedding fx1);
  }.

  Record class_of (F: Type -> Type): Type := Class {
    base :> PFunctor.class_of F;
    ext :> mixin_of F base.(PFunctor.base).(Functor.map);
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


(* Theory *)

Section MFix.
  Variable PF: positiveFunctorType.

  Inductive ufix: Type :=
  | Ufix: UF PF.(PositiveFunctor.Sh1) PF.(PositiveFunctor.Sh2) ufix -> ufix
  .

  Inductive range: forall (u:ufix), Prop :=
  | Range
      (m: PF ufix)
      (OnTL: fmem (femb m) <1= range):
      range (Ufix (femb m))
  .

  Definition mfix := sig range.

  Definition mfix_to_ufix (m:mfix): ufix := proj1_sig m.

  (* FIXME: move *)

  Program Definition Mfix (m: PF mfix) : mfix :=
    @exist _ _ (Ufix (femb (fmap mfix_to_ufix m))) _.
  Next Obligation.
    constructor. intros. inv PR.
    repeat (autounfold in *; simpl in *).
    rewrite PositiveFunctor.NATURAL in MEM.
    repeat (autounfold in *; simpl in *).
    destruct (PositiveFunctor.embedding PF mfix m d) eqn:EQ; [|inv MEM].
    subst. destruct m0. auto.
  Qed.

  (* Definition mfix_des (x: mfix) : PF mfix := *)
  (*   (proj2_sig x). *)

  (* Definition ufix_des (m: ufix) (R: range m) : PF ufix := *)
  (*   match R with *)
  (*   | Range m _ => m *)
  (*   end. *)
  
  Inductive ufix_order: forall (x y:ufix), Prop :=
  | Ufix_order x u (IN: fmem u x): ufix_order x (Ufix u)
  .

  Lemma ufix_order_wf: well_founded ufix_order.
  Proof.
    unfold well_founded. fix 1. intro. destruct a.
    constructor. intros.
    inv H. inversion IN.
    repeat (autounfold in *; simpl in *).
    destruct (u d).
    - specialize (ufix_order_wf u0).
      rewrite MEM in ufix_order_wf.
      apply ufix_order_wf.
    - inv MEM.
  Defined.

  Inductive mfix_order: forall (x y:mfix), Prop :=
  | Mfix_order x y PX PY (ORD: ufix_order x y): mfix_order (@exist _ _ x PX) (@exist _ _ y PY)
  .

  Lemma mfix_order_ufix_order x y (ORD: mfix_order x y):
    ufix_order (mfix_to_ufix x) (mfix_to_ufix y).
  Proof.
    inv ORD. auto.
  Qed.
End MFix.


(* Instances *)

Program Definition id_positiveFunctorMixin :=
  @PositiveFunctor.Mixin
    id id_functorMixin.(Functor.map)
    () Empty_set
    (fun _ x _ => inl x)
    _ _.
Next Obligation.
  eapply fapp in EQ; [|apply ()]. inv EQ. auto.
Qed.
Canonical Structure id_positiveFunctorType := PositiveFunctorType _ id_positiveFunctorMixin.


Program Definition option_positiveFunctorMixin :=
  @PositiveFunctor.Mixin
    option option_functorMixin.(Functor.map)
    () ()
    (fun _ x _ =>
       match x with
       | Some x => inl x
       | None => inr ()
       end)
    _ _.
Next Obligation.
  destruct x1, x2; simpl in *; auto.
  - eapply fapp in EQ; [|apply ()]. inv EQ. auto.
  - eapply fapp in EQ; [|apply ()]. inv EQ.
  - eapply fapp in EQ; [|apply ()]. inv EQ.
Qed.
Next Obligation.
  destruct fx1; auto.
Qed.
Canonical Structure option_positiveFunctorType := PositiveFunctorType _ option_positiveFunctorMixin.
