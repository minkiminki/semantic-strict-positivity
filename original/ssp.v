Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.
Set Automatic Coercions Import.


(* Type Definitions *)

Module Functor.
  Record mixin_of (F: Type -> Type): Type := Mixin {
    map: forall T1 T2 (f: forall (x1:T1), T2) (y1:F T1), F T2;

    MAP_ID T:
      map (@id T) = id;
    MAP_COMPOSE T1 T2 T3
                (f12: forall (x1:T1), T2)
                (f23: forall (x2:T2), T3):
      (map f23) ∘ (map f12) = map (f23 ∘ f12);
  }.
  Notation class_of := mixin_of (only parsing).

  Structure type: Type := Pack {
    sort :> Type -> Type;
    _: class_of sort;
    _: Type -> Type;
  }.

  Definition class cF :=
    match cF return class_of cF with
    | @Pack _ c _ => c
    end.

  Definition unpack K (k: forall F (c : class_of F), K F c) cF :=
    match cF in type return K cF (class cF) with
    | Pack c _ => k _ c
    end.

  Definition pack F c := @Pack F c F.
End Functor.

Notation functorType := Functor.type.
Notation FunctorType := Functor.pack.
Definition functor_map F := Functor.map (Functor.class F).
Notation "'fmap' f" := (@functor_map _ _ _ f) (at level 0).


Section UniversalFunctor.
  Variable (Sh1 Sh2: Type).

  Definition UF T := Sh1 -> (T + Sh2).

  Definition UF_map T1 T2 (f: forall (x1:T1), T2) (y1:UF T1): UF T2 :=
    fun s1 =>
      match y1 s1 with
      | inl x => inl (f x)
      | inr s2 => inr s2
      end.

  Inductive UF_in T (F: UF T) x: Prop :=
  | UF_IN s1 (EQ: F s1 = inl x)
  .

  Program Definition UF_functorMixin :=
    @Functor.Mixin UF UF_map _ _.
  Next Obligation.
    apply functional_extensionality. intro y1.
    apply functional_extensionality. intro s1.
    unfold UF_map. destruct (y1 s1) eqn:EQ; auto.
  Qed.
  Next Obligation.
    apply functional_extensionality. intro y1.
    apply functional_extensionality. intro s1.
    unfold UF_map, compose. destruct (y1 s1) eqn:EQ1; auto.
  Qed.
End UniversalFunctor.


Module PositiveFunctor.
  Record mixin_of (F: Type -> Type): Type := Mixin {
    Sh1: Type;
    Sh2: Type;
    embedding: forall T (x: F T), UF Sh1 Sh2 T;

    INJECTIVE: forall T x1 x2 (EQ: @embedding T x1 = @embedding T x2), x1 = x2;
    NATURAL: False; (* FIXME: map_nat; natural transformation *)
  }.

  Record class_of (F: Type -> Type): Type := Class {
    base :> Functor.class_of F;
    ext :> mixin_of F;
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
    Functor.unpack _ k.

  Coercion functorType cF := Functor.Pack (class cF) cF.
End PositiveFunctor.

Notation positiveFunctorType := PositiveFunctor.type.
Notation PositiveFunctorType := PositiveFunctor.pack.
Canonical Structure PositiveFunctor.functorType.


(* FIXME: move *)
(** ** Less than or equal *)

Notation "p <0= q" :=
  (forall (PR: p : Prop), q : Prop)
  (at level 50, no associativity, only parsing).

Notation "p <1= q" :=
  (forall x0 (PR: p x0 : Prop), q x0 : Prop)
  (at level 50, no associativity).

Notation "p <2= q" :=
  (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop)
  (at level 50, no associativity).

Notation "p <3= q" :=
  (forall x0 x1 x2 (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop)
  (at level 50, no associativity).


Section MFix.
  Variable PF: positiveFunctorType.

  Inductive ufix: Type :=
  | Ufix: UF PF.(PositiveFunctor.Sh1) PF.(PositiveFunctor.Sh2) ufix -> ufix
  .

  Inductive range: forall (u:ufix), Prop :=
  | Range
      (m: PF ufix)
      (OnTL: UF_in (PF.(PositiveFunctor.embedding) _ m) <1= range):
      range (Ufix (PF.(PositiveFunctor.embedding) _ m))
  .

  Inductive mfix: Type :=
  | Mfix_ (m:ufix) (RANGE: range m)
  .

  Definition mfix_to_ufix (m:mfix) :=
    match m with @Mfix_ m _ => m end.

  Program Definition Mfix (m: PF mfix) : mfix :=
    @Mfix_ (Ufix (PF.(PositiveFunctor.embedding) _ (fmap mfix_to_ufix m))) _.
  Next Obligation.
    constructor. intros. inversion PR.
    (* rewrite SSPF.map_nat in EQ. *)
    (* unfold SPUF.map in EQ. *)
    (* destruct (SSPF.emb M Mfixpoint m s); inversion EQ. *)
    (* destruct m0. *)
    (* simpl. *)
    (* apply H. *)
  Admitted.

  Definition mfix_des (x:mfix): PF mfix.
  Proof.
    (* Mfix_destruct *)
  Admitted.

  Inductive ufix_order: forall (x y:ufix), Prop :=
  | Ufix_order x u (IN: UF_in u x): ufix_order x (Ufix u)
  .

  Lemma ufix_order_wf: well_founded ufix_order.
  Proof.
    unfold well_founded. fix 1. intro. destruct a.
    constructor. intros.
    inversion H. subst. inversion IN.
    destruct (u s1).
    - specialize (ufix_order_wf u0). inversion EQ.
      rewrite H1 in ufix_order_wf.
      apply ufix_order_wf.
    - inversion EQ.
  Defined.

  Inductive mfix_order: forall (x y:mfix), Prop :=
  | Mfix_order x y PX PY (ORD: ufix_order x y): mfix_order (@Mfix_ x PX) (@Mfix_ y PY)
  .

  Lemma mfix_order_ufix_order x y (ORD: mfix_order x y):
    ufix_order (mfix_to_ufix x) (mfix_to_ufix y).
  Proof.
    inversion ORD. auto.
  Qed.
End MFix.


(* Instances *)

(* FIXME: MOVE *)
Lemma fapp A B a
      (f g: A -> B) (EQ: f = g):
  f a = g a.
Proof.
  subst. auto.
Qed.

Program Definition id_functorMixin :=
  @Functor.Mixin id (fun _ _ => id) _ _.
Canonical Structure id_functorType := FunctorType id_functorMixin.

Program Definition id_positiveFunctorMixin :=
  @PositiveFunctor.Mixin id () Empty_set (fun _ x _ => inl x) _ _.
Next Obligation.
  eapply fapp in EQ; [|apply ()]. inversion EQ. auto.
Qed.
Next Obligation.
Admitted.
Canonical Structure id_positiveFunctorType := PositiveFunctorType _ id_positiveFunctorMixin.


Program Definition option_functorMixin :=
  @Functor.Mixin option option_map _ _.
Next Obligation.
  apply functional_extensionality. intro.
  destruct x; auto.
Qed.
Next Obligation.
  apply functional_extensionality. intro.
  destruct x; auto.
Qed.
Canonical Structure option_functorType := FunctorType option_functorMixin.

Program Definition option_positiveFunctorMixin :=
  @PositiveFunctor.Mixin
    option () ()
    (fun _ x _ =>
       match x with
       | Some x => inl x
       | None => inr ()
       end) _ _.
Next Obligation.
  destruct x1, x2; simpl in *; auto.
  - eapply fapp in EQ; [|apply ()]. inversion EQ. auto.
  - eapply fapp in EQ; [|apply ()]. inversion EQ.
  - eapply fapp in EQ; [|apply ()]. inversion EQ.
Qed.
Next Obligation.
Admitted.
Canonical Structure option_positiveFunctorType := PositiveFunctorType _ option_positiveFunctorMixin.


(* End *)
