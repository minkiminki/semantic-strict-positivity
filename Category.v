Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.
Set Automatic Coercions Import.


(* Tactics.  FIXME: move it! *)

Ltac inv H := inversion H; subst; clear H.
Ltac simplify := repeat (autounfold in *; simpl in *).


(* Categories *)

Module Functor.
  Definition TY := Type -> Type.

  Record mixin_of (F: Type -> Type): Type := Mixin {
    map: forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2;

    MAP_ID T:
      map (@id T) = id;
    MAP_COMPOSE T1 T2 T3
                (f12: forall (x1:T1), T2)
                (f23: forall (x2:T2), T3)
                x1:
      map f23 (map f12 x1) = map (f23 ∘ f12) x1;
    (* FIXME: ∘ and tactic doesn't interact well. *)
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
Hint Unfold functor_map.


Module NatTrans.
Section NatTrans.
  Variable (F G: functorType).

  Record mixin_of (NT: forall (X:Type) (fx:F X), G X): Type := Mixin {
    COMMUTE: forall T1 T2 (f:T1 -> T2), (NT _) ∘ (fmap f) = (fmap f) ∘ (NT _);
  }.

  Definition class_of := mixin_of.

  Structure type: Type := Pack {
    sort :> forall (X:Type) (fx:F X), G X;
    _: class_of sort;
    _: forall (X:Type) (fx:F X), G X;
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
End NatTrans.
End NatTrans.


Module PFunctor.
  Record mixin_of (F: Type -> Type) (F_map: forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2): Type := Mixin {
    mem: forall X, F X -> X -> Type;
    rel: forall X Y (rel: X -> Y -> Prop) (fx:F X) (fy:F Y), Prop;

    MEM: forall X Y (f: X -> Y) (fx: F X) (x: X)
           (MEM: mem fx x),
        mem (F_map _ _ f fx) (f x);
  }.

  Record class_of (F: Type -> Type): Type := Class {
    base :> Functor.class_of F;
    ext :> mixin_of F base.(Functor.map);
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
End PFunctor.

Notation pFunctorType := PFunctor.type.
Notation PFunctorType := PFunctor.pack.
Canonical Structure PFunctor.functorType.
Definition functor_mem F := PFunctor.mem (PFunctor.class F).
Definition functor_rel F := PFunctor.rel (PFunctor.class F).
Notation "'fmem' fx" := (@functor_mem _ _ fx) (at level 0).
Notation "'frel' rel" := (@functor_rel _ _ _ rel) (at level 0).
Hint Unfold functor_mem.
Hint Unfold functor_rel.


Module PNatTrans.
Section PNatTrans.
  Variable (F G: pFunctorType).

  Record mixin_of (NT: forall (X:Type) (fx:F X), G X): Type := Mixin {
    MEM1: forall X fx (x:X), fmem fx x -> fmem (NT _ fx) x;
    MEM2: forall X fx (x:X), fmem (NT _ fx) x -> fmem fx x;
    REL: forall T1 T2 (rel: forall (x1:T1) (x2:T2), Prop) fx1 fx2,
        frel rel fx1 fx2 <-> frel rel (NT _ fx1) (NT _ fx2);
  }.

  Record class_of (NT: forall (X:Type) (fx:F X), G X): Type := Class {
    base :> NatTrans.class_of F G NT;
    ext :> mixin_of NT;
  }.

  Structure type: Type := Pack {
    sort :> forall (X:Type) (fx:F X), G X;
    _: class_of sort;
    _: forall (X:Type) (fx:F X), G X;
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
End PNatTrans.
End PNatTrans.


(* Lemmas *)
(* FIXME: move *)

Lemma fapp A B a
      (f g: A -> B) (EQ: f = g):
  f a = g a.
Proof.
  subst. auto.
Qed.

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


(* Instances *)

Program Definition id_functorMixin :=
  @Functor.Mixin id (fun _ _ => id) _ _.
Canonical Structure id_functorType := FunctorType id_functorMixin.

Program Definition id_pFunctorMixin :=
  @PFunctor.Mixin
    id id_functorMixin.(Functor.map)
    (fun _ fx x => fx = x)
    (fun _ _ rel fx fy => rel fx fy)
    _.
Canonical Structure id_pFunctorType := PFunctorType _ id_pFunctorMixin.

Hint Unfold id.


Program Definition const_functorMixin T :=
  @Functor.Mixin (fun _ => T) (fun _ _ _ => id) _ _.
Canonical Structure const_functorType T := FunctorType (const_functorMixin T).

Program Definition const_pFunctorMixin T :=
  @PFunctor.Mixin
    (fun _ => T) (const_functorMixin T).(Functor.map)
    (fun _ _ _ => False)
    (fun _ _ _ => eq)
    _.
Program Canonical Structure const_pFunctorType (T:Type) := PFunctorType (FunctorType (const_functorMixin T)) (const_pFunctorMixin T).


Definition function_map D (F: functorType) T1 T2 (f: T1 -> T2) (fx1: D -> F T1) :=
  (fmap f) ∘ fx1.

Inductive function_mem D (F: pFunctorType) T (fx: D -> F T) x: Type :=
| Function_mem d (MEM: fmem (fx d) x)
.

Definition function_rel D (F: pFunctorType) T1 T2
           f (fx1:D -> F T1) (fx2:D -> F T2): Prop :=
  forall d, frel f (fx1 d) (fx2 d).

Program Definition function_functorMixin D (F: functorType) :=
  @Functor.Mixin (fun T => D -> F T) (@function_map _ _) _ _.
Next Obligation.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  unfold function_map, functor_map. rewrite Functor.MAP_ID. auto.
Qed.
Next Obligation.
  apply functional_extensionality. intro.
  unfold function_map, functor_map, compose. rewrite Functor.MAP_COMPOSE. auto.
Qed.
Canonical Structure function_functorType D F := FunctorType (function_functorMixin D F).

Program Definition function_pFunctorMixin D (F: pFunctorType) :=
  @PFunctor.Mixin (fun T => D -> F T) (@function_map _ _)
                  (@function_mem _ _) (@function_rel _ _) _.
Next Obligation.
  inversion MEM. econstructor.
  apply PFunctor.MEM. eauto.
Qed.
Canonical Structure function_pFunctorType D (F: pFunctorType) := PFunctorType (FunctorType (function_functorMixin D F)) (function_pFunctorMixin D F).

Hint Unfold function_map.
Hint Unfold function_rel.


Program Definition option_functorMixin :=
  @Functor.Mixin option option_map _ _.
Next Obligation.
  apply functional_extensionality. intro.
  destruct x; auto.
Qed.
Next Obligation.
  destruct x1; auto.
Qed.
Canonical Structure option_functorType := FunctorType option_functorMixin.

Inductive option_frel X Y (rel: forall (x:X) (y:Y), Prop):
  forall (fx:option X) (f:option Y), Prop :=
| option_frel_Some x y (REL: rel x y):
    option_frel rel (Some x) (Some y)
| option_frel_None:
    option_frel rel None None
.

Program Definition option_pFunctorMixin :=
  @PFunctor.Mixin
    option option_functorMixin.(Functor.map)
    (fun _ fx x => fx = Some x)
    option_frel
    _.
Canonical Structure option_pFunctorType := PFunctorType _ option_pFunctorMixin.


Definition coproduct_type (F1 F2: Type -> Type) T := (F1 T + F2 T)%type.

Definition coproduct_map (F1 F2: functorType) T1 T2 (f:T1 -> T2) (fx: F1 T1 + F2 T1) :=
  match fx with
  | inl fx => inl (fmap f fx)
  | inr fx => inr (fmap f fx)
  end.

Definition coproduct_mem (F1 F2: pFunctorType) T (fx:coproduct_type F1 F2 T) x :=
  match fx with
  | inl fx => fmem fx x
  | inr fx => fmem fx x
  end.

Inductive coproduct_rel (F1 F2: pFunctorType) T1 T2 f:
  forall (fx1:coproduct_type F1 F2 T1) (fx2:coproduct_type F1 F2 T2), Prop :=
| coproduct_rel_inl fx1 fx2 (REL: frel f fx1 fx2):
    coproduct_rel F1 F2 f (inl fx1) (inl fx2)
| coproduct_rel_inr fx1 fx2 (REL: frel f fx1 fx2):
    coproduct_rel F1 F2 f (inr fx1) (inr fx2)
.

Program Definition coproduct_functorMixin (F1 F2: functorType) :=
  @Functor.Mixin (coproduct_type F1 F2) (coproduct_map F1 F2) _ _.
Next Obligation.
  apply functional_extensionality. intro.
  destruct x; simpl.
  - unfold functor_map. rewrite ? Functor.MAP_ID. auto.
  - unfold functor_map. rewrite ? Functor.MAP_ID. auto.
Qed.
Next Obligation.
  destruct x1; simpl.
  - f_equal. apply Functor.MAP_COMPOSE.
  - f_equal. apply Functor.MAP_COMPOSE.
Qed.
Canonical Structure coproduct_functorType F1 F2 := FunctorType (coproduct_functorMixin F1 F2).

Program Definition coproduct_pFunctorMixin (F1 F2: pFunctorType) :=
  @PFunctor.Mixin (coproduct_type F1 F2) (coproduct_map F1 F2)
                  (@coproduct_mem F1 F2) (@coproduct_rel F1 F2) _.
Next Obligation.
  destruct fx; simpl in *.
  - apply PFunctor.MEM. auto.
  - apply PFunctor.MEM. auto.
Qed.
Canonical Structure coproduct_pFunctorType F1 F2 := PFunctorType _ (coproduct_pFunctorMixin F1 F2).

Hint Unfold coproduct_map.
Hint Unfold coproduct_mem.


Program Definition compose_functorMixin (F1 F2: functorType) :=
  @Functor.Mixin (F2 ∘ F1) (fun _ _ f => fmap (fmap f)) _ _.
Next Obligation.
  apply functional_extensionality. intro.
  unfold functor_map. rewrite ? Functor.MAP_ID. auto.
Qed.
Next Obligation.
Admitted.
Canonical Structure compose_functorType F1 F2 := FunctorType (compose_functorMixin F1 F2).

Program Definition compose_pFunctorMixin (F1 F2: pFunctorType) :=
  @PFunctor.Mixin
    (F2 ∘ F1) (compose_functorMixin F1 F2).(Functor.map)
    _
    _
    _.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Canonical Structure compose_pFunctorType F1 F2 := PFunctorType _ (compose_pFunctorMixin F1 F2).
