Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.
Set Automatic Coercions Import.


(* Tactics.  FIXME: move it! *)

Ltac inv H := inversion H; subst; clear H.
Ltac simplify := repeat (autounfold in *; simpl in *).

Lemma drop_id X (x: X) : id x = x.
Proof. auto. Qed.

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
Notation "'fmap' f" := (@Functor.map _ (Functor.class _) _ _ f) (at level 0).


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


Module SFunctor.
  Record mixin_of (F: Type -> Type) (F_map: forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2): Type := Mixin {
    mem: forall X, F X -> X -> Prop;
    map_dep: forall X Y (fx:F X) (f: forall x (MEM:mem fx x), Y), F Y;
    rel: forall X Y (rel: X -> Y -> Prop) (fx:F X) (fy:F Y), Prop;

    MEM: forall X Y (f: X -> Y) (fx: F X) (x: X) (MEM: mem fx x), mem (F_map _ _ f fx) (f x);
    MAP_DEP: forall X Y fx (f: forall x (MEM:mem fx x), Y) (g: Y -> X) (INV: forall x r, g (f x r) = x), F_map _ _ g (@map_dep _ _ fx f) = fx
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
End SFunctor.

Notation sFunctorType := SFunctor.type.
Notation SFunctorType := SFunctor.pack.
Canonical Structure SFunctor.functorType.
Notation "'fmem' fx" := (@SFunctor.mem _ _ (SFunctor.ext (SFunctor.class _)) _ fx) (at level 0).
Notation "'fmap_dep' fx" := (@SFunctor.map_dep _ _ (SFunctor.ext (SFunctor.class _)) _ _ fx) (at level 0).
Notation "'frel' rel" := (@SFunctor.rel _ _ (SFunctor.ext (SFunctor.class _)) _ _ rel) (at level 0).


Module SNatTrans.
Section SNatTrans.
  Variable (F G: sFunctorType).

  Record mixin_of (NT: forall (X:Type) (fx:F X), G X): Type := Mixin {
    MEM: forall X fx (x:X), fmem fx x <-> fmem (NT _ fx) x;
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
End SNatTrans.
End SNatTrans.


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

Program Definition id_sFunctorMixin :=
  @SFunctor.Mixin
    id id_functorMixin.(Functor.map)
    (fun _ fx x => fx = x)
    (fun _ _ fx FX => FX _ eq_refl)
    (fun _ _ rel fx fy => rel fx fy)
    _ _.
Canonical Structure id_sFunctorType := SFunctorType _ id_sFunctorMixin.

Hint Unfold id.


Program Definition const_functorMixin T :=
  @Functor.Mixin (fun _ => T) (fun _ _ _ => id) _ _.
Canonical Structure const_functorType T := FunctorType (const_functorMixin T).

Program Definition const_sFunctorMixin T :=
  @SFunctor.Mixin
    (fun _ => T) (const_functorMixin T).(Functor.map)
    (fun _ _ _ => False)
    (fun _ _ fx _ => fx)
    (fun _ _ _ => eq)
    _ _.
Program Canonical Structure const_sFunctorType (T:Type) := SFunctorType (FunctorType (const_functorMixin T)) (const_sFunctorMixin T).


Definition function_map D (F: functorType) T1 T2 (f: T1 -> T2) (fx1: D -> F T1) :=
  (fmap f) ∘ fx1.

Inductive function_mem D (F: sFunctorType) T (fx: D -> F T) x: Prop :=
| Function_mem d (MEM: fmem (fx d) x)
.

Program Definition function_map_dep D (F: sFunctorType) T1 T2 (fx1: D -> F T1) (f: forall (x1:T1) (MEM: function_mem F fx1 x1), T2): D -> F T2 :=
  fun X => fmap_dep (fx1 X) (fun x MEM => (f x _)).
Next Obligation.
  econstructor. eauto.
Qed.

Definition function_rel D (F: sFunctorType) T1 T2
           f (fx1:D -> F T1) (fx2:D -> F T2): Prop :=
  forall d, frel f (fx1 d) (fx2 d).

Hint Unfold function_map.
Hint Unfold function_map_dep.
Hint Unfold function_rel.

Program Definition function_functorMixin D (F: functorType) :=
  @Functor.Mixin (fun T => D -> F T) (@function_map _ _) _ _.
Next Obligation.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  simplify. rewrite Functor.MAP_ID. auto.
Qed.
Next Obligation.
  apply functional_extensionality. intro.
  simplify. unfold compose. rewrite Functor.MAP_COMPOSE. auto.
Qed.
Canonical Structure function_functorType D F := FunctorType (function_functorMixin D F).

Program Definition function_sFunctorMixin D (F: sFunctorType) :=
  @SFunctor.Mixin (fun T => D -> F T) (@function_map _ _)
                  (@function_mem _ _) (@function_map_dep _ _) (@function_rel _ _) _ _.
Next Obligation.
  inversion MEM. econstructor.
  apply SFunctor.MEM. eauto.
Qed.
Next Obligation.
  simplify. extensionality s.
  apply SFunctor.MAP_DEP.
  intros. apply INV.
Qed.
Canonical Structure function_sFunctorType D (F: sFunctorType) := SFunctorType (FunctorType (function_functorMixin D F)) (function_sFunctorMixin D F).


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

Program Definition option_sFunctorMixin :=
  @SFunctor.Mixin
    option option_functorMixin.(Functor.map)
    (fun _ fx x => fx = Some x)
    (fun _ _ fx FX => match fx with | Some fx => Some (FX fx eq_refl) | None => None end)
    option_frel
    _ _.
Next Obligation.
  destruct fx; auto.
  simpl. f_equal. apply INV.
Qed.
Canonical Structure option_sFunctorType := SFunctorType _ option_sFunctorMixin.


Definition coproduct_type (F1 F2: Type -> Type) T := (F1 T + F2 T)%type.

Definition coproduct_map (F1 F2: functorType) T1 T2 (f:T1 -> T2) (fx: F1 T1 + F2 T1) :=
  match fx with
  | inl fx => inl (fmap f fx)
  | inr fx => inr (fmap f fx)
  end.

Definition coproduct_mem (F1 F2: sFunctorType) T (fx:coproduct_type F1 F2 T) x :=
  match fx with
  | inl fx => fmem fx x
  | inr fx => fmem fx x
  end.

Inductive coproduct_rel (F1 F2: sFunctorType) T1 T2 f:
  forall (fx1:coproduct_type F1 F2 T1) (fx2:coproduct_type F1 F2 T2), Prop :=
| coproduct_rel_inl fx1 fx2 (REL: frel f fx1 fx2):
    coproduct_rel F1 F2 f (inl fx1) (inl fx2)
| coproduct_rel_inr fx1 fx2 (REL: frel f fx1 fx2):
    coproduct_rel F1 F2 f (inr fx1) (inr fx2)
.

Hint Unfold coproduct_map.
Hint Unfold coproduct_mem.

Program Definition coproduct_functorMixin (F1 F2: functorType) :=
  @Functor.Mixin (coproduct_type F1 F2) (coproduct_map F1 F2) _ _.
Next Obligation.
  apply functional_extensionality. intro.
  destruct x; simpl;
  rewrite Functor.MAP_ID; auto.
Qed.
Next Obligation.
  destruct x1; simpl.
  - f_equal. apply Functor.MAP_COMPOSE.
  - f_equal. apply Functor.MAP_COMPOSE.
Qed.
Canonical Structure coproduct_functorType F1 F2 := FunctorType (coproduct_functorMixin F1 F2).

Program Definition coproduct_sFunctorMixin (F1 F2: sFunctorType) :=
  @SFunctor.Mixin (coproduct_type F1 F2) (coproduct_map F1 F2)
                  (@coproduct_mem F1 F2) (fun _ _ _ _ => _) (@coproduct_rel F1 F2) _ _.
Next Obligation.
  destruct H1.
  - apply (inl (F1.(SFunctor.map_dep) s H2)).
  - apply (inr (F2.(SFunctor.map_dep) s H2)).
Defined.
Next Obligation.
  destruct fx; simpl in *.
  - apply SFunctor.MEM. auto.
  - apply SFunctor.MEM. auto.
Qed.
Next Obligation.
  destruct fx; simplify; f_equal;
  apply SFunctor.MAP_DEP; auto.
Qed.
Canonical Structure coproduct_sFunctorType F1 F2 := SFunctorType _ (coproduct_sFunctorMixin F1 F2).


Definition product_type (F1 F2: Type -> Type) T := (F1 T * F2 T)%type.

Definition product_map (F1 F2: functorType) T1 T2 (f:T1 -> T2) (fx: F1 T1 * F2 T1) :=
  match fx with
  | (f1x, f2x) => (fmap f f1x, fmap f f2x)
  end.

Definition product_mem (F1 F2: sFunctorType) T (fx:product_type F1 F2 T) x :=
  match fx with
  | (f1x, f2x) => (fmem f1x x) \/ (fmem f2x x)
  end.

Definition product_rel (F1 F2: sFunctorType) T1 T2 f
           (fx1:product_type F1 F2 T1) (fx2:product_type F1 F2 T2) : Prop :=
  match fx1, fx2 with
  | (f1x1, f2x1), (f1x2, f2x2) => (frel f f1x1 f1x2) /\ (frel f f2x1 f2x2) 
  end.

Hint Unfold product_map.
Hint Unfold product_mem.

Program Definition product_functorMixin (F1 F2: functorType) :=
  @Functor.Mixin (product_type F1 F2) (product_map F1 F2) _ _.
Next Obligation.
  apply functional_extensionality. intro.
  destruct x; simpl.
  rewrite ? Functor.MAP_ID. auto.
Qed.
Next Obligation.
  destruct x1; simpl.
  f_equal; apply Functor.MAP_COMPOSE.
Qed.
Canonical Structure product_functorType F1 F2 := FunctorType (product_functorMixin F1 F2).

Program Definition product_sFunctorMixin (F1 F2: sFunctorType) :=
  @SFunctor.Mixin (product_type F1 F2) (product_map F1 F2)
                  (@product_mem F1 F2) (fun _ _ _ _ => _) (@product_rel F1 F2) _ _.
Next Obligation.
  destruct H1.
  apply (F1.(SFunctor.map_dep) s (fun x r => H2 _ (or_introl r)),
        F2.(SFunctor.map_dep) s0 (fun x r => H2 _ (or_intror r))).
Defined.
Next Obligation.
  destruct fx; simpl in *.
  destruct MEM; [left | right];
  apply SFunctor.MEM; auto.
Qed.
Next Obligation.
  destruct fx. simplify. f_equal;
  apply SFunctor.MAP_DEP; auto.
Qed.
Canonical Structure product_sFunctorType F1 F2 := SFunctorType _ (product_sFunctorMixin F1 F2).

Program Definition compose_functorMixin (F1 F2: functorType) :=
  @Functor.Mixin (F2 ∘ F1) (fun _ _ f => fmap (fmap f)) _ _.
Next Obligation.
  apply functional_extensionality. intro.
  rewrite ? Functor.MAP_ID. auto.
Qed.
Next Obligation.
  repeat rewrite Functor.MAP_COMPOSE.
  f_equal. extensionality s. apply Functor.MAP_COMPOSE.
Qed.
Canonical Structure compose_functorType F1 F2 := FunctorType (compose_functorMixin F1 F2).

Inductive comp_mem (F1 F2: sFunctorType) X : F2 (F1 X) -> X -> Prop :=
| _comp_mem x gx fgx (HG : F1.(SFunctor.mem) gx x) (HF : F2.(SFunctor.mem) fgx gx) :
    comp_mem F1 F2 fgx x.

Definition comp_rel (F1 F2: sFunctorType) X Y (RE: X -> Y -> Prop) : F2 (F1 X) -> F2 (F1 Y) -> Prop
  := F2.(SFunctor.rel) (F1.(SFunctor.rel) RE).

Hint Unfold comp_rel.

Program Definition compose_sFunctorMixin (F1 F2: sFunctorType) :=
  @SFunctor.Mixin
    (F2 ∘ F1) (compose_functorMixin F1 F2).(Functor.map)
    (@comp_mem F1 F2) _ (@comp_rel F1 F2) _ _.
Next Obligation.
  apply (F2.(SFunctor.map_dep)
              fx (fun y r1 => (F1.(SFunctor.map_dep) y (fun z r2 => f _ (_comp_mem F1 F2 _ _ _ r2 r1))))).
Defined.
Next Obligation.
  inv MEM. eapply _comp_mem.
  apply (SFunctor.MEM _ f _ _ HG). 
  apply (SFunctor.MEM _ (Functor.map F1 f) _ _ HF).
Qed.
Next Obligation.
  apply F2.(SFunctor.MAP_DEP).
  intros. apply SFunctor.MAP_DEP. auto.
Qed.
Canonical Structure compose_sFunctorType F1 F2 := SFunctorType _ (compose_sFunctorMixin F1 F2).


Definition dep_prod_type A (B: A -> Type -> Type) X := (forall a: A, B a X).

Definition dep_prod_map A (B: A -> functorType) X Y (f: X-> Y)
           (x : forall a: A, B a X) : (forall a: A, B a Y) :=
  fun (a: A) => fmap f (x a).

Definition dep_prod_mem A (B: A -> sFunctorType) X (fx: dep_prod_type B X) x :=
  exists (a: A), fmem (fx a) x.

Definition dep_prod_rel A (B: A -> sFunctorType) X Y (RE: X -> Y -> Prop)
           (fx: dep_prod_type B X) (fy: dep_prod_type B Y) : Prop :=
  forall a : A, frel RE (fx a) (fy a).

Program Definition dep_prod_functorMixin A (B: A -> functorType) := 
  @Functor.Mixin (dep_prod_type B) (dep_prod_map B) _ _.
Next Obligation.
  unfold dep_prod_map.
  extensionality s. extensionality a.
  rewrite ? Functor.MAP_ID. auto.
Qed.
Next Obligation.
  unfold dep_prod_map.
  extensionality s.
  eapply Functor.MAP_COMPOSE.
Qed.
Canonical Structure dep_prod_functorType A (B: A -> functorType) := FunctorType (dep_prod_functorMixin B).

Program Definition dep_prod_sFunctorMixin A (B: A -> sFunctorType) :=
  @SFunctor.Mixin (dep_prod_type B) (dep_prod_map B)
                  (dep_prod_mem B) (fun _ _ _ _ => _) (dep_prod_rel B) _ _.
Next Obligation.
  intro.
  apply ((B a).(SFunctor.map_dep) (H1 a) 
      (fun y r => H2 y (ex_intro (fun a => (B a).(SFunctor.mem) (H1 a) y) _ r))).
Defined.
Next Obligation.
  inv MEM.
  exists x0. unfold dep_prod_map.
  apply (SFunctor.MEM _ f _ _ H).
Qed.
Next Obligation.
  unfold dep_prod_map. extensionality a.
  apply SFunctor.MAP_DEP. eauto.
Qed.
Canonical Structure dep_prod_sFunctorType A (B: A -> sFunctorType) := SFunctorType _ (dep_prod_sFunctorMixin B).


Definition dep_sum_type A (B: A -> Type -> Type) X := sigT (fun a => B a X).

Definition dep_sum_map A (B: A -> functorType) X Y (f: X-> Y)
           (fx : dep_sum_type B X) : dep_sum_type B Y :=
  match fx with
  | existT _ a fx' => existT _ a (fmap f fx') end. 

Definition dep_sum_mem A (B: A -> sFunctorType) X (fx: dep_sum_type B X) x :=
  match fx with
  | existT _ a fx => fmem fx x end. 

Inductive dep_sum_rel A (B: A -> sFunctorType) X Y (RE: X -> Y -> Prop) :
  dep_sum_type B X -> dep_sum_type B Y -> Prop :=
| _dep_sum_rel a (x: B a X) (y: B a Y)(r: frel RE x y)
  : dep_sum_rel B RE (existT _ a x) (existT _ a y).

Program Definition dep_sum_functorMixin A (B: A -> functorType) := 
  @Functor.Mixin (dep_sum_type B) (dep_sum_map B) _ _.
Next Obligation.
  extensionality x. destruct x.
  simplify. f_equal.
  rewrite ? Functor.MAP_ID. auto.
Qed.
Next Obligation.
  destruct x1. simplify. f_equal.
  apply Functor.MAP_COMPOSE.
Qed.
Canonical Structure dep_sum_functorType A (B: A -> functorType) := FunctorType (dep_sum_functorMixin B).

Program Definition dep_sum_sFunctorMixin A (B: A -> sFunctorType) :=
  @SFunctor.Mixin (dep_sum_type B) (dep_sum_map B)
                  (dep_sum_mem B) (fun _ _ _ _ => _) (dep_sum_rel B) _ _.
Next Obligation.
  destruct H1.
  apply (existT _ x ((B x).(SFunctor.map_dep) s (fun x0 r => H2 _ r))).
Defined.
Next Obligation.
  destruct fx. simplify.
  apply SFunctor.MEM. auto.
Qed.
Next Obligation.
  destruct fx. simplify. f_equal.
  apply SFunctor.MAP_DEP. auto.
Qed.
Canonical Structure dep_sum_sFunctorType A (B: A -> sFunctorType) := SFunctorType _ (dep_sum_sFunctorMixin B).
