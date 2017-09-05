Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.
Set Automatic Coercions Import.


(* Tactics.  FIXME: move it! *)

Ltac inv H := inversion H; subst; clear H.
Ltac simplify := repeat (autounfold in *; unfold id in *; simpl in *).

(* Categories *)

Structure FunctorData (F : Type -> Type) : Type
  := { map: forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2; }.

Structure FunctorProp F (Fn : FunctorData F) : Prop
  := {
      MAP_ID T:
        Fn.(map) (@id T) = id;
      MAP_COMPOSE T1 T2 T3
                  (f12: forall (x1:T1), T2)
                  (f23: forall (x2:T2), T3)
                  x1:
        Fn.(map) f23 (Fn.(map) f12 x1) = Fn.(map) (f23 ∘ f12) x1;
    }.

Structure SFunctorData (F : Type -> Type) : Type
  := {
      Fn :> FunctorData F;
      mem: forall X, F X -> X -> Prop;
      map_dep: forall X Y (fx:F X) (f: forall x (MEM:mem fx x), Y), F Y;
      rel: forall X Y (rel: X -> Y -> Prop) (fx:F X) (fy:F Y), Prop;
      MAP_DEP: forall X Y fx (f: forall x (MEM:mem fx x), Y) (g: Y -> X) (INV: forall x r, g (f x r) = x), Fn.(map) g (map_dep f) = fx;
    }.

Structure SFunctorProp F (Fn : SFunctorData F)
  : Prop
  := {
      MAP_MEM: forall X Y (f: X -> Y) (fx: F X) (x: X) (MEM: Fn.(mem) fx x), Fn.(mem) (Fn.(map) f fx) (f x);
    }.

Structure NatTrans (F G : Type -> Type) (FnF : FunctorData F) `(FnG : FunctorData G) : Type :=
  {
    NT :> forall {X:Type} (fx:F X), G X;
    MAP_COMMUTE: forall T1 T2 (f:T1 -> T2) x, NT (FnF.(map) f x) = (FnG.(map) f) (NT x);
  }.

Structure SNatTransProp F G (FnF : SFunctorData F) (FnG : SFunctorData G) (N : NatTrans FnF FnG)
  : Prop := {
             MEM_COMMUTE: forall X fx (x:X), FnF.(mem) fx x <-> FnG.(mem) (N _ fx) x;
             REL_COMMUTE: forall T1 T2 (rel': forall (x1:T1) (x2:T2), Prop) fx1 fx2,
                 FnF.(rel) rel' fx1 fx2 <-> FnG.(rel) rel' (N _ fx1) (N _ fx2);
           }.

(* instances *)

Definition Ident (X : Type) := X.

Definition id_functorData : FunctorData Ident := Build_FunctorData _ (fun _ _ => id).

Program Definition id_sFunctorData : SFunctorData Ident
  := Build_SFunctorData id_functorData
                        (fun _ fx x => fx = x)
                        (fun _ _ fx FX => FX _ eq_refl)
                        (fun _ _ rel fx fy => rel fx fy) _.

Hint Resolve id_functorData id_sFunctorData.

Definition Const (T : Type) (X : Type) := T.

Definition const_functorData T : FunctorData (Const T)
  := Build_FunctorData (fun X => T) (fun _ _ _ x => x).

Program Definition const_sFunctorData T : SFunctorData (Const T)
  := Build_SFunctorData (const_functorData T)
                        (fun _ _ _ => False)
                        (fun _ _ fx _ => fx)
                        (fun _ _ _ => eq) _.

Hint Resolve const_functorData const_sFunctorData.


Definition Expn (D : Type) (F : Type -> Type) := (fun X => D -> F X).

Definition function_map D F (Fn : FunctorData F) T1 T2 (f: T1 -> T2)
           (fx1: D -> F T1) :=
  (Fn.(map) f) ∘ fx1.
Hint Unfold function_map.

Inductive function_mem D F (Fn : SFunctorData F) T (fx: D -> F T) x: Prop :=
| Function_mem d (MEM: Fn.(mem) (fx d) x).
Hint Constructors function_mem.

Program Definition function_map_dep D F (Fn : SFunctorData F) T1 T2 (fx1: D -> F T1)
        (f: forall (x1:T1) (MEM: function_mem Fn fx1 x1), T2): D -> F T2 :=
  fun X => Fn.(map_dep) (fx1 X) (fun x MEM => (f x _)).
Next Obligation.
  econstructor. eauto.
Defined.

Definition function_rel D F (Fn : SFunctorData F) T1 T2
           f (fx1:D -> F T1) (fx2:D -> F T2): Prop :=
  forall d, Fn.(rel) f (fx1 d) (fx2 d).
Hint Unfold function_rel.

Definition function_functorData D F (Fn : FunctorData F)
  : FunctorData (Expn D F) := Build_FunctorData _ (function_map Fn).

Program Definition function_sFunctorData D F (Fn : SFunctorData F)
  : SFunctorData (Expn D F)
  := Build_SFunctorData (function_functorData D Fn)
                        (@function_mem _ _ _)
                        (@function_map_dep _ _ _)
                        (@function_rel _ _ _) _.
Next Obligation.
  extensionality s. apply MAP_DEP. auto.
Qed.

Hint Resolve function_functorData function_sFunctorData.


Definition Coprod (F1 F2: Type -> Type) T := (F1 T + F2 T)%type.

Definition coproduct_map F1 F2 (Fn1 : FunctorData F1) (Fn2 : FunctorData F2) T1 T2
           (f:T1 -> T2) (fx: F1 T1 + F2 T1) :=
  match fx with
  | inl fx => inl (Fn1.(map) f fx)
  | inr fx => inr (Fn2.(map) f fx)
  end.

Hint Unfold coproduct_map.

Definition coproduct_mem F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2) T
           (fx: F1 T + F2 T) x :=
  match fx with
  | inl fx => Fn1.(mem) fx x
  | inr fx => Fn2.(mem) fx x
  end.

Hint Unfold coproduct_mem.

Inductive coproduct_rel F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2) T1 T2 r:
  forall (fx1:Coprod F1 F2 T1) (fx2:Coprod F1 F2 T2), Prop :=
| coproduct_rel_inl fx1 fx2 (REL: Fn1.(rel) r fx1 fx2):
    coproduct_rel Fn1 Fn2 r (inl fx1) (inl fx2)
| coproduct_rel_inr fx1 fx2 (REL: Fn2.(rel) r fx1 fx2):
    coproduct_rel Fn1 Fn2 r (inr fx1) (inr fx2)
.

Hint Constructors coproduct_rel.

Program Definition coproduct_functorData  F1 F2 (Fn1 : FunctorData F1) (Fn2 : FunctorData F2)
  : FunctorData (Coprod F1 F2)
  := Build_FunctorData _ (@coproduct_map _ _ _ _).

Program Definition coproduct_sFunctorData F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2)
  : SFunctorData (Coprod F1 F2)
  := Build_SFunctorData (coproduct_functorData Fn1 Fn2)
                        (@coproduct_mem _ _ _ _)
                        _
                        (@coproduct_rel _ _ _ _) _.
Next Obligation.
  destruct fx. 
  - apply (inl (Fn1.(map_dep) f0 f)).
  - apply (inr (Fn2.(map_dep) f0 f)).
Defined.
Next Obligation.
  destruct fx; simplify; f_equal; apply MAP_DEP; auto. 
Qed.

Hint Resolve coproduct_functorData coproduct_sFunctorData.
