Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.


(* Tactics.  FIXME: move it! *)

Ltac inv H := inversion H; subst; clear H.
Ltac simplify := repeat (autounfold in *; unfold id in *; simpl in *).

(* Categories *)

Class FunctorData (F : Type -> Type) : Type
  := { map: forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2; }.

Class FunctorProp F `{FunctorData F} : Prop
  := {
      MAP_ID T:
        map (@id T) = id;
      MAP_COMPOSE T1 T2 T3
                  (f12: forall (x1:T1), T2)
                  (f23: forall (x2:T2), T3)
                  x1:
        map f23 (map f12 x1) = map (f23 ∘ f12) x1;
    }.
Arguments FunctorProp F {H}.

Class SFunctorData F `{FunctorData F} : Type
  := {
      mem: forall X, F X -> X -> Prop;
      tag: forall {X} (x : F X), F (sigT (mem x));
      rel: forall X Y (rel: X -> Y -> Prop) (fx:F X) (fy:F Y), Prop;
      (* TAG: forall X (x: F X), map (@projT1 X _) (tag x) = x; *)
    }.
Arguments SFunctorData F {H}.

Class SFunctorProp F `{H : FunctorData F} `{@SFunctorData _ H} `{@FunctorProp _ H}
  : Prop
  := {
      MAP_MEM: forall X Y (f: X -> Y) (fx: F X) (x: X) (MEM: mem fx x), mem (map f fx) (f x);
    }.
Arguments SFunctorProp F {H} {H0} {H1}.

Structure NatTrans (F G : Type -> Type) `{FunctorData F} `{FunctorData G} : Type :=
  {
    NT :> forall {X:Type} (fx:F X), G X;
    MAP_COMMUTE: forall T1 T2 (f:T1 -> T2) x, NT (map f x) = (map f) (NT x);
  }.
Arguments NatTrans F G {H} {H0}.

Class SNatTransProp F G `{H : FunctorData F} `{H0 : FunctorData G} 
      `{@SFunctorData F H} `{@SFunctorData G H0} `{H1 : @NatTrans F G _ _}
  : Prop := {
             MEM_COMMUTE: forall X fx (x:X), mem fx x <-> mem (H1 _ fx) x;
             REL_COMMUTE: forall T1 T2 (rel': forall (x1:T1) (x2:T2), Prop) fx1 fx2,
                 rel rel' fx1 fx2 <-> rel rel' (H1 _ fx1) (H1 _ fx2);
           }.

(* instances *)

Definition Ident (X : Type) := X.

Instance id_functorData : FunctorData Ident := Build_FunctorData _ (fun _ _ => id).

Program Instance id_sFunctorData : SFunctorData Ident
  := Build_SFunctorData _
                        (fun _ fx x => fx = x)
                        (fun _ x => existT _ x eq_refl)
                        (fun _ _ rel fx fy => rel fx fy).
Hint Resolve id_functorData id_sFunctorData.

Definition Const (T : Type) (X : Type) := T.

Instance const_functorData T : FunctorData (Const T)
  := Build_FunctorData (fun X => T) (fun _ _ _ x => x).

Program Instance const_sFunctorData T : SFunctorData (Const T)
  := Build_SFunctorData _
                        (fun _ _ _ => False)
                        (fun _ x => x)
                        (fun _ _ _ => eq).

Hint Resolve const_functorData const_sFunctorData.


Definition Expn (D : Type) (F : Type -> Type) := (fun X => D -> F X).

Definition function_map D F `{FunctorData F} T1 T2 (f: T1 -> T2)
           (fx1: D -> F T1) :=
  (map f) ∘ fx1.
Hint Unfold function_map.

Inductive function_mem D F `{SFunctorData F} T (fx: D -> F T) x: Prop :=
| Function_mem d (MEM: mem (fx d) x).
Hint Constructors function_mem.

Definition function_tag D F `{SFunctorData F} T (fx: D -> F T) : D -> F (sigT (function_mem fx)) :=
  fun d =>
    map (fun x => match x with
                    existT _ x m => existT (function_mem fx) x (Function_mem fx x d m)
                  end)
        (tag (fx d)).

Definition function_rel D F `{SFunctorData F} T1 T2
           f (fx1:D -> F T1) (fx2:D -> F T2): Prop :=
  forall d, rel f (fx1 d) (fx2 d).
Hint Unfold function_rel.

Instance function_functorData D F `{FunctorData F}
  : FunctorData (Expn D F) := Build_FunctorData _ (@function_map D F _).

Program Instance function_sFunctorData D F `{SFunctorData F}
  : SFunctorData (Expn D F)
  := Build_SFunctorData _
                        (@function_mem _ _ _ _)
                        (@function_tag _ _ _ _)
                        (@function_rel _ _ _ _).
Hint Resolve function_functorData function_sFunctorData.

Definition Coprod (F1 F2: Type -> Type) T := (F1 T + F2 T)%type.

Definition coproduct_map F1 F2 `{FunctorData F1} `{FunctorData F2} T1 T2
           (f:T1 -> T2) (fx: F1 T1 + F2 T1) :=
  match fx with
  | inl fx => inl (map f fx)
  | inr fx => inr (map f fx)
  end.

Hint Unfold coproduct_map.

Definition coproduct_mem F1 F2 `{SFunctorData F1} `{SFunctorData F2} T
           (fx: F1 T + F2 T) x :=
  match fx with
  | inl fx => mem fx x
  | inr fx => mem fx x
  end.

Hint Unfold coproduct_mem.

Inductive coproduct_rel F1 F2 `{SFunctorData F1} `{SFunctorData F2} T1 T2 f:
  forall (fx1:Coprod F1 F2 T1) (fx2:Coprod F1 F2 T2), Prop :=
| coproduct_rel_inl fx1 fx2 (REL: rel f fx1 fx2):
    coproduct_rel f (inl fx1) (inl fx2)
| coproduct_rel_inr fx1 fx2 (REL: rel f fx1 fx2):
    coproduct_rel f (inr fx1) (inr fx2)
.

Hint Constructors coproduct_rel.

Program Instance coproduct_functorData  F1 F2 `{FunctorData F1} `{FunctorData F2}
  : FunctorData (Coprod F1 F2)
  := Build_FunctorData _ (@coproduct_map _ _ _ _).

Program Instance coproduct_sFunctorData F1 F2 `{SFunctorData F1} `{SFunctorData F2}
  : SFunctorData (Coprod F1 F2)
  := Build_SFunctorData _
                        (@coproduct_mem _ _ _ _ _ _)
                        (fun _ x => match x with
                                    | inl x' => inl (tag x')
                                    | inr x' => inr (tag x')
                                    end)
                        (@coproduct_rel _ _ _ _ _ _) .
Hint Resolve coproduct_functorData coproduct_sFunctorData.

Definition map_dep F `{SFunctorData F} X Y (fx : F X) (f : forall x (MEM: mem fx x), Y)
  : F Y := map (fun x =>match x with existT _ _ m => f _ m end) (tag fx).
