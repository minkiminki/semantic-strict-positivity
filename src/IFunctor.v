Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.


(* Tactics.  FIXME: move it! *)

Ltac inv H := inversion H; subst; clear H.
Ltac simplify := repeat (autounfold in *; unfold id in *; simpl in *).

(* Categories *)

Section IFUNCTOR.

  Context {C : Type}.

  Definition iType := C -> Type.

  Class IFunctorData (F : iType -> iType) : Type
    := {
        map: forall {T1 T2 : iType} (f: forall i, T1 i -> T2 i) i, F T1 i -> F T2 i;
      }.

  Class IFunctorProp (F : iType -> iType) `{IFunctorData F} : Prop
    := {
        MAP_ID T:
          map (fun i (x : T i) => x) = (fun i x => x);
        MAP_COMPOSE (T1 T2 T3 : iType)
              (f12: forall i (x1:T1 i), T2 i)
              (f23: forall i (x2:T2 i), T3 i)
              i (x1 : F T1 i):
          map f23 i (map f12 i x1) = map (fun i x => f23 i (f12 i x)) i x1;
      }.
  Arguments IFunctorProp F {H}.

  Inductive sigTd {A : iType} (P : forall i, A i -> Type) : iType :=
  | existTd i (x : A i) : P i x -> sigTd P i .

  Class ISFunctorData F `{IFunctorData F} : Type
    := {
        mem {X} i : F X i-> forall j, X j -> Prop;
        tag {X} i (x : F X i): F (sigTd (mem x)) i;
        rel: forall {X Y} (rel: forall i, X i -> Y i -> Prop) i (fx:F X i) (fy:F Y i) , Prop;
      (* TAG: forall X (x: F X), map (@projT1 X _) (tag x) = x; *)
      }.
  Arguments ISFunctorData F {H}.

  Class ISFunctorProp F `{H : IFunctorData F} `{@ISFunctorData _ H} `{@IFunctorProp _ H}
    : Prop
    := {
        MAP_MEM: forall X Y (f: forall i, X i-> Y i) i j (fx: F X i) (x: X j)
                        (MEM: mem i fx j x), mem i (map f i fx) j (f j x);
      }.
  Arguments ISFunctorProp F {H} {H0} {H1}.

  Structure INatTrans (F G : iType -> iType) `{IFunctorData F} `{IFunctorData G} : Type :=
    {
      NT :> forall {X:iType} i (fx: F X i), G X i;
      MAP_COMMUTE: forall T1 T2 (f: forall i, T1 i -> T2 i) i x,
          NT (map f i x) = (map f i) (NT x);
    }.
  Arguments INatTrans F G {H} {H0}.

  Class ISNatTransProp F G `{H : IFunctorData F} `{H0 : IFunctorData G} 
        `{@ISFunctorData F H} `{@ISFunctorData G H0} `{H1 : @INatTrans F G _ _}
    : Prop := {
               MEM_COMMUTE: forall X i j (fx: F X i) (x:X j),
                 mem i fx j x <-> mem i (H1 _ _ fx) j x;
               REL_COMMUTE: forall X Y (rel': forall i, X i -> Y i -> Prop) i fx1 fx2,
                   rel rel' i fx1 fx2 <-> rel rel' i (H1 _ _ fx1) (H1 _ _ fx2);
             }.

  (* instances *)

  Definition Ident (X : iType) := X.

  Instance id_ifunctorData : IFunctorData Ident := Build_IFunctorData _ (fun _ _ => id).

  Inductive id_mem (X : iType) : forall i, X i -> forall j, X j -> Prop :=
  | _id_mem i (x : X i) : id_mem X i x i x.

  Program Instance id_isFunctorData : ISFunctorData Ident
    := Build_ISFunctorData _
                          id_mem
                          (fun X i x => existTd (id_mem X i x) i x (_id_mem X i x))
                          (fun _ _ => id).
  Hint Resolve id_ifunctorData id_isFunctorData.

  Definition Const (T : iType) (X : iType) := T.

  Instance const_ifunctorData T : IFunctorData (Const T)
    := Build_IFunctorData (Const T) (fun _ _ _ _ x => x).

  Program Instance const_isFunctorData T : ISFunctorData (Const T)
    := Build_ISFunctorData _
                          (fun _ _ _ _ _ => False)
                          (fun _ _ x => x)
                          (fun _ _ _ _ => eq).

  Hint Resolve const_ifunctorData const_isFunctorData.

  






  Definition Expn (D : Type) (F : Type -> Type) := (fun X => D -> F X).

(*
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

*)

End IFUNCTOR.