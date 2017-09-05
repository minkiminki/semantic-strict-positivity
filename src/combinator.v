Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators Coq.Lists.List.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor.

(* comp list embed
const id option prod coprod function dep_prod dep_sum *)

(* Instances *)

Definition option_functorData : FunctorData option := Build_FunctorData _ option_map.

Inductive option_frel X Y (rel: forall (x:X) (y:Y), Prop):
  forall (fx:option X) (f:option Y), Prop :=
| option_frel_Some x y (REL: rel x y):
    option_frel rel (Some x) (Some y)
| option_frel_None:
    option_frel rel None None
.
Hint Constructors option_frel.

Program Definition option_sFunctorData : SFunctorData option
  := Build_SFunctorData option_functorData
                        (fun _ fx x => fx = Some x)
                        (fun _ _ fx FX => match fx with | Some fx => Some (FX fx eq_refl) | None => None end)
                        option_frel _.
Next Obligation.
  destruct fx; auto.
  simpl. f_equal. apply INV.
Qed.

Hint Resolve option_functorData.
Hint Resolve option_sFunctorData.


Definition Prod (F1 F2: Type -> Type) T := (F1 T * F2 T)%type.

Definition product_map F1 F2 (Fn1 : FunctorData F1) (Fn2 : FunctorData F2) T1 T2 (f:T1 -> T2) (fx: F1 T1 * F2 T1) :=
  match fx with
  | (f1x, f2x) => (Fn1.(map) f f1x, Fn2.(map) f f2x)
  end.

Definition product_mem F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2) T (fx:Prod F1 F2 T) x :=
  match fx with
  | (f1x, f2x) => (Fn1.(mem) f1x x) \/ (Fn2.(mem) f2x x)
  end.

Definition product_rel F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2)T1 T2 f
           (fx1:Prod F1 F2 T1) (fx2:Prod F1 F2 T2) : Prop :=
  match fx1, fx2 with
  | (f1x1, f2x1), (f1x2, f2x2) => (Fn1.(rel) f f1x1 f1x2) /\ (Fn2.(rel) f f2x1 f2x2) 
  end.
Hint Unfold product_map product_mem product_rel.


Definition product_functorData F1 F2 (Fn1 : FunctorData F1) (Fn2 : FunctorData F2)
  : FunctorData (Prod F1 F2)
  := Build_FunctorData _ (@product_map _ _ Fn1 Fn2).

Program Definition product_sFunctorData F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2)
  : SFunctorData (Prod F1 F2)
  := Build_SFunctorData (product_functorData Fn1 Fn2)
                        (@product_mem _ _ Fn1 Fn2)
                        _
                        (@product_rel _ _ Fn1 Fn2) _.
Next Obligation.
  destruct fx.
  apply (Fn1.(map_dep) f0 (fun x r => f _ (or_introl r)),
        Fn2.(map_dep) f1 (fun x r => f _ (or_intror r))).
Defined.  
Next Obligation.
  destruct fx. simplify. f_equal; apply MAP_DEP; auto.
Qed.

Hint Resolve product_functorData product_sFunctorData.


Inductive comp_mem F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2) X : F2 (F1 X) -> X -> Prop :=
| _comp_mem x (gx : F1 X) (fgx : F2 (F1 X)) (HG : Fn1.(mem) gx x) (HF : Fn2.(mem) fgx gx) :
    comp_mem Fn1 Fn2 fgx x.

Hint Constructors comp_mem.

Definition comp_rel F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2) X Y (RE: X -> Y -> Prop) : F2 (F1 X) -> F2 (F1 Y) -> Prop
  := Fn2.(rel) (Fn1.(rel) RE).
Hint Unfold comp_rel.

Program Definition compose_functorData F1 F2 (Fn1 : FunctorData F1) (Fn2 : FunctorData F2)
  : FunctorData (F2 ∘ F1)
  := Build_FunctorData (F2 ∘ F1) (fun _ _ f => (Fn2.(map) (@map F1 Fn1 _ _ f))).

Program Definition compose_sFunctorData F1 F2 (Fn1 : SFunctorData F1) (Fn2 : SFunctorData F2)
  : SFunctorData (F2 ∘ F1)
  := @Build_SFunctorData (F2 ∘ F1) (compose_functorData Fn1 Fn2)
                        (@comp_mem F1 F2 _ _)
                        _
                        (@comp_rel F1 F2 _ _) _.
Next Obligation.
  apply (@map_dep F2 Fn2 _ _ fx (fun (y : F1 X) r1 => (Fn1.(map_dep) y (fun (z : X) r2 => f z (@_comp_mem F1 F2 Fn1 Fn2 X z y fx r2 r1))))).
Defined.
Next Obligation.
  apply (@MAP_DEP F2). intros.
  apply MAP_DEP. auto.
Qed.

Hint Resolve compose_functorData compose_sFunctorData.


Definition dep_prod_type A (B: A -> Type -> Type) X := (forall a: A, B a X).

Definition dep_prod_map A (B: A -> Type -> Type) (Fn : forall a, FunctorData (B a)) X Y (f: X-> Y)
           (x : dep_prod_type B X) : (dep_prod_type B Y) :=
  fun (a: A) => (Fn a).(map) f (x a).

Definition dep_prod_mem A (B: A -> Type -> Type) (Fn : forall a, SFunctorData (B a))
           X (fx: dep_prod_type B X) x :=
  exists (a: A), (Fn a).(mem) (fx a) x.


Definition dep_prod_rel A (B: A -> Type -> Type) (Fn : forall a, SFunctorData (B a))
           X Y (RE : X -> Y -> Prop)
           (fx: dep_prod_type B X) (fy: dep_prod_type B Y) : Prop :=
  forall a : A, (Fn a).(rel) RE (fx a) (fy a).

Hint Unfold dep_prod_map dep_prod_mem dep_prod_rel.

Definition dep_prod_functorData A (B: A -> Type -> Type)
        (Fn : forall a, FunctorData (B a)) : FunctorData (dep_prod_type B) :=
  Build_FunctorData _ (@dep_prod_map _ B Fn).

Program Definition dep_prod_sFunctorData A (B: A -> Type -> Type)
        (Fn : forall a, SFunctorData (B a))
  : SFunctorData (dep_prod_type B) :=
  Build_SFunctorData (dep_prod_functorData B Fn) 
                     (@dep_prod_mem A B Fn)
                     _
                     (@dep_prod_rel A B Fn) _.
Next Obligation.
  intro.
  apply ((Fn a).(map_dep) (fx a) 
      (fun y r => f y (ex_intro (fun a => (Fn a).(mem) (fx a) y) _ r))).
Defined.
Next Obligation.
  extensionality s. apply MAP_DEP. auto.
Qed.

Hint Resolve dep_prod_functorData dep_prod_sFunctorData.


Definition dep_sum_type A (B: A -> Type -> Type) X := sigT (fun a => B a X).

Definition dep_sum_map A (B: A -> Type -> Type) (Fn : forall a, FunctorData (B a))
           X Y (f: X-> Y) (fx : dep_sum_type B X) : dep_sum_type B Y :=
  match fx with
  | existT _ a fx' => existT _ a ((Fn a).(map) f fx') end. 

Definition dep_sum_mem A (B: A -> Type -> Type) (Fn : forall a, SFunctorData (B a))
            X (fx: dep_sum_type B X) x :=
  match fx with
  | existT _ a fx => (Fn a).(mem) fx x end. 
Hint Unfold dep_sum_map dep_sum_mem.

Inductive dep_sum_rel A (B: A -> Type -> Type) (Fn : forall a, SFunctorData (B a))
          X Y (RE: X -> Y -> Prop) :
  dep_sum_type B X -> dep_sum_type B Y -> Prop :=
| _dep_sum_rel a (x: B a X) (y: B a Y)(r: (Fn a).(rel) RE x y)
  : dep_sum_rel Fn RE (existT _ a x) (existT _ a y).
Hint Constructors dep_sum_rel.

Definition dep_sum_functorData A (B: A -> Type -> Type) (Fn : forall a, FunctorData (B a))
         : FunctorData (dep_sum_type B) :=
  Build_FunctorData _ (@dep_sum_map _ B Fn).

Program Definition dep_sum_sFunctorData A (B: A -> Type -> Type)
        (Fn : forall a, SFunctorData (B a))
  : SFunctorData (dep_sum_type B) :=
  Build_SFunctorData (dep_sum_functorData B Fn)
                     (@dep_sum_mem A B Fn)
                     _
                     (@dep_sum_rel A B Fn) _.
Next Obligation.
  destruct fx.
  apply (existT _ x ((Fn x).(map_dep) b (fun x0 r => f _ r))).
Defined.
Next Obligation.
  destruct fx. simplify. f_equal.
  apply MAP_DEP. auto.
Qed.

Hint Resolve dep_sum_functorData dep_prod_sFunctorData.

Program Instance id_SPFunctor : SPFunctor Ident :=
  @Build_SPFunctor Ident id_sFunctorData _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve id_SPFunctor.


Program Instance option_SPFunctor : SPFunctor option :=
  @Build_SPFunctor option option_sFunctorData _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve option_SPFunctor.


Program Instance const_SPFunctor D : SPFunctor (Const D) :=
  @Build_SPFunctor (Const D) (const_sFunctorData D) _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve const_SPFunctor.


Program Instance prod_SPFunctor F1 F2 `{Fn1 : SPFunctor F1} `{Fn2 : SPFunctor F2}
  : SPFunctor (Prod F1 F2) :=
  @Build_SPFunctor (Prod F1 F2) (product_sFunctorData Fn1 Fn2) _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve prod_SPFunctor.

Program Instance coprod_SPFunctor F1 F2 `{Fn1 : SPFunctor F1} `{Fn2 : SPFunctor F2}
  : SPFunctor (Coprod F1 F2) :=
  @Build_SPFunctor (Coprod F1 F2) (coproduct_sFunctorData Fn1 Fn2) _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve coprod_SPFunctor.

Program Instance function_SPFunctor D F `{Fn : SPFunctor F}
  : @SPFunctor (Expn D F) :=
  @Build_SPFunctor (Expn D F) (function_sFunctorData D Fn) _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve function_SPFunctor.


Program Instance dep_prod_SPFunctor A (B: A -> Type -> Type)
        `{Fn : forall a, SPFunctor (B a)}
  : SPFunctor (dep_prod_type B) :=
  @Build_SPFunctor (dep_prod_type B) (dep_prod_sFunctorData B Fn) _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve dep_prod_functorData.


Program Instance dep_sum_SPFunctor A (B: A -> Type -> Type)
        `{Fn : forall a, SPFunctor (B a)}
  : SPFunctor (dep_sum_type B) :=
  @Build_SPFunctor (dep_sum_type B) (dep_sum_sFunctorData B Fn) _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve dep_sum_sFunctorData.

Program Instance comp_SPFunctor F1 F2 `{Fn1 : SPFunctor F1} `{Fn2 : SPFunctor F2}
  : SPFunctor (compose F1 F2) :=
  @Build_SPFunctor (compose F1 F2) (compose_sFunctorData Fn2 Fn1) _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve comp_SPFunctor.


Fixpoint list_mem X (l: list X) (x: X) : Prop :=
match l with
| nil => False
| cons hd tl => eq hd x \/ list_mem tl x end.

Inductive list_rel (X Y : Type) (RE: X -> Y -> Prop) : list X -> list Y -> Prop :=
| _list_rel_nil : list_rel RE nil nil
| _list_rel_cons hd1 hd2 tl1 tl2 (HD: RE hd1 hd2) (TL: list_rel RE tl1 tl2) : 
    (list_rel RE (cons hd1 tl1) (cons hd2 tl2)).
Hint Constructors list_rel.

Definition list_map_dep X Y (x: list X) (ALL: forall y, list_mem x y -> Y) : list Y.
  induction x.
  - apply nil.
  - apply cons.
    + apply (ALL a (or_introl (eq_refl a))).
    + apply IHx. intros.
      apply (ALL y (or_intror H)).
Defined.

Definition list_functorData : FunctorData list := Build_FunctorData _ List.map.

Program Definition list_sFunctorData : SFunctorData list
  := Build_SFunctorData list_functorData list_mem list_map_dep list_rel _.
Next Obligation.
  induction fx.
  - intros. auto.
  - intros. simpl. f_equal; auto.
Qed.

Hint Resolve list_functorData.
Hint Resolve list_sFunctorData.


Program Instance list_SPFunctor : SPFunctor list :=
  @Build_SPFunctor list list_sFunctorData _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve list_SPFunctor.


Inductive tree X : Type :=
| leaf : tree X
| node : X -> tree X -> tree X -> tree X.
Arguments leaf {X}.

Fixpoint tree_map X Y (f : X -> Y) (t : tree X) : tree Y :=
  match t with
  | leaf => leaf
  | node v lt rt => node (f v) (tree_map f lt) (tree_map f rt) end.

Fixpoint tree_mem X (t : tree X) (x: X) : Prop :=
match t with
| leaf => False
| node v t1 t2 => (v = x) \/ tree_mem t1 x \/ tree_mem t2 x end.

Inductive tree_rel (X Y : Type) (RE: X -> Y -> Prop) : tree X -> tree Y -> Prop :=
| _tree_rel_leaf : tree_rel RE leaf leaf
| _tree_rel_node v1 v2 lt1 lt2 rt1 rt2
  : RE v1 v2 -> tree_rel RE lt1 lt2 -> tree_rel RE rt1 rt2
    -> tree_rel RE (node v1 lt1 rt1) (node v2 lt2 rt2).
Hint Constructors tree_rel.

Definition tree_map_dep X Y (x: tree X) (ALL: forall y, tree_mem x y -> Y) : tree Y.
  induction x.
  - apply leaf.
  - apply node.
    + apply (ALL x1 (or_introl (eq_refl x1))).
    + apply IHx1. intros. apply (ALL y (or_intror (or_introl H))).
    + apply IHx2. intros. apply (ALL y (or_intror (or_intror H))).
Defined.

Definition tree_functorData : FunctorData tree := Build_FunctorData _ tree_map.

Program Definition tree_sFunctorData : SFunctorData tree
  := Build_SFunctorData tree_functorData tree_mem tree_map_dep tree_rel _.
Next Obligation.
  induction fx.
  - reflexivity.
  - simpl. f_equal; auto.
Qed.

Hint Resolve tree_functorData.
Hint Resolve tree_sFunctorData.


Program Instance tree_SPFunctor : SPFunctor tree :=
  @Build_SPFunctor tree tree_sFunctorData _ _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Hint Resolve tree_SPFunctor.