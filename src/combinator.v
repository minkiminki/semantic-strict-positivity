Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators Coq.Lists.List.

Set Implicit Arguments.

Require Import Functor SPFunctor.

Ltac sconstructor := repeat (try apply (@coproduct_rel_inl _ (Const _));
                     try apply (@coproduct_rel_inr _ (Const _));
                     try apply (@coproduct_rel_inl Ident (Const _));
                     try apply (@coproduct_rel_inr Ident (Const _));
                     simplify; subst; try constructor; auto).

Ltac comm H := simplify; try rewrite (@REL_COMMUTE _ (UF _ _) _ _ _ _ _ _ _) in H;
               try rewrite (@MEM_COMMUTE _ (UF _ _) _ _ _ _ _ _ _) in H;
               repeat rewrite MAP_COMMUTE in H; simplify.

Ltac commute := simplify; try rewrite (@REL_COMMUTE _ (UF _ _) _ _ _ _ _ _ _);
                try rewrite (@MEM_COMMUTE _ (UF _ _) _ _ _ _ _ _ _); 
                repeat rewrite MAP_COMMUTE; simplify.

Ltac des_ d := try destruct (emb _ _ d); subst; simplify; auto.

Ltac des := repeat (simplify; repeat (match goal with
                              | [ |- context[@NT _ _ _ _ _ _ _ ?d]] => des_ d
                              end);
            repeat (match goal with
               | [ H : coproduct_rel ?rel (inl ?i) (inl ?i0) |- _] => inv H end);
            repeat (match goal with
               | [ H : coproduct_rel ?rel (inl ?i) (inr ?i0) |- _] => inv H end);
            repeat (match goal with
               | [ H : coproduct_rel ?rel (inr ?i) (inl ?i0) |- _] => inv H end);
            repeat (match goal with
               | [ H : coproduct_rel ?rel (inr ?i) (inr ?i0) |- _] => inv H end);
            repeat (match goal with
               | [ H : inl ?i = inl ?i0 |- _] => inv H end);
            repeat (match goal with
               | [ H : inl ?i = inr ?i0 |- _] => inv H end);
            repeat (match goal with
               | [ H : inr ?i = inl ?i0 |- _] => inv H end);
            repeat (match goal with
               | [ H : inr ?i = inr ?i0 |- _] => inv H end);
                   sconstructor).

Ltac des' := repeat (simplify; repeat (match goal with
                              | [ |- context[emb _ _ ?d]] => des_ d
                              end);
            repeat (match goal with
               | [ H : coproduct_rel ?rel (inl ?i) (inl ?i0) |- _] => inv H end);
            repeat (match goal with
               | [ H : coproduct_rel ?rel (inl ?i) (inr ?i0) |- _] => inv H end);
            repeat (match goal with
               | [ H : coproduct_rel ?rel (inr ?i) (inl ?i0) |- _] => inv H end);
            repeat (match goal with
               | [ H : coproduct_rel ?rel (inr ?i) (inr ?i0) |- _] => inv H end);
            repeat (match goal with
               | [ H : inl ?i = inl ?i0 |- _] => inv H end);
            repeat (match goal with
               | [ H : inl ?i = inr ?i0 |- _] => inv H end);
            repeat (match goal with
               | [ H : inr ?i = inl ?i0 |- _] => inv H end);
            repeat (match goal with
               | [ H : inr ?i = inr ?i0 |- _] => inv H end);
            repeat (match goal with
               | [ H : function_mem _ _|- _] => destruct H end);
                   sconstructor).


(* comp list embed
const id option prod coprod function dep_prod dep_sum *)

(* Instances *)

Instance option_functorData : FunctorData option := Build_FunctorData _ option_map.

Inductive option_frel X Y (rel: forall (x:X) (y:Y), Prop):
  forall (fx:option X) (f:option Y), Prop :=
| option_frel_Some x y (REL: rel x y):
    option_frel rel (Some x) (Some y)
| option_frel_None:
    option_frel rel None None
.
Hint Constructors option_frel.

Program Instance option_sFunctorData `{FunctorData} : SFunctorData option
  := Build_SFunctorData _
                        (fun _ fx x => fx = Some x)
                        _
                        option_frel.
Next Obligation.
  destruct x.
  - apply Some. apply (existT _ x). auto.
  - apply None.
Defined.

Hint Resolve option_functorData.
Hint Resolve option_sFunctorData.


Definition Prod (F1 F2: Type -> Type) T := (F1 T * F2 T)%type.

Definition product_map F1 F2 `{FunctorData F1} `{FunctorData F2} T1 T2 (f:T1 -> T2) (fx: F1 T1 * F2 T1) :=
  match fx with
  | (f1x, f2x) => (map f f1x, map f f2x)
  end.

Definition product_mem F1 F2 `{SFunctorData F1} `{SFunctorData F2} T (fx:Prod F1 F2 T) x :=
  match fx with
  | (f1x, f2x) => (mem f1x x) \/ (mem f2x x)
  end.

Definition product_rel F1 F2 `{SFunctorData F1} `{SFunctorData F2} T1 T2 f
           (fx1:Prod F1 F2 T1) (fx2:Prod F1 F2 T2) : Prop :=
  match fx1, fx2 with
  | (f1x1, f2x1), (f1x2, f2x2) => (rel f f1x1 f1x2) /\ (rel f f2x1 f2x2) 
  end.
Hint Unfold product_map product_mem product_rel.


Instance product_functorData F1 F2 `{FunctorData F1} `{FunctorData F2}
  : FunctorData (Prod F1 F2)
  := Build_FunctorData _ (@product_map _ _ _ _).

Program Instance product_sFunctorData F1 F2 `{SFunctorData F1} `{SFunctorData F2}
  : SFunctorData (Prod F1 F2)
  := Build_SFunctorData _
                        (@product_mem _ _ _ _ _ _)
                        _
                        (@product_rel _ _ _ _ _ _).
Next Obligation.
  destruct x as [x1 x2]. apply pair.
  - set (x1' := tag x1).
    eapply (map _ (tag x1)). Unshelve. intro. destruct x0.
    apply (existT _ x (or_introl m)).
  - set (x1' := tag x2).
    eapply (map _ (tag x2)). Unshelve. intro. destruct x0.
    apply (existT _ x (or_intror m)).
Defined.

Hint Resolve product_functorData product_sFunctorData.


Inductive comp_mem F1 F2 `{SFunctorData F1} `{SFunctorData F2} X : F2 (F1 X) -> X -> Prop :=
| _comp_mem x (gx : F1 X) (fgx : F2 (F1 X)) (HG : mem gx x) (HF : mem fgx gx) :
    comp_mem fgx x.

Hint Constructors comp_mem.

Definition comp_rel F1 F2 `{SFunctorData F1} `{SFunctorData F2} X Y (RE: X -> Y -> Prop) : F2 (F1 X) -> F2 (F1 Y) -> Prop
  := rel (rel RE).
Hint Unfold comp_rel.

Program Instance compose_functorData F1 F2 `{FunctorData F1} `{FunctorData F2}
  : FunctorData (F2 ∘ F1)
  := Build_FunctorData (F2 ∘ F1) (fun _ _ f => (map (@map F1 _ _ _ f))).

Program Instance compose_sFunctorData F1 F2 `{SFunctorData F1} `{SFunctorData F2}
  : SFunctorData (F2 ∘ F1)
  := @Build_SFunctorData (F2 ∘ F1) _
                        (@comp_mem F1 F2 _ _ _ _)
                        _
                        (@comp_rel F1 F2 _ _ _ _).
Next Obligation.
  set (x' := @tag F2 _ _ _ x).
  eapply (map _ x'). Unshelve.
  intro. destruct x1.
  set (x'' := tag x0).
  eapply (map _ x''). Unshelve.
  intro. destruct x1.
  exists x1. econstructor.
  apply m0. apply m.
Defined.

Hint Resolve compose_functorData compose_sFunctorData.


Definition dep_prod_type A (B: A -> Type -> Type) X := (forall a: A, B a X).

Definition dep_prod_map A (B: A -> Type -> Type) `{forall a, FunctorData (B a)} X Y (f: X-> Y)
           (x : dep_prod_type B X) : (dep_prod_type B Y) :=
  fun (a: A) => map f (x a).

Definition dep_prod_mem A (B: A -> Type -> Type) `{H : forall a, FunctorData (B a)}
           `{forall a, @SFunctorData (B a) (H a)} X (fx: dep_prod_type B X) x :=
  exists (a: A), mem (fx a) x.


Definition dep_prod_rel A (B: A -> Type -> Type) `{H : forall a, FunctorData (B a)}
           `{forall a, @SFunctorData (B a) (H a)} X Y (RE : X -> Y -> Prop)
           (fx: dep_prod_type B X) (fy: dep_prod_type B Y) : Prop :=
  forall a : A, rel RE (fx a) (fy a).

Hint Unfold dep_prod_map dep_prod_mem dep_prod_rel.

Instance dep_prod_functorData A (B: A -> Type -> Type)
        `{forall a, FunctorData (B a)} : FunctorData (dep_prod_type B) :=
  Build_FunctorData _ (@dep_prod_map _ B _).

Program Instance dep_prod_sFunctorData A (B: A -> Type -> Type)
        `{H : forall a, FunctorData (B a)} `{forall a, @SFunctorData (B a) (H a)}
  : SFunctorData (dep_prod_type B) :=
  Build_SFunctorData _
                     (@dep_prod_mem A B _ _)
                     _
                     (@dep_prod_rel A B _ _).
Next Obligation.
  intro. set (xa := tag (x a)).
  eapply (map _ xa). Unshelve.
  intro. destruct x1.
  exists x0. exists a. apply m.
Defined.

Hint Resolve dep_prod_functorData dep_prod_sFunctorData.


Definition dep_sum_type A (B: A -> Type -> Type) X := sigT (fun a => B a X).

Definition dep_sum_map A (B: A -> Type -> Type) `{forall a, FunctorData (B a)}
           X Y (f: X-> Y) (fx : dep_sum_type B X) : dep_sum_type B Y :=
  match fx with
  | existT _ a fx' => existT _ a (map f fx') end. 

Definition dep_sum_mem A (B: A -> Type -> Type) `{H : forall a, FunctorData (B a)}
           `{forall a, @SFunctorData (B a) (H a)} X (fx: dep_sum_type B X) x :=
  match fx with
  | existT _ a fx => mem fx x end. 
Hint Unfold dep_sum_map dep_sum_mem.

Inductive dep_sum_rel A (B: A -> Type -> Type) `{H : forall a, FunctorData (B a)}
          `{forall a, @SFunctorData (B a) (H a)} X Y (RE: X -> Y -> Prop) :
  dep_sum_type B X -> dep_sum_type B Y -> Prop :=
| _dep_sum_rel a (x: B a X) (y: B a Y)(r: rel RE x y)
  : dep_sum_rel RE (existT _ a x) (existT _ a y).
Hint Constructors dep_sum_rel.

Instance dep_sum_functorData A (B: A -> Type -> Type) `{forall a, FunctorData (B a)}
         : FunctorData (dep_sum_type B) :=
  Build_FunctorData _ (@dep_sum_map _ B _).

Program Instance dep_sum_sFunctorData A (B: A -> Type -> Type)
        `{H : forall a, FunctorData (B a)} `{forall a, @SFunctorData (B a) (H a)}
  : SFunctorData (dep_sum_type B) :=
  Build_SFunctorData _
                     (@dep_sum_mem A B _ _)
                     _
                     (@dep_sum_rel A B _ _).
Next Obligation.
  destruct x. exists x. apply (tag b).
Defined.

Hint Resolve dep_sum_functorData dep_prod_sFunctorData.

Program Instance id_SPFunctor : SPFunctor Ident :=
  @Build_SPFunctor Ident _ _ unit False
                   (Build_NatTrans _ _ (fun _ x _ => inl x) _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  split; intros.
  - apply (Function_mem _ _ tt). auto.
  - inv H. inv MEM. auto.
Qed.
Next Obligation.
  split; intros.
  - intro. simplify. auto.
  - specialize (H tt). inv H. auto. 
Qed.
Next Obligation.
  apply equal_f with tt in EQ. inv EQ. auto.
Qed.

Hint Resolve id_SPFunctor.

Program Instance option_SPFunctor : SPFunctor option :=
  @Build_SPFunctor option _ _ unit unit
                   (Build_NatTrans _ _ (fun _ x _ =>
                                              match x with
                                              | Some x => inl x
                                              | None => inr ()
                                              end) _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  destruct x; auto.
Qed.
Next Obligation.
  split; intros.
  - econstructor; [apply ()|].
    subst. constructor.
  - inv H. destruct fx; simplify; inv MEM; auto.
Qed.
Next Obligation.
  destruct fx1, fx2; simplify;
    (split; intros; [inv H; econstructor; auto
                    | specialize (H tt); simplify; inv H; constructor; auto]).
  simplify. auto.
Qed.
Next Obligation.
  destruct x1, x2; simplify; auto;
  apply equal_f with tt in EQ; inv EQ; auto.
Qed.
Next Obligation.
  destruct x; auto.
Qed.

Hint Resolve option_SPFunctor.


Program Instance const_SPFunctor D : SPFunctor (Const D) :=
  @Build_SPFunctor (Const D) _ _ unit D
                   (Build_NatTrans _ _ (fun _ a _ => inr a) _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  split; intros.
  - inv H.
  - inv H. inv MEM.
Qed.
Next Obligation.
  split; intros.
  - subst. econstructor. econstructor.
  - simplify. specialize (H tt).
    simplify. inv H. inv REL. auto.
Qed.
Next Obligation.
  apply equal_f with tt in EQ.
  inv EQ. auto.
Qed.

Hint Resolve const_SPFunctor.

Arguments Sh1 F {H} {H0} {SPFunctor}.
Arguments Sh2 F {H} {H0} {SPFunctor}.

Definition prod_embed (F G : Type -> Type) `{SPFunctor F} `{SPFunctor G} X
           (x : (Prod F G) X) s
  :=
    match x with
    | (xl, xr) =>
      match s with
      | inl s' =>
        match (@emb _ _ H0 _ _ xl s') with
        | inl a => inl a
        | inr b => inr (inl b)
        end
      | inr s' =>
        match (@emb _ _ _ _ _ xr s') with
        | inl a => inl a
        | inr b => inr (inr b)
        end
      end
    end.
Hint Unfold prod_embed.


Program Instance prod_SPFunctor F1 F2 `{SPFunctor F1} `{SPFunctor F2}
  : SPFunctor (Prod F1 F2) :=
  @Build_SPFunctor (Prod F1 F2) _ _ (Sh1 F1 + Sh1 F2) (Sh2 F1 + Sh2 F2)
                   (Build_NatTrans _ _ (@prod_embed F1 F2 _ _ _ _ _ _) _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  destruct x; simplify; commute; extensionality s; destruct s; des.

Qed.
Next Obligation.
  split; intros; simplify; destruct fx.
  - destruct H5; comm H5; inv H5;
      [apply (Function_mem _ _ (inl d)) | apply (Function_mem _ _ (inr d))]; des.
  - inv H5; destruct d; [left | right]; commute;
      apply (Function_mem _ _ s); des.
Qed.
Next Obligation.
  split; intros; destruct fx1, fx2.
  - destruct H5. comm H5. comm H6.
    intro. destruct d; [specialize (H5 s) | specialize (H6 s)]; des.
  - split; commute; intro d;
      [specialize (H5 (inl d)) | specialize (H5 (inr d))]; des.
Qed.
Next Obligation.
  destruct x1, x2; simplify; f_equal; apply INJECTIVE; extensionality a;
  [apply equal_f with (inl a) in EQ | apply equal_f with (inr a) in EQ]; des.
Qed.
Next Obligation.
  destruct x. simpl. f_equal. 
  - rewrite MAP_COMPOSE. unfold compose.
    rewrite <- (TAG _ f) at 3. f_equal.
    extensionality s. destruct s. simpl. auto.
  - rewrite MAP_COMPOSE. unfold compose.
    rewrite <- (TAG _ f0) at 3. f_equal.
    extensionality s. destruct s. simpl. auto.
Qed.
Hint Resolve prod_SPFunctor.


Definition coprod_embed (F G : Type -> Type) `{SPFunctor F} `{SPFunctor G} X
           (x : (Coprod F G) X)
           (s: sum (sum unit (Sh1 F)) (sum unit (Sh1 G))) :=
  match x with
  | inl x' =>
    match s with
    | inl (inl _) => inr (inl true)
    | inl (inr s') =>
      match emb _ x' s' with
      | inl a => inl a
      | inr b => inr (inr (inl b))
      end
    | inr s' => inr (inl false)
    end
  | inr x' =>
    match s with
    | inl s' => inr (inl false)
    | inr (inl _) => inr (inl true)
    | inr (inr s') =>
      match emb _ x' s' with
      | inl a => inl a
      | inr b => inr (inr (inr b))
      end
    end  
  end.
Hint Unfold coprod_embed.

Program Instance coprod_SPFunctor F1 F2 `{SPFunctor F1} `{SPFunctor F2}
  : SPFunctor (Coprod F1 F2) :=
  @Build_SPFunctor (Coprod F1 F2) _ _ ((() + Sh1 F1) + (() + Sh1 F2))
                   (bool + (Sh2 F1 + Sh2 F2))
                   (Build_NatTrans _ _ (@coprod_embed F1 F2 _ _ _ _ _ _) _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  destruct x; extensionality a; simplify;
    destruct a; destruct s; commute; des.
Qed.
Next Obligation.
  split; intros.
  - destruct fx; comm H5; inv H5;
    [apply (Function_mem _ _ (inl (inr d))) |apply (Function_mem _ _ (inr (inr d)))];
    des.
  - inv H5. destruct fx; simplify; commute; simplify; 
              destruct d; destruct s; try inv MEM; apply (Function_mem _ _ s);
                des.
Qed.
Next Obligation.
  split; intros.
  - inv H5; comm REL; intro; destruct d; destruct s; sconstructor;
      specialize (REL s); des.
  - destruct fx1, fx2; simplify; sconstructor; commute.
    + intro. specialize (H5 (inl (inr d))). des. 
    + specialize (H5 (inl (inl tt))). des. 
    + specialize (H5 (inl (inl tt))). des.
    + intro. specialize (H5 (inr (inr d))). des. 
Qed.
Next Obligation.
  destruct x1, x2; f_equal.
  - apply INJECTIVE; simplify. extensionality s.
    apply equal_f with (inl (inr s)) in EQ. des.
  - apply equal_f with (inl (inl tt)) in EQ. des.
  - apply equal_f with (inl (inl tt)) in EQ. des.
  - apply INJECTIVE; simplify. extensionality s.
    apply equal_f with (inr (inr s)) in EQ. des.
Qed.
Next Obligation.
  destruct x; simpl; f_equal; apply TAG.
Qed.
Hint Resolve coprod_SPFunctor.

Definition function_embed D F `{SPFunctor F} X (x: D -> F X)
           (s: D * (Sh1 F)) : (X + (Sh2 F)) :=
  match s with
  | (d, s') => emb _ (x d) s' end.
Hint Unfold function_embed.

Program Instance function_SPFunctor D F `{SPFunctor F}
  : @SPFunctor (Expn D F) (function_functorData _ _) _ :=
  @Build_SPFunctor (Expn D F) _ _ (D * (Sh1 F))
                   (Sh2 F)
                   (Build_NatTrans _ _ (@function_embed D F _ _ _) _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  extensionality s. destruct s. simplify. commute. des.
Qed.
Next Obligation.
  split; intros; simplify.
  - inv H2. comm MEM. inv MEM. apply (Function_mem _ _ (d, d0)). des.
  - inv H2. destruct d. apply (Function_mem _ _ d). commute.
    apply (Function_mem _ _ s). des.
Qed.
Next Obligation.
  split; intros; simplify.
  - intro. destruct d. specialize (H2 d). comm H2. specialize (H2 s). des.
  - intro. commute. intro. specialize (H2 (d, d0)). des.
Qed.
Next Obligation.
  extensionality d. apply INJECTIVE. extensionality s.
  apply equal_f with (d, s) in EQ. auto.
Qed.
Next Obligation.
  unfold function_map. extensionality d. unfold compose. unfold function_tag.
  rewrite MAP_COMPOSE. unfold compose. rewrite <- TAG. f_equal.
  extensionality s. destruct s. auto.
Qed.
Hint Resolve function_SPFunctor.

Definition dep_prod_embed A (B: A -> Type -> Type)
           `{H : forall a, FunctorData (B a)}
           `{H0 : forall a, @SFunctorData (B a) (H a)}
           `{H1 : forall a, @SPFunctor (B a) (H a) (H0 a)}
           X (x: forall a : A, B a X)
           (s: sigT (fun a => Sh1 (B a))) : (X + (sigT (fun a => Sh2 (B a)))) :=
  match s with
  | existT _ a sh =>
    match emb _ (x a) sh with
    | inl v => inl v
    | inr v => inr (existT _ a v)
    end
  end.
Hint Unfold dep_prod_embed.

Program Instance dep_prod_SPFunctor  A (B: A -> Type -> Type)
           `{H : forall a, FunctorData (B a)}
           `{H0 : forall a, @SFunctorData (B a) (H a)}
           `{H1 : forall a, @SPFunctor (B a) (H a) (H0 a)}
  : SPFunctor (dep_prod_type B) :=
  @Build_SPFunctor (dep_prod_type B) _ _ (sigT (fun a => Sh1 (B a)))
                   (sigT (fun a => Sh2 (B a)))
                   (Build_NatTrans _ _ (@dep_prod_embed A B _ _ _) _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  extensionality s. destruct s. simplify. commute. des.
Qed.    
Next Obligation.
  split; intros.
  - destruct H2. comm H2. inv H2. apply (Function_mem _ _ (existT _ x0 d)). des.
  - inv H2. comm MEM. destruct d. exists x0. commute.
    apply (Function_mem _ _ s). des.
Qed.
Next Obligation.
  split; intros.
  - simplify. intro. destruct d. specialize (H2 x). comm H2. specialize (H2 s). des.
  - simplify. intro. commute. intro. specialize (H2 (existT _ a d)). des.
    dependent destruction REL. auto.
Qed.
Next Obligation.
  extensionality a. apply INJECTIVE. extensionality s.
  apply equal_f with (existT _ a s) in EQ. des. dependent destruction H3. auto.
Qed.
Next Obligation.
  unfold dep_prod_map. extensionality d. unfold dep_prod_sFunctorData_obligation_1.
  rewrite MAP_COMPOSE. unfold compose. rewrite <- TAG. f_equal.
  extensionality s. destruct s. auto.
Qed.

Hint Resolve dep_prod_SPFunctor.

Section DEP_SUM.

Variable A : Type.
Variable B : A -> Type -> Type.

Context `{H : forall a, FunctorData (B a)}.
Context `{H0 : forall a, @SFunctorData (B a) (H a)}.
Context `{H1 : forall a, @SPFunctor (B a) (H a) (H0 a)}.

Axiom eq_dec : forall (a1 a2 : A), {a1 = a2} + {~ a1 = a2}.

Ltac dec_eq a1 a2 := let p := fresh "p" in
                   destruct (eq_dec a1 a2) as [p|p];
                   [subst | ];
                   eauto; try intuition; repeat rewrite <- eq_rect_eq in *;
                   sconstructor.

Definition dep_sum_embed X (x: sigT (fun a => (B a) X))
           (s: sigT (fun a => sum unit (Sh1 (B a)))) :
  sum X (sum bool (sigT (fun a => (Sh2 (B a))))) :=
  match x with
  | existT _ a x' =>
    match s with
    | existT _ a' sh =>
      match (eq_dec a a') with
      | left pf =>
        match sh with
        | inl _ => inr (inl true)
        | inr sh' =>
          match emb _ (eq_rect _ (fun y => (B y) X) x' _ pf) sh' with
          | inl a => inl a
          | inr b => inr (inr (existT _ a' b)) end
        end
      | right _ => inr (inl false)
      end
    end
  end.
Hint Unfold dep_sum_embed.

Global Program Instance dep_sum_SPFunctor : SPFunctor (dep_sum_type B) :=
  @Build_SPFunctor (dep_sum_type B) _ _ (sigT (fun a => (unit + Sh1 (B a))%type))
                   (bool + (sigT (fun a => (Sh2 (B a)))))
                   (Build_NatTrans _ _ dep_sum_embed _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  destruct x. extensionality s. destruct s. simplify.
  dec_eq x x0. commute. des.
Qed.
Next Obligation.
  split; intros.
  - destruct fx. comm H2. inv H2. 
    apply (Function_mem _ _ (existT _ x0 (inr d))). dec_eq x0 x0. des.
  - inv H2. destruct d, fx, s; simplify; dec_eq x1 x0.
    commute. apply (Function_mem _ _ s). des.
Qed.
Next Obligation.
  split; intros.
  - destruct fx1, fx2. dependent destruction H2. intro d. destruct d.
    simplify. destruct s; dec_eq x0 x. comm r. specialize (r s). des.
  - destruct fx1, fx2. dec_eq x x0. commute. intro.
    specialize (H2 (existT _ x0 (inr d))). simplify. dec_eq x0 x0.
    + des. dependent destruction H3. auto.
    + specialize (H2 (existT _ x0 (inl tt))). simplify. dec_eq x x0.
      dec_eq x0 x0. inv H2. inv REL.
Qed.    
Next Obligation.
  destruct x1, x2. dec_eq x x0.
  - f_equal. apply INJECTIVE. extensionality s.
    apply equal_f with (existT _ x0 (inr s)) in EQ. dec_eq x0 x0.
    des. dependent destruction H3. auto.
  - apply equal_f with (existT _ x (inl tt)) in EQ.
    dec_eq x x. dec_eq x0 x. inv EQ.
Qed.
Next Obligation.
  destruct x. simpl. f_equal. apply TAG.
Qed.

Hint Resolve dep_sum_SPFunctor.

End DEP_SUM.


Definition comp_embed' (F G : Type -> Type) `{SPFunctor F} `{SPFunctor G} X
           (x': (Sh1 F) -> (sum ((Sh1 G) -> (sum X (Sh2 G))) (Sh2 F)))
           (s: prod (sum unit (Sh1 G)) (Sh1 F)) :=
  match s with
  | (sg', sf) =>
    match x' sf with
    | inl x'' =>
      match sg' with
      | inl _ => inr (inl tt)
      | inr sg =>
        match x'' sg with
        | inl x''' => inl x'''
        | inr e => inr (inr (inl e)) end
      end
    | inr e' =>
      match sg' with
      | inl _ => inr (inr (inr e'))
      | inr _ => inr (inl tt) end
    end
  end.
Hint Unfold comp_embed'.

Lemma comp_embed'_injective F G `{SPFunctor F} `{SPFunctor G} X x y
  : @comp_embed' F G _ _ _ _ _ _ X x = @comp_embed' F G _ _ _ _ _ _ X y -> x = y.
Proof.
  unfold comp_embed'. intros.
  extensionality s. destruct (x s) eqn : EQ1; destruct (y s) eqn : EQ2.
  - f_equal.
    extensionality t.
    apply equal_f with (inr t, s) in H5.
    rewrite EQ1 in H5. rewrite EQ2 in H5.
    destruct (s0 t); destruct (s1 t); inversion H5; eauto.
  - apply equal_f with (inl tt, s) in H5.
    rewrite EQ1 in H5. rewrite EQ2 in H5. inversion H5.
  - apply equal_f with (inl tt, s) in H5.
    rewrite EQ1 in H5. rewrite EQ2 in H5. inversion H5.
  - f_equal.
    apply equal_f with (inl tt, s) in H5.
    rewrite EQ1 in H5. rewrite EQ2 in H5. inversion H5. eauto.
Qed.

Definition comp_embed F G `{SPFunctor F} `{SPFunctor G} X (x: F (G X)) :=
  @comp_embed' F G _ _ _ _ _ _ _ (emb _ (map (emb _) x)).
Hint Unfold comp_embed.

Program Instance comp_SPFunctor F1 F2 `{SPFunctor F1} `{SPFunctor F2}
  : SPFunctor (compose F1 F2) :=
  @Build_SPFunctor (compose F1 F2) _ _ ((() + Sh1 F2) * Sh1 F1) 
                   (() + (Sh2 F2 + Sh2 F1))
                   (Build_NatTrans _ _ (@comp_embed F1 F2 _ _ _ _ _ _) _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  extensionality s. destruct s. simplify. destruct s.
  - commute. des.
  - commute. des_ s0. commute. des.
Qed.
Next Obligation.
  split; intros.
  - inv H5. comm HG. comm HF. inv HG. inv HF.
    apply (Function_mem _ _ (inr d, d0)). commute. des.
  - simplify. inv H5. destruct d. destruct s.
    + comm MEM. des_ s0; inv MEM.
    + comm MEM. 
      destruct (emb _ _ s0) eqn : EQ; [| inv MEM]. apply (_comp_mem x i fx).
      commute. apply (Function_mem _ _ s). des.
      commute. apply (Function_mem _ _ s0). des.
Qed.
Next Obligation.
  split; intros.
  - comm H5. intro. destruct d. specialize (H5 s0). commute. destruct s; [des|].
    des_ s0; des_ s0; inv H5. comm REL. specialize (REL s). des. sconstructor.
  - simplify. commute. intro. comm H5.
    destruct (emb _ fx1 d) eqn : EQ1;
    destruct (emb _ fx2 d) eqn : EQ2.
    + sconstructor. commute. intro. specialize (H5 (inr d0, d)). simplify.
      rewrite EQ1 in H5. rewrite EQ2 in H5. des.
    + specialize (H5 (inl tt, d)). simplify.
      rewrite EQ1 in H5. rewrite EQ2 in H5. inv H5. inv REL.
    + specialize (H5 (inl tt, d)). simplify.
      rewrite EQ1 in H5. rewrite EQ2 in H5. inv H5. inv REL.
    + sconstructor. specialize (H5 (inl tt, d)). simplify.
      rewrite EQ1 in H5. rewrite EQ2 in H5. inv H5. inv REL. auto.
Qed.   
Next Obligation.
  unfold comp_embed in EQ. apply comp_embed'_injective in EQ.
  apply INJECTIVE in EQ. simplify.
  apply (map_injective (NT _) _ _ (@INJECTIVE _ _ _ _ _) EQ).
Qed.
Next Obligation.
  unfold compose_sFunctorData_obligation_1.
  rewrite MAP_COMPOSE. simpl. unfold compose.
  rewrite <- TAG. f_equal. extensionality x0.
  destruct x0.
  rewrite MAP_COMPOSE. simpl. rewrite <- TAG. f_equal.
  extensionality s. unfold compose. destruct s. auto.
Qed.
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

Definition list_tag X (x: list X) : list (sigT (list_mem x)).
  induction x.
  - apply nil.
  - apply cons.
    + exists a. constructor. auto.
    + simpl. eapply (List.map _ IHx). Unshelve.
      intro. destruct X0.
      exists x0. auto.
Defined.

Definition list_map_dep X Y (x: list X) (ALL: forall y, list_mem x y -> Y) : list Y.
  induction x.
  - apply nil.
  - apply cons.
    + apply (ALL a (or_introl (eq_refl a))).
    + apply IHx. intros.
      apply (ALL y (or_intror H)).
Defined.

Instance list_functorData : FunctorData list := Build_FunctorData _ List.map.

Program Instance list_sFunctorData `{FunctorData} : SFunctorData list
  := Build_SFunctorData _ list_mem list_tag list_rel.

Hint Resolve list_functorData.
Hint Resolve list_sFunctorData.


Fixpoint list_embed X (l: list X) : list unit -> X + unit :=
  match l with
  | nil => (fun x => inr tt)
  | cons hd tl => (fun x => match x with
                            | nil => inl hd
                            | cons xhd xtl => list_embed tl xtl end) end.

Program Instance list_SPFunctor : SPFunctor list :=
  @Build_SPFunctor list _ _ (list unit) unit
                   (Build_NatTrans _ _ list_embed _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  induction x.
  - extensionality s. auto.
  - extensionality s. destruct s; auto.
    apply equal_f with s in IHx. auto.
Qed.
Next Obligation.
  split; intros; induction fx.
  - inv H.
  - inv H.
    + apply (Function_mem _ _ nil). sconstructor.
    + apply IHfx in H0. inv H0.
      apply (Function_mem _ _ (cons tt d)). sconstructor.
  - inv H. inv MEM.
  - inv H. destruct d.
    + inv MEM. sconstructor.
    + right. apply IHfx. apply (Function_mem _ _ d). sconstructor.
Qed.      
Next Obligation.
  split; intros; revert fx2 H; induction fx1; intros.
  - inv H. intro. sconstructor.
  - inv H. intro. destruct d; sconstructor.
  - destruct fx2; [constructor|].
    specialize (H nil). inv H.
  - destruct fx2; [specialize (H nil); inv H|]. constructor.
    + specialize (H nil). inv H. auto.
    + apply IHfx1. intro. specialize (H (cons tt d)). auto.
Qed.
Next Obligation.
  revert x2 EQ. induction x1; intros.
  - destruct x2; auto. apply equal_f with nil in EQ. inversion EQ.
  - destruct x2; [apply equal_f with nil in EQ; inv EQ|]. f_equal.
    + apply equal_f with nil in EQ. inversion EQ. auto.
    + apply IHx1. extensionality s. apply equal_f with (cons tt s) in EQ. auto.
Qed.
Next Obligation.
  induction x.
  - auto.
  - simpl. f_equal.
    rewrite List.map_map. 
    rewrite <- IHx at 3. remember (list_tag x).
    clear Heql IHx. induction l.
    + auto.
    + simpl. destruct a0. f_equal.
      apply IHl.
Qed.
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

Definition tree_tag X (x : tree X) : tree (sigT (tree_mem x)).
  induction x.
  - apply leaf.
  - apply node; simpl.
    + exists x1. auto.
    + eapply (tree_map _ IHx1). Unshelve.
      intro. destruct X0.
      exists x. auto.
    + eapply (tree_map _ IHx2). Unshelve.
      intro. destruct X0.
      exists x. auto.
Defined.

Definition tree_map_dep X Y (x: tree X) (ALL: forall y, tree_mem x y -> Y) : tree Y.
  induction x.
  - apply leaf.
  - apply node.
    + apply (ALL x1 (or_introl (eq_refl x1))).
    + apply IHx1. intros. apply (ALL y (or_intror (or_introl H))).
    + apply IHx2. intros. apply (ALL y (or_intror (or_intror H))).
Defined.

Instance tree_functorData : FunctorData tree := Build_FunctorData _ tree_map.

Program Instance tree_sFunctorData `{FunctorData} : SFunctorData tree
  := Build_SFunctorData _ tree_mem tree_tag tree_rel.

Hint Resolve tree_functorData.
Hint Resolve tree_sFunctorData.


Fixpoint tree_embed X (t: tree X) : list bool -> X + unit :=
  match t with
  | leaf => (fun x => inr tt)
  | node v lt rt => (fun x => match x with
                              | nil => inl v
                              | cons true xtl => tree_embed lt xtl
                              | cons false xtl => tree_embed rt xtl end) end.

Program Instance tree_SPFunctor : SPFunctor tree :=
  @Build_SPFunctor tree _ _ (list bool) unit
                   (Build_NatTrans _ _ tree_embed _)
                   (Build_SNatTransProp _ _ _ _ _) _ _.
Next Obligation.
  induction x.
  - extensionality s. auto.
  - extensionality s. destruct s; auto. destruct b.
    + apply equal_f with s in IHx1. auto.
    + apply equal_f with s in IHx2. auto.
Qed.
Next Obligation.
  split; intros; induction fx.
  - inv H.
  - inv H; [|destruct H0].
    + apply (Function_mem _ _ nil). sconstructor.
    + apply IHfx1 in H. inv H.
      apply (Function_mem _ _ (cons true d)). sconstructor.
    + apply IHfx2 in H. inv H.
      apply (Function_mem _ _ (cons false d)). sconstructor.
  - inv H. inv MEM.
  - inv H. destruct d; [| destruct b].
    + inv MEM. sconstructor.
    + right. left. apply IHfx1. apply (Function_mem _ _ d). sconstructor.
    + right. right. apply IHfx2. apply (Function_mem _ _ d). sconstructor.
Qed.
Next Obligation.
  split; intros; revert fx2 H; induction fx1; intros.
  - inv H. intro. sconstructor.
  - inv H. intro. destruct d; sconstructor. destruct b; sconstructor.
  - destruct fx2; [constructor|].
    specialize (H nil). inv H.
  - destruct fx2; [specialize (H nil); inv H|]. constructor.
    + specialize (H nil). inv H. auto.
    + apply IHfx1_1. intro. specialize (H (cons true d)). auto.
    + apply IHfx1_2. intro. specialize (H (cons false d)). auto.
Qed.
Next Obligation.
  revert x2 EQ. induction x1; intros.
  - destruct x2; auto. apply equal_f with nil in EQ. inversion EQ.
  - destruct x2; [apply equal_f with nil in EQ; inv EQ|]. f_equal.
    + apply equal_f with nil in EQ. inversion EQ. auto.
    + apply IHx1_1. extensionality s. apply equal_f with (cons true s) in EQ. auto.
    + apply IHx1_2. extensionality s. apply equal_f with (cons false s) in EQ. auto.
Qed.
Next Obligation.
  induction x; auto.
  simpl. f_equal.
  - rewrite <- IHx1 at 3. remember (tree_tag x2).
    clear Heqt IHx1 IHx2. induction t; auto.
    simpl. f_equal; auto.
    destruct x. auto.
  - rewrite <- IHx2 at 3. remember (tree_tag x3).
    clear Heqt IHx1 IHx2. induction t; auto.
    simpl. f_equal; auto.
    destruct x. auto.
Qed.
Hint Resolve tree_SPFunctor.
