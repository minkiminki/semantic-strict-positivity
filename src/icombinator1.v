Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor hott iso container_combinator.

Arguments S {C} F {SPFunctor}.
Arguments P {C} F {SPFunctor}.
Arguments NT {C F G H H0} NatIso {X} f.
Arguments NTinv {C F G H H0} NatIso {X} f.
Arguments ISO {C F} SPFunctor.
Arguments NatIso {C F G} H H0.
Arguments Transitive_NatIso {C F G H FnF FnG FnH} H0 H1.

Section IDENT.

  Variable C : Type.
  Variable i : C.

  Definition Ident (X : C -> Type) := X i.

  Inductive Ident_eq (X : C -> Type) (x : Ident X) :
    forall i, X i -> Prop :=
  | Ident_eq_refl : Ident_eq X x i x.

  Definition Ident_Functor : Functor Ident
    := Build_Functor _ (fun _ _ f => f i) Ident_eq (fun _ _ R => @R i)
                     (fun X fx => existI fx (Ident_eq_refl _ fx)).

  Program Instance Ident_SPF : SPFunctor Ident
    := @Build_SPFunctor _ _ Ident_Functor unit (fun _ j => i = j)
                        (Build_NatIso _ _
                                      (fun X fx =>
                                         (existT _ tt
                                                 (fun j EQ => eq_rect i X fx j EQ)))
                                      (fun X gx => projT2 gx i eq_refl)
                                      _ _ _ _ _) _.
  Next Obligation.
    compute. f_equal.
    extensionality i0. extensionality e.
    destruct e. reflexivity.
  Qed.
  Next Obligation.
    split; intros.
    - destruct H.
      exists eq_refl. reflexivity.
    - destruct H. destruct x0. destruct H.
      constructor.
  Qed.
  Next Obligation.
    split; intros.
    - constructor. intros.
      destruct p. apply H.
    - inversion H. subst. apply (H1 i eq_refl).
  Qed.
  Next Obligation.
    compute. destruct gx. destruct x. f_equal.
    extensionality i0. extensionality e.
    destruct e. reflexivity.
  Qed.

End IDENT.

Section CONST.

  Variable C D : Type.

  Definition Const (X : C -> Type) := D.

  Definition Const_Functor : Functor Const
    := Build_Functor _ (fun _ _ _ => @id D) (fun _ _ _ _ => False) (fun _ _ _ => eq)
                     (fun _ => id).

  Program Instance Const_SPF : SPFunctor Const
    := @Build_SPFunctor _ _ Const_Functor D (fun _ _ => False)
                        (Build_NatIso _ _
                                      (fun _ fx => existT _ fx (fun _ => False_rect _))
                                      (fun _ => @projT1 _ _) _ _ _ _ _) _.
  Next Obligation.
    compute. f_equal.
    extensionality i. extensionality x. destruct x.
  Qed.
  Next Obligation.
    split; compute; intros.
    - destruct H.
    - destruct H. destruct x0.
  Qed.
  Next Obligation.
    split; compute; intros.
    - destruct H. apply Container_rel.
      intros. destruct p.
    - inversion H. reflexivity.
  Qed.
  Next Obligation.
    destruct gx.
    compute. f_equal.
    extensionality i. extensionality f. destruct f.
  Qed.

End CONST.

Section PROD.

  Variable C : Type.
  Variable (F G : (C -> Type) -> Type).
  Context `{SPF_F : SPFunctor _ F}.
  Context `{SPF_G : SPFunctor _ G}.

  Program Instance Prod_SPF : SPFunctor (Prod F G) := 
    @Build_SPFunctor _ _ (@Prod_Functor _ F G Fn Fn) _ _
                     (Transitive_NatIso
                        (@Prod_Iso _ _ _ _ _ _ _ _ _ (ISO SPF_F) (ISO SPF_G))
                        (Prod_Container (P F) (P G))) _.
  Next Obligation.
    rewrite surjective_pairing.
    f_equal; rewrite MAP_COMPOSE; apply TAG.
  Qed.

End PROD.

Section COPROD.

  Variable C : Type.
  Variable (F G : (C -> Type) -> Type).
  Context `{SPF_F : SPFunctor _ F}.
  Context `{SPF_G : SPFunctor _ G}.

  Program Instance Coprod_SPF : SPFunctor (Coprod F G) := 
    @Build_SPFunctor _ _ (@Coprod_Functor _ F G Fn Fn) _ _
                     (Transitive_NatIso
                        (@Coprod_Iso _ _ _ _ _ _ _ _ _ (ISO SPF_F) (ISO SPF_G))
                        (Coprod_Container (P F) (P G))) _.
  Next Obligation.
    destruct fx; f_equal; apply TAG.
  Qed.

End COPROD.

Section DEP_FUN.

  Variable C A : Type.
  Variable (B: A -> (C -> Type) -> Type).
  Context `{SPF_F : forall (a : A), SPFunctor (B a)}.

  Program Instance Dep_fun_SPF : SPFunctor (Dep_fun B) := 
    @Build_SPFunctor _ _ (@Dep_fun_Functor _ _ B (fun a => Fn)) _ _
                     (Transitive_NatIso
                        (@Dep_Fun_Iso _ _ _ _ _ _ (fun a => ISO (SPF_F a)))
                        (Dep_Fun_Container _ (fun a : A => P (B a))))_.
  Next Obligation.
    extensionality a. rewrite MAP_COMPOSE. apply TAG.
  Qed.

End DEP_FUN.

Section DEP_SUM.

  Variable C A : Type.
  Variable (B: A -> (C -> Type) -> Type).
  Context `{SPF_F : forall (a : A), SPFunctor (B a)}.

  Program Instance Dep_sum_SPF : SPFunctor (Dep_sum B) := 
    @Build_SPFunctor _ _ (@Dep_sum_Functor _ _ B (fun a => Fn)) _ _
                     (Transitive_NatIso
                        (@Dep_sum_Iso _ _ _ _ _ _ (fun a => ISO (SPF_F a)))
                        (Dep_Sum_Container _ (fun a : A => P (B a))))_.
  Next Obligation.
    rewrite sigT_eta. f_equal. apply TAG.
  Qed.

End DEP_SUM.

Section COMP.

  Variable C1 C2 : Type.
  Variable F1 : C2 -> (C1 -> Type) -> Type.
  Variable F2 : (C2 -> Type) -> Type.

  Context `{SPF_F2 : SPFunctor _ F2}.
  Context `{SPF_F1 : forall (i : C2), SPFunctor (F1 i)}.

  Program Instance Comp_SPF : SPFunctor (Comp F1 F2) := 
    @Build_SPFunctor _ _ (@Comp_Functor _ _ _ _ Fn (fun i => Fn)) _ _ 
                     (Transitive_NatIso (Transitive_NatIso
                                           (@Comp_Iso1 _ _ F1 _ _ _ _ _ (ISO SPF_F2))
                                           (@Comp_Iso2 _ _ F1 _ _ (P F2) _ _
                                                       (fun i => ISO (SPF_F1 i))))
                                        (Comp_Container _ (fun i => P (F1 i)) (P F2))) _.
  Next Obligation.
    repeat rewrite MAP_COMPOSE. unfold Comp in *.
    rewrite <- TAG. f_equal.
    extensionality i. extensionality x.
    rewrite MAP_COMPOSE. apply TAG.
  Qed.

End COMP.

Section EXPN.

  Variable C D : Type.
  Variable F : (C -> Type) -> Type.
  Context `{SPFunctor _ F}.

  Definition Expn (X : C -> Type) := (D -> F X).

  Definition Expn_Functor : Functor Expn := Dep_fun_Functor (fun d : D => F).

  Definition Expn_SPF : SPFunctor Expn := Dep_fun_SPF (fun d : D => F).

End EXPN.

Section SUBST.

  Variable C0 C : Type.
  Variable (F : (C0 + C -> Type) -> Type).
  Variable T : (C0 -> Type).

  Context `{SPFunctor _ F}.

  Definition Subst := (Comp (fun (i : C0 + C) =>
                               match i with
                               | inl c0 => @Const C (T c0) 
                               | inr c => @Ident C c
                               end) F).

  Definition Subst_SPFunctor : SPFunctor Subst := 
    @Comp_SPF _ _ _ _ _
              (fun i : C0 + C =>
                 match i with
                 | inl c => Const_SPF C (T c)
                 | inr c => Ident_SPF c
                 end).

End SUBST.  

Section DEPEND.

  Variable A B : Type.
  Variable f : A -> B.
  Variable (F : A -> (B -> Type) -> Type).
  Context `{forall a, SPFunctor (F a)}.

  Definition Depend (b : B) (X : B -> Type) :=
    sigT (fun a : A => ((F a X) * (f a = b))%type).

  Definition Depend_SPFunctor (b : B) : SPFunctor (Depend b) :=
    @Dep_sum_SPF _ _ _ (fun a => @Prod_SPF _ _ _ _ (Const_SPF B ((f a) = b))).

End DEPEND.

