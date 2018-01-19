Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor icombinator.

(* Ident *)

Definition Ident C (i : C) (X : C -> Type) := X i.

Goal True. constructor. Qed.

Inductive Ident_eq C (i : C) (X : C -> Type) (x : Ident i X) :
  forall i, X i -> Prop :=
| Ident_eq_refl : Ident_eq i X x i x.

Program Definition Ident_Functor C (i : C) : Functor (Ident i)
  := Build_Functor _ (fun _ _ f => f i) (Ident_eq i) (fun _ _ R => @R i)
                   (fun X fx => existI fx (Ident_eq_refl _ _ fx)) _.

Program Instance Ident_SPF C (i : C) : SPFunctor (Ident i)
  := @Build_SPFunctor _ _ (Ident_Functor i) unit (fun _ j => i = j)
                      (Build_NatIso _ _
                                    (fun X fx =>
                                       (existT _ tt
                                               (fun j EQ => eq_rect i X fx j EQ)))
                                    (fun X gx => projT2 gx i eq_refl)
                                    _ _ _ _ _).
Next Obligation.
  compute. f_equal.
  extensionality i0. extensionality e.
  destruct e. reflexivity.
Qed.
Next Obligation.
  split; intros.
  - destruct H.
    eapply (Container_mem _ _ tt i eq_refl).
  - inversion H. subst.
    constructor.
Qed.
Next Obligation.
  split; intros.
  - apply Container_rel.
    intros. destruct p. apply H.
  - inversion H. subst.
    specialize (H1 i eq_refl). apply H1.
Qed.
Next Obligation.
  compute. destruct gx. f_equal.
  - destruct x. reflexivity.
  - extensionality i0. extensionality e.
    destruct e. reflexivity.
Qed.

(* Const *)

Definition Const C (D : Type) (X : C -> Type) := D.

Program Definition Const_Functor C D : Functor (@Const C D)
  := Build_Functor _ (fun _ _ _ fx => fx) (fun _ _ _ _ => False) (fun _ _ _ => eq)
                   (fun _ => id) _.

Program Instance Const_SPF C D : SPFunctor (@Const C D)
  := @Build_SPFunctor _ _ (Const_Functor C D) D (fun _ _ => False)
                      (Build_NatIso _ _
                                    (fun _ fx => existT _ fx (fun _ => False_rect _))
                                    (fun _ => @projT1 _ _) _ _ _ _ _).
Next Obligation.
  compute. f_equal.
  extensionality i. extensionality x. destruct x.
Qed.
Next Obligation.
  split; compute; intros.
  - destruct H.
  - destruct H. destruct p.
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

Section COPROD.

  Variable C : Type.
  Variable (F G : (C -> Type) -> Type).
  Context `{SPFunctor _ F}.
  Context `{SPFunctor _ G}.

  Definition Coprod (X : C -> Type) := (F X + G X)%type.

  Inductive Coprod_rel X Y (R : forall i : C, X i -> Y i -> Prop)
    : Coprod X -> Coprod Y -> Prop :=
  | coprod_rel_inl fx fy (REL : rel R fx fy) : Coprod_rel R (inl fx) (inl fy)
  | coprod_rel_inr gx gy (REL : rel R gx gy) : Coprod_rel R (inr gx) (inr gy)
  .

  Program Definition Coprod_Functor : Functor Coprod
    := Build_Functor _ (fun _ _ f x => match x with
                                       | inl fx => inl (map f fx)
                                       | inr gx => inr (map f gx) end)
                     (fun _ x => match x with
                                 | inl fx => @mem _ _ _ _ fx
                                 | inr gx => @mem _ _ _ _ gx end)
                     Coprod_rel
                     (fun _ fx => match fx with
                                  | inl f => inl (tag _ f)
                                  | inr g => inr (tag _ g)
                                  end)
                     _.
  Next Obligation.
    destruct fx; simpl; f_equal; apply TAG.
  Defined.
 
  Program Instance Coprod_SPF : SPFunctor Coprod
    := @Build_SPFunctor _ _ Coprod_Functor (S F + S G)%type
                        (fun s => match s with
                                  | inl sf => (P F) sf
                                  | inr sg => (P G) sg end)
                        (Build_NatIso _ _
                                      (fun _ fx =>
                                         match fx with
                                         | inl f =>
                                           existT _ (inl (projT1 (NT ISO f))) 
                                                  (projT2 (NT ISO f))
                                         | inr g =>
                                           existT _ (inr (projT1 (NT ISO g))) 
                                                  (projT2 (NT ISO g))
                                         end)
                                      (fun X fx =>
                                         match fx with
                                         | existT _ s p =>
                                           match s as s return
                                                 ((forall i : C,
                                                      match s as s' return (s' = s -> C -> Type) with
                                                      | inl sf =>
                                                        fun _ : inl sf = s => P F sf
                                                      | inr sg =>
                                                        fun _ : inr sg = s => P G sg
                                                      end eq_refl i -> X i)
                                                  -> Coprod X)
                                           with
                                           | inl s' =>
                                             fun f => inl (NTinv ISO (existT _ s' f))
                                           | inr s' =>
                                             fun f => inr (NTinv ISO (existT _ s' f))
                                           end p end) _ _ _ _ _).
  Next Obligation.
    destruct fx; simpl.
    - rewrite MAP_COMMUTE. simpl.
      unfold container_map.
      destruct (NT _ f0). reflexivity.
    - rewrite MAP_COMMUTE. simpl.
      unfold container_map.
      destruct (NT _ g). reflexivity.
  Qed.
  Next Obligation.
    destruct fx; split; intros.
    - apply MEM_COMMUTE in H1. inversion H1. apply Container_mem.
    - apply MEM_COMMUTE. simpl in *. destruct (NT _ f).
      apply CONTAINER_MEM in H1. apply CONTAINER_MEM.
      destruct H1. exists x2. apply H1.
    - apply MEM_COMMUTE in H1. inversion H1. apply Container_mem.
    - apply MEM_COMMUTE. simpl in *. destruct (NT _ g).
      apply CONTAINER_MEM in H1. apply CONTAINER_MEM.
      destruct H1. exists x2. apply H1.
  Qed.
  Next Obligation.
    split; intros. 
    - destruct H1; apply REL_COMMUTE in REL; simpl in *;
        destruct (NT _ _), (NT _ _);
      apply CONTAINER_REL2 in REL;
      destruct REL; subst; constructor; auto.
    - destruct fx, fy; try (constructor; apply REL_COMMUTE); simpl in *;
        destruct (NT ISO _), (NT ISO _);
      apply CONTAINER_REL2 in H1; destruct H1;
      inversion x2; subst;
        apply Container_rel; intros;
      specialize (H1 i p);
      rewrite <- eq_rect_eq in H1; auto. (* axiom K *)
  Qed.    
  Next Obligation.
    destruct fx; f_equal; destruct (NT ISO _) eqn : EQ; simpl;
    rewrite <- EQ; apply BIJECTION1.
  Qed.
  Next Obligation.
    destruct gx as [[sf | sg] f]; simpl; rewrite BIJECTION2; auto.
  Qed.

End COPROD.
     
Section PROD.

  Variable C : Type.
  Variable (F G : (C -> Type) -> Type).
  Context `{SPFunctor _ F}.
  Context `{SPFunctor _ G}.

  Definition Prod (X : C -> Type) := (F X * G X)%type.

  Program Definition Prod_Functor : Functor Prod
    := Build_Functor _ (fun _ _ f x => match x with
                                       | (fx, gx) => (map f fx, map f gx)
                                       end)
                     (fun _ x _ a => match x with
                                     | (fx, gx) => mem fx a \/ mem gx a end)
                     (fun _ _ R x y =>
                        match x, y with
                        | (fx, gx), (fy, gy) => rel R fx fy /\ rel R gx gy end)
                     (fun X fx =>
                        let
                          (f, g) as p
                          return
                          (Prod
                             (sigI
                                (fun (i : C) (a : X i) =>
                                   (let (fx0, gx) as x' return (x' = p -> Prop) := p in
                                    fun _ : (fx0, gx) = p => mem fx0 a \/ mem gx a) eq_refl))) := fx in
                        (map (sigImply _ (fun i x => @or_introl _ _)) (tag X f),
                         map (sigImply _ (fun i x => @or_intror _ _)) (tag X g))) _.
  Next Obligation.
    destruct fx.
    repeat rewrite MAP_COMPOSE. f_equal; rewrite <- TAG; f_equal;
      extensionality i; extensionality x;
      symmetry; apply sigImply_proj1.
  Qed.
  
  Program Instance Prod_SPF : SPFunctor Prod
  := @Build_SPFunctor _ _ Prod_Functor (S F * S G)%type
                      (fun s i => match s with
                                  | (sf, sg) => ((P F) sf i + (P G) sg i)%type
                                  end)
                      (Build_NatIso _ _
                                    (fun X fx =>
                                       match fx with
                                       | (f, g) =>
                                         existT _
                                                (projT1 (NT _ f), projT1 (NT _ g))
                                                (fun _ p =>
                                                   match p with
                                                   | inl p' => projT2 (NT ISO f) _ p'
                                                   | inr p' => projT2 (NT ISO g) _ p'
                                                   end) end)
                                    _ _ _ _ _ _).
  Next Obligation.
    destruct X0. destruct x. apply pair; apply (NTinv ISO).
    - exists s. intros. apply (x0 _ (inl X0)).
    - exists s0. intros. apply (x0 _ (inr X0)).
  Defined.
  Next Obligation.
    destruct fx; simpl. unfold container_map.
    repeat rewrite MAP_COMMUTE. simpl.
    destruct (NT _ f0), (NT _ g). simpl. f_equal.
    extensionality i. extensionality p.
    destruct p; reflexivity.
  Qed.
  Next Obligation.
    destruct fx; split; intros.
    - destruct H1; apply MEM_COMMUTE in H1; simpl in *;
      destruct (NT _ f), (NT _ g);
      apply CONTAINER_MEM in H1; apply CONTAINER_MEM; destruct H1.
      + exists (inl x4); auto.
      + exists (inr x4); auto.
    - repeat rewrite MEM_COMMUTE. simpl in *. destruct (NT _ f), (NT _ g).
      apply CONTAINER_MEM in H1. destruct H1. destruct x4;
      [left | right]; apply CONTAINER_MEM; exists p; apply H1.
  Qed.
  Next Obligation.
    split; intros. 
    - destruct fx, fy. destruct H1.
      apply REL_COMMUTE in H1. apply REL_COMMUTE in H2. simpl in *.
      destruct (NT _ f), (NT _ g), (NT _ f0), (NT _ g0).
      apply CONTAINER_REL2 in H1. destruct H1.
      apply CONTAINER_REL2 in H2. destruct H2.
      subst. apply Container_rel.
      simpl in *. destruct p; auto.
    - destruct fx, fy. repeat rewrite REL_COMMUTE. simpl in *.
      destruct (NT _ f), (NT _ f0), (NT _ g), (NT _ g0).

      apply CONTAINER_REL2 in H1. destruct H1. inversion x5. subst.
      rewrite <- eq_rect_eq in H1. (* axiom k *)
      split; apply Container_rel; intros.
      + apply (H1 _ (inl p)).
      + apply (H1 _ (inr p)).
  Qed.    
  Next Obligation.
    destruct fx. simpl.
    destruct (NT _ f) eqn : EQ1.
    destruct (NT _ g) eqn : EQ2. simpl.
    f_equal; rewrite <- BIJECTION1; [rewrite EQ1 | rewrite EQ2]; f_equal.
  Qed.
  Next Obligation.
    destruct gx. destruct x. simpl. repeat rewrite BIJECTION2.
    f_equal. extensionality i. extensionality X0.
    destruct X0; reflexivity.
  Qed.

End PROD.

Section DEP_SUM.

  Variable C A : Type.
  Variable (B : A -> (C -> Type) -> Type).
  Context `{forall (a : A), SPFunctor (B a)}.

  Definition Dep_sum (X : C -> Type) := sigT (fun a => B a X).

  Inductive Dep_sum_rel X Y (R : forall i : C, X i -> Y i -> Prop)
    : Dep_sum X -> Dep_sum Y -> Prop :=
  | dep_sum_rel a (fx : B a X) (fy : B a Y) (REL : rel R fx fy) :
      Dep_sum_rel R (existT _ a fx) (existT _ a fy)
  .

  Goal True. auto. Qed.

  Program Definition Dep_sum_Functor : Functor Dep_sum
    := Build_Functor Dep_sum
                     (fun _ _ f fx => existT _ (projT1 fx) (map f (projT2 fx)))
                     (fun _ fx => @mem _ _ _ _ (projT2 fx))
                     Dep_sum_rel
                     (fun _ fx => existT _ (projT1 fx) (tag _ (projT2 fx)))
                     _.
  Next Obligation.
    destruct fx. simpl. f_equal. apply TAG.
  Qed.
 
  Program Instance Dep_sum_SPF : SPFunctor Dep_sum
    := @Build_SPFunctor _ _ Dep_sum_Functor (sigT (fun a => S (B a)))
                        (fun s => P (B (projT1 s)) (projT2 s))
                        (Build_NatIso _ _
                                      _
                                      _ _ _ _ _ _).
  Next Obligation.
    exists (existT _ (projT1 X0) (projT1 (@NT _ _ _ _ _ ISO X (projT2 X0)))).
    apply (projT2 (@NT _ _ _ _ _ ISO X (projT2 X0))).
  Defined.
  Next Obligation.
    destruct X0. destruct x.
    exists x. apply (NTinv ISO).
    exists s. apply x0.
  Defined.
  Next Obligation.
    unfold Dep_sum_SPF_obligation_1, container_map. 
    destruct fx. simpl. rewrite MAP_COMMUTE. simpl. f_equal.
  Qed.
  Next Obligation.
    unfold Dep_sum_SPF_obligation_1; destruct fx; simpl; split; intros.
    - apply MEM_COMMUTE in H0. destruct (NT _ b). simpl in H0.
      apply CONTAINER_MEM in H0. apply CONTAINER_MEM.
      destruct H0. exists x3. apply H0.
    - apply MEM_COMMUTE. destruct (NT _ b). simpl.
      apply CONTAINER_MEM in H0. destruct H0.
      apply CONTAINER_MEM.
      exists x3. apply H0.
  Qed.
  Next Obligation.
    unfold Dep_sum_SPF_obligation_1; destruct fx, fy; split; intros.
    - destruct H0. apply REL_COMMUTE in REL. simpl.
      destruct (NT _ fx), (NT _ fy). simpl in *.
      
      apply CONTAINER_REL2 in REL. destruct REL.
      subst. simpl in *. apply Container_rel. apply H0.
    - simpl in *. 
      apply CONTAINER_REL2 in H0. destruct H0. inversion x1. subst. constructor.
      apply REL_COMMUTE. destruct (NT _ b0), (NT _ b). simpl in *.
      apply inj_pair2 in H3. subst. constructor. (* axiom k *)
      intros. specialize (H0 i p). rewrite <- eq_rect_eq in H0. (* axiom k*)
      apply H0.
  Qed.
  Next Obligation.
    destruct fx. simpl. destruct (NT _ b) eqn : EQ. simpl.
    f_equal. rewrite <- EQ. apply BIJECTION1.
  Qed.
  Next Obligation.
    unfold Dep_sum_SPF_obligation_1, Dep_sum_SPF_obligation_2.
    destruct gx. destruct x. simpl in *. rewrite BIJECTION2. reflexivity.
  Qed.

End DEP_SUM.

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

  Program Definition Subst_SPFunctor : SPFunctor Subst.
    apply Comp_SPF.
    - apply H.
    - intro. destruct i.
      + apply Const_SPF.
      + apply Ident_SPF.
  Defined.

(*
  Arguments map {C} F {Functor X Y}.


  Definition maybe (X : C -> Type) :=
    (fun i => match i with
              | inl c0 => T c0
              | inr c => X c
              end). 

  Definition Subst (X : C -> Type) :=
    F (maybe X).

  Program Definition Subst_Functor : Functor Subst
    := Build_Functor _ _ (fun X fx i => @mem _ _ _ (maybe X) fx (inr i)) _ _ _.
  Next Obligation.
    eapply (map F _ X0).
    Unshelve.
    intro. destruct i.
    - apply id.
    - apply (f c).
  Defined.
  Next Obligation.
    set (@rel _ F _ (maybe X) (maybe Y)).
    eapply (P _ fx fy).
    Unshelve.
    intro. destruct i.
    - apply eq.
    - apply R.
  Defined.
  Next Obligation.
    unfold Subst in *.
    set (tag _ fx). simpl in *.
    eapply (map _ _ f). Unshelve.
    intros. destruct X0. destruct i.
    - apply x.
    - simpl in *.
      apply (existI x). apply m.
  Defined.
  Next Obligation.
    unfold Subst_Functor_obligation_1, Subst_Functor_obligation_2, Subst_Functor_obligation_3. simpl.
    rewrite MAP_COMPOSE. rewrite <- (@TAG _ F _ _ fx) at 3.
    f_equal. extensionality i. extensionality x.
    destruct x. destruct i; reflexivity.
  Qed.
 
  Program Instance Subst_SPF : SPFunctor Subst
    := @Build_SPFunctor _ _ Subst_Functor (S F + S G)%type
                        (fun s => match s with
                                  | inl sf => (P F) sf
                                  | inr sg => (P G) sg end)
                        (Build_NatIso _ _
                                      (fun _ fx =>
                                         match fx with
                                         | inl f =>
                                           existT _ (inl (projT1 (NT ISO f))) 
                                                  (projT2 (NT ISO f))
                                         | inr g =>
                                           existT _ (inr (projT1 (NT ISO g))) 
                                                  (projT2 (NT ISO g))
                                         end)
                                      (fun X fx =>
                                         match fx with
                                         | existT _ s p =>
                                           match s as s return
                                                 ((forall i : C,
                                                      match s as s' return (s' = s -> C -> Type) with
                                                      | inl sf =>
                                                        fun _ : inl sf = s => P F sf
                                                      | inr sg =>
                                                        fun _ : inr sg = s => P G sg
                                                      end eq_refl i -> X i)
                                                  -> Coprod X)
                                           with
                                           | inl s' =>
                                             fun f => inl (NTinv ISO (existT _ s' f))
                                           | inr s' =>
                                             fun f => inr (NTinv ISO (existT _ s' f))
                                           end p end) _ _ _ _ _).
  Next Obligation.

*)

End SUBST.  

Section DEPEND.

  Variable A B : Type.
  Variable f : A -> B.
  Variable (F : A -> (B -> Type) -> Type).
  Context `{forall a, SPFunctor (F a)}.

  Definition Depend (b : B) (X : B -> Type) :=
    sigT (fun a : A => ((F a X) + (f a = b))%type).

  Definition Depend_SPFunctor (b : B) : SPFunctor (Depend b).
    apply Dep_sum_SPF.
    intro.
    apply Coprod_SPF.
    - apply H.
    - apply Const_SPF.
  Defined.

End DEPEND.
