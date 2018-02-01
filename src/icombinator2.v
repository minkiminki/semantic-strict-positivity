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
    exists eq_refl. reflexivity.
  - destruct H. subst.
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
    := Build_Functor _ (fun X Y f x => match x return Coprod Y with
                                       | inl fx => inl (map f fx)
                                       | inr gx => inr (map f gx) end)
                     (fun X x => match x return (forall i, X i -> Prop) with
                                 | inl fx => @mem _ _ _ _ fx
                                 | inr gx => @mem _ _ _ _ gx end)
                     Coprod_rel
                     (fun X fx => match fx as fx' return
                                        (Coprod (sigI (_ X fx'))) with
                                  | inl f => inl (tag _ f)
                                  | inr g => inr (tag _ g)
                                  end)
                     _.
  Next Obligation.
    destruct fx; simpl; f_equal; apply TAG.
  Defined.
  
  Program Instance Coprod_SPF : SPFunctor Coprod
    := @Build_SPFunctor
         _ _ Coprod_Functor (S F + S G)%type
         (fun s => match s return (C -> Type) with
                   | inl sf => (P F) sf
                   | inr sg => (P G) sg end)
         (Build_NatIso _ _
                       (fun X fx =>
                          match fx return (Container _ X) with
                          | inl f =>
                            existT _ (inl (projT1 (NT ISO f))) 
                                   (projT2 (NT ISO f))
                          | inr g =>
                            existT _ (inr (projT1 (NT ISO g))) 
                                   (projT2 (NT ISO g))
                          end)
                       (fun X (fx : Container
                                      (fun s : S F + S G =>
                                         match s return (C -> Type) with
                                         | inl sf => P F sf
                                         | inr sg => P G sg
                                         end) X) =>
                          match projT1 fx as s
                                return ((forall i, match s return (C -> Type) with
                                                   | inl sf => P F sf
                                                   | inr sg => P G sg
                                                   end i -> X i) -> Coprod X)
                          with
                          | inl s' =>
                            fun x =>  inl (NTinv ISO (existT _ s' x))
                          | inr s' =>
                            fun x => inr (NTinv ISO (existT _ s' x))
                          end (projT2 fx)) _ _ _ _ _).
  Next Obligation.
    destruct fx; rewrite MAP_COMMUTE; reflexivity.
  Qed.
  Next Obligation.
    split; intros; destruct fx; simpl in *.
    - apply MEM_COMMUTE in H1. apply H1.
    - apply MEM_COMMUTE in H1. apply H1.
    - apply MEM_COMMUTE. apply H1.
    - apply MEM_COMMUTE. apply H1.
  Qed.
  Next Obligation.
    split; intros.
    - destruct H1; apply REL_COMMUTE in REL; apply CONTAINER_REL2 in REL;
        apply CONTAINER_REL2; destruct (NT ISO _), (NT ISO _); simpl in *;
          destruct REL; subst; exists eq_refl; apply H1.
    - destruct fx, fy.
      + constructor. apply REL_COMMUTE.
        apply CONTAINER_REL2. apply CONTAINER_REL2 in H1. simpl in *.
        destruct (NT ISO f0), (NT ISO f). destruct H1. simpl in *.
        giveup.
      + inversion H1.
      + inversion H1.
      + giveup.
  Qed.
  Next Obligation.
    destruct fx; simpl; f_equal;
    rewrite <- BIJECTION1; destruct (NT ISO _); reflexivity.
  Qed.
  Next Obligation.
    destruct gx; destruct x; simpl;
    rewrite BIJECTION2; reflexivity.
  Qed.

End COPROD.
     
Section PROD.

  Variable C : Type.
  Variable (F G : (C -> Type) -> Type).
  Context `{SPFunctor _ F}.
  Context `{SPFunctor _ G}.

  Definition Prod (X : C -> Type) := (F X * G X)%type.

  Program Definition Prod_Functor : Functor Prod
    := Build_Functor _ (fun X Y f x => (map f (fst x), map f (snd x)))
                     (fun X x _ a => (mem (fst x) a \/ mem (snd x) a))
                     (fun _ _ R x y => rel R (fst x) (fst y)/\ rel R (snd x) (snd y))
                     (fun X x => ((map (sigImply _ (fun i x => @or_introl _ _))
                                       (tag _ (fst x))),
                                  (map (sigImply _ (fun i x => @or_intror _ _))
                                       (tag _ (snd x))))) _.
  Next Obligation.
    repeat rewrite MAP_COMPOSE. destruct fx. f_equal;
    rewrite <- TAG; reflexivity.
  Qed.
  
  Program Instance Prod_SPF : SPFunctor Prod
    := @Build_SPFunctor
         _ _ Prod_Functor (S F * S G)%type
         (fun s i => ((P F) (fst s) i + (P G) (snd s) i)%type)
         (Build_NatIso _ _
                       (fun X x =>
                          existT _
                                 (projT1 (NT ISO (fst x)), projT1 (NT ISO (snd x)))
                                 (fun i p =>
                                    match p return X i with
                                    | inl fp => projT2 (NT ISO (fst x)) i fp
                                    | inr gp => projT2 (NT ISO (snd x)) i gp
                                    end))
                       (fun X x =>
                          (NTinv ISO (existT _ (fst (projT1 x))
                                             (fun i p => projT2 x i (inl p))),
                           NTinv ISO (existT _ (snd (projT1 x))
                                             (fun i p => projT2 x i (inr p)))))
                       _ _ _ _ _).
  Next Obligation.
    unfold sigTimply. simpl.
    repeat rewrite MAP_COMMUTE. f_equal.
    extensionality i. extensionality p.
    destruct p; reflexivity.
  Qed.
  Next Obligation. 
    split; intro.
    - destruct H1; apply MEM_COMMUTE in H1; destruct H1.
      + exists (inl x0). apply H1.
      + exists (inr x0). apply H1.
    - destruct H1. destruct x0; [left | right];
      apply MEM_COMMUTE; exists p; apply H1.
  Qed.
  Next Obligation. 
    giveup.
  Qed.
  Next Obligation.
    destruct fx.
    repeat rewrite <- sigT_eta. repeat rewrite BIJECTION1. reflexivity.
  Qed.
  Next Obligation.
    repeat rewrite BIJECTION2. simpl.
    destruct gx. destruct x. simpl. f_equal.
    extensionality i. extensionality p.
    destruct p; reflexivity.
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
    rewrite sigT_eta. f_equal. apply TAG.
  Qed.
 
  Program Instance Dep_sum_SPF : SPFunctor Dep_sum
    := @Build_SPFunctor
         _ _ Dep_sum_Functor (sigT (fun a => S (B a)))
         (fun s => P (B (projT1 s)) (projT2 s))
         (Build_NatIso _ _
                       (fun X fx =>
                          existT _ (existT _ (projT1 fx) (projT1 (NT ISO (projT2 fx))))
                                 (projT2 (NT ISO (projT2 fx))))
                       (fun X fx =>
                          existT _ (projT1 (projT1 fx))
                                 (NTinv ISO
                                        (existT _ (projT2 (projT1 fx)) (projT2 fx))))
                       _ _ _ _ _).
  Next Obligation.
    rewrite MAP_COMMUTE. reflexivity.
  Qed.
  Next Obligation. giveup. Qed.
  Next Obligation. giveup. Qed.
  Next Obligation. 
    rewrite sigT_eta. f_equal. rewrite <- sigT_eta. apply BIJECTION1.
  Qed.
  Next Obligation. 
    rewrite sigT_eta. rewrite BIJECTION2. simpl.
    destruct (projT1 gx).
    destruct gx. simpl. reflexivity.
    repeat rewrite <- sigT_eta.
    f_equal.
    - intros. simpl.
    rewrite sigT_eta. simpl.

giveup. Qed.
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
