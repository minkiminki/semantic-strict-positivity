Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor icombinator hott.

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
        assert (e : sig (fun (e' : x = x0) => f_equal inl e' = x2)). {          
          exists ((sum_eq_inl x (inl x0)).(fn1) x2).
          apply ((sum_eq_inl x (inl x0)).(bij1) x2).
        }
        destruct e. subst. exists eq_refl. apply H1.
      + inversion H1.
      + inversion H1.
      + constructor. apply REL_COMMUTE.
        apply CONTAINER_REL2. apply CONTAINER_REL2 in H1. simpl in *.
        destruct (NT ISO _), (NT ISO _). destruct H1. simpl in *.
        assert (e : sig (fun (e' : x = x0) => f_equal _ e' = x2)). {
          exists ((sum_eq_inr x (inr x0)).(fn1) x2).
          apply ((sum_eq_inr x (inr x0)).(bij1) x2).
        }
        destruct e. subst. exists eq_refl. apply H1.
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
    split; intros.
    - destruct H1. apply REL_COMMUTE in H1. apply REL_COMMUTE in H2.
      destruct H1. destruct H2. simpl.
      constructor. intros.
      destruct p; [apply H1 | apply H2].
    - assert (rel R (NT ISO (fst fx)) (NT ISO (fst fy)) /\
              rel R (NT ISO (snd fx)) (NT ISO (snd fy)));
        [ | split; apply REL_COMMUTE; tauto].
      destruct (NT ISO (fst fx)), (NT ISO (fst fy)),
      (NT ISO (snd fx)), (NT ISO (snd fy)).
      apply CONTAINER_REL2 in H1. destruct H1. simpl in *.
      
      revert x0 y x3 y0 H1.
      
      assert (forall (x0 : forall i : C, P F (fst (x, x2)) i -> X i) (y : forall i : C, P F (fst (x1, x4)) i -> Y i)
    (x3 : forall i : C, P G (snd (x, x2)) i -> X i) (y0 : forall i : C, P G (snd (x1, x4)) i -> Y i),
  (forall (i : C) (p : P F (fst (x, x2)) i + P G (snd (x, x2)) i),
   R i match p with
       | inl fp => x0 i fp
       | inr gp => x3 i gp
       end
     (eq_rect (x1, x4)
        (fun s : S F * S G =>
         forall i0 : C, P F (fst s) i0 + P G (snd s) i0 -> Y i0)
        (fun (i0 : C) (p0 : P F (fst (x1, x4)) i0 + P G (snd (x1, x4)) i0) =>
         match p0 with
         | inl fp => y i0 fp
         | inr gp => y0 i0 gp
         end) (x, x2) x5 i p)) ->
  container_rel R (existT (fun s : S F => forall i : C, P F s i -> X i) (fst (x, x2)) x0)
    (existT (fun s : S F => forall i : C, P F s i -> Y i) (fst (x1, x4)) y) /\
  container_rel R (existT (fun s : S G => forall i : C, P G s i -> X i) (snd (x, x2)) x3)
    (existT (fun s : S G => forall i : C, P G s i -> Y i) (snd (x1, x4)) y0)); auto.
      destruct x5. simpl. intros. 
      split; constructor; intros;
        [ apply (H1 i (inl p)) | apply (H1 i (inr p))].
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

  Lemma DEP_SUM_REL X Y (R : forall i : C, X i -> Y i -> Prop) x y :
    Dep_sum_rel R x y <-> exists (e : projT1 y = projT1 x),
      rel R (projT2 x) (eq_rect (projT1 y) (fun a => B a Y) (projT2 y) (projT1 x) e).
  Proof.
    split; intro.
    - inversion H0. exists eq_refl. apply REL.
    - destruct x, y. destruct H0. simpl in *. subst. constructor.
      apply H0.
  Qed.

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
  Next Obligation. 
    split; intro.
    - apply MEM_COMMUTE in H0. apply H0.
    - apply MEM_COMMUTE. apply H0.
  Qed.
  Next Obligation.
    split; intro. destruct H0. simpl. apply REL_COMMUTE in REL.
    - destruct (NT ISO fx), (NT ISO fy). simpl in *.   
      apply CONTAINER_REL in REL. destruct REL as [s [f1 [f2 [EQ1 [EQ2 REL]]]]].
      inversion EQ1. subst. inversion EQ2. subst.
      constructor. apply REL.
    - apply DEP_SUM_REL.

      assert (exists e : projT1 fy = projT1 fx,
                 rel R (NT ISO (projT2 fx))
                     (eq_rect (projT1 fy) (fun x => Container (P (B x)) Y)
                              (NT ISO (projT2 fy)) (projT1 fx) e)).
      
      +

        apply CONTAINER_REL2 in H0. simpl in *. destruct H0.

        rewrite <- ((sig_eq _ _).(bij1) x) in H0. simpl in *.
        remember (sig_eq1 x). clear x Heqs. simpl in *.
        destruct s.
        exists x. apply CONTAINER_REL2.

        assert (projT1
           (eq_rect (projT1 fy) (fun x0 : A => Container (P (B x0)) Y)
              (NT ISO (projT2 fy)) (projT1 fx) x) =
               eq_rect (projT1 fy) (fun a : A => S (B a)) (projT1 (NT ISO (projT2 fy)))
        (projT1 fx) x). {
          giveup.
        }
        exists (eq_trans H1 e).
        intros.

        specialize (H0 i p). 
        
        match goal with
        | [|- R i ?temp ?temp1] => replace temp1 with
              (eq_rect
            (existT (fun a : A => S (B a)) (projT1 fy) (projT1 (NT ISO (projT2 fy))))
            (fun s : {a : A & S (B a)} =>
             forall i : C, P (B (projT1 s)) (projT2 s) i -> Y i)
            (projT2 (NT ISO (projT2 fy)))
            (existT (fun a : A => S (B a)) (projT1 fx) (projT1 (NT ISO (projT2 fx))))
            (sig_eq2
               (existT (fun a : A => S (B a)) (projT1 fy) (projT1 (NT ISO (projT2 fy))))
               (existT (fun a : A => S (B a)) (projT1 fx) (projT1 (NT ISO (projT2 fx))))
               (existT
                  (fun e : projT1 fy = projT1 fx =>
                   eq_rect (projT1 fy) (fun a : A => S (B a))
                     (projT1 (NT ISO (projT2 fy))) (projT1 fx) e =
                   projT1 (NT ISO (projT2 fx))) x e)) i p) end; [apply H0|].

        clear H0. Opaque sig_eq2.
        repeat rewrite eq_rect_fun. 
        repeat rewrite eq_rect_fun2. simpl.
        giveup.
      + destruct H1. exists x. apply REL_COMMUTE.

        replace (NT ISO (eq_rect (projT1 fy) (fun a : A => B a Y) (projT2 fy) (projT1 fx) x)) with (eq_rect (projT1 fy) (fun x : A => Container (P (B x)) Y) 
            (NT ISO (projT2 fy)) (projT1 fx) x); [apply H1 | ].
        clear H0 H1. destruct x. reflexivity.
  Qed.
  Next Obligation. 
    rewrite sigT_eta. f_equal. rewrite <- sigT_eta. apply BIJECTION1.
  Qed.
  Next Obligation. 
    rewrite sigT_eta. rewrite BIJECTION2. simpl.
    destruct gx. destruct x. reflexivity.
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
