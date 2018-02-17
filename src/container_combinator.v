Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor hott iso.

Arguments S {C} F {SPFunctor}.
Arguments P {C} F {SPFunctor}.
Arguments NT {C F G H H0} NatIso {X} f.
Arguments NTinv {C F G H H0} NatIso {X} f.

Section DEP_FUN_CONTAINER.

  Variable C A : Type.
  Variable BS : A -> Type.
  Variable BP : forall a, (BS a) -> C -> Type.

  Program Definition Dep_Fun_Container
    : @NatIso C _ _
              (Dep_fun_Functor (fun a => Container (@BP a)))
              (Functor_Container (fun f i => sigT (fun a => BP (f a) i)))
    :=
      Build_NatIso _ _
                   (fun X fx => existT _ (fun a => projT1 (fx a))
                                       (fun i x => projT2 (fx (projT1 x)) i (projT2 x))) (fun X fx a => existT _ (projT1 fx a)
                                                                                                               (fun i x => projT2 fx i (existT _ a x))) _ _ _ _ _.
  Next Obligation.
    split; intro.
    - destruct H as [a [p EQ]]. 
      exists (existT _ a p). apply EQ.
    - destruct H as [[a p] EQ].
      exists a. exists p. apply EQ.
  Qed.
  Next Obligation. 
    split; intro. - giveup.

    - apply CONTAINER_REL2 in H. destruct H. simpl in *.
      intro. apply CONTAINER_REL2.
 
      exists (eqext _ x a). intros.

      specialize (H i (existT _ a p)). simpl in *.

      set (eq_rect_fun3 _ x). simpl in *. giveup.
  Qed.
  Next Obligation.
    extensionality a. symmetry. apply sigT_eta.
  Qed.
  Next Obligation.
    rewrite sigT_eta. f_equal.
    extensionality i. extensionality x.
    f_equal. symmetry. apply sigT_eta.
  Qed.

End DEP_FUN_CONTAINER.

Section COPROD_CONTAINER.

  Variable C : Type.
  Variable S1 S2 : Type.
  Variable P1 : S1 -> C -> Type.
  Variable P2 : S2 -> C -> Type.

  Program Instance Coprod_Container
    : @NatIso _ _ _ (@Coprod_Functor _ (Container P1) (Container P2) _ _ )
              (Functor_Container (sum_rect _ P1 P2)) :=
    Build_NatIso _ _
                 (fun X x => match x return (Container (sum_rect _ P1 P2) X) with
                             | inl fx => existT _ (inl (projT1 fx)) (projT2 fx)
                             | inr gx => existT _ (inr (projT1 gx)) (projT2 gx)
                             end)
                 (fun X fx => match (projT1 fx) as s' return
                                    ((forall i, (sum_rect (fun _ => C -> Type) P1 P2 s') i -> X i)
                                     -> Container P1 X + Container P2 X) with
                              | inl s => 
                                fun x => inl (existT _ s x)
                              | inr s =>
                                fun x => inr (existT _ s x)
                              end (projT2 fx)) _ _ _ _ _.
  Next Obligation.
    destruct fx; reflexivity.
  Qed.
  Next Obligation.
    destruct fx; reflexivity.
  Qed.
  Next Obligation.
    split; intro.
    - destruct fx, fy, H; constructor; apply H.
    - destruct fx, fy; try (inversion H; fail);
        apply CONTAINER_REL2; apply CONTAINER_REL2 in H; destruct H; simpl in *.
      + rewrite <- ((sum_eq_inl (projT1 c0) (inl (projT1 c))).(bij1) x) in H.
        simpl in *. exists (sum_eq_inl1 x). destruct c. simpl in *.
        destruct (sum_eq_inl1 x). apply H.
      + rewrite <- ((sum_eq_inr (projT1 c0) (inr (projT1 c))).(bij1) x) in H.
        simpl in *. exists (sum_eq_inr1 x). destruct c. simpl in *.
        destruct (sum_eq_inr1 x). apply H.
  Qed.
  Next Obligation.
    destruct fx; simpl; f_equal; symmetry; apply sigT_eta.
  Qed.
  Next Obligation.
    destruct gx. destruct x; reflexivity.
  Qed.

End COPROD_CONTAINER.
     
Section PROD_CONTAINER.

  Variable C : Type.
  Variable S1 S2 : Type.
  Variable P1 : S1 -> C -> Type.
  Variable P2 : S2 -> C -> Type.

  Program Instance Prod_Container
    : @NatIso _ _ _ (@Prod_Functor _ (Container P1) (Container P2) _ _ )
              (Functor_Container (fun s i => (P1 (fst s) i + P2 (snd s) i)%type)) :=
    Build_NatIso _ _
                 (fun X fx => existT _ (projT1 (fst fx), projT1 (snd fx))
                                     (fun i => sum_rect _ (projT2 (fst fx) i)
                                                        (projT2 (snd fx) i)))
                 (fun X fx => (existT _ (fst (projT1 fx))
                                      (fun i p => projT2 fx i (inl p)),
                               existT _ (snd (projT1 fx))
                                      (fun i p => projT2 fx i (inr p))))
                 _ _ _ _ _.
  Next Obligation.
    unfold sigTimply. simpl. f_equal.
    extensionality i. extensionality p. destruct p; reflexivity.
  Qed.
  Next Obligation.
    split; intro.
    - destruct H; destruct H as [p EQ]; destruct EQ;
        [exists (inl p) | exists (inr p)]; reflexivity.
    - destruct H; destruct x0; simpl in *; [left | right]; rewrite <- H;
        exists p; reflexivity.
  Qed.
  Next Obligation.
    split; intro.
    - destruct H. destruct H, H0. simpl in *. constructor.
      intros. destruct p; [apply H | apply H0].

    - apply CONTAINER_REL2 in H; destruct H. split; apply CONTAINER_REL2.
      simpl in *.

      exists (f_equal fst x). intros.
      specialize (H i (inl p)). simpl in *. giveup. giveup.
  Qed.
  Next Obligation.
    rewrite surjective_pairing. f_equal; rewrite sigT_eta; f_equal.
  Qed.
  Next Obligation.
    destruct gx as [[s1 s2] f]. simpl in *. f_equal.
    extensionality i. extensionality p. destruct p; reflexivity.
  Qed.

End PROD_CONTAINER.

Section DEP_SUM_CONTAINER.

  Variable C A : Type.
  Variable BS : A -> Type.
  Variable BP : forall a, (BS a) -> C -> Type.

  Program Definition Dep_Sum_Container
    : @NatIso C _ _
              (Dep_sum_Functor (fun a => Container (@BP a)))
              (Functor_Container (fun (s : sigT BS) => BP (projT2 s)))
    :=
      Build_NatIso _ _
                   (fun X fx => existT _ (existT _ (projT1 fx) (projT1 (projT2 fx)))
                                       (projT2 (projT2 fx)))
                   (fun X fx => existT _ (projT1 (projT1 fx))
                                       (existT _ (projT2 (projT1 fx)) (projT2 fx)))
                   _ _ _ _ _.
  Next Obligation.
    split; apply id.
  Qed.
  Next Obligation.
    giveup.
  Qed.
  Next Obligation.
    rewrite sigT_eta. f_equal. symmetry. apply sigT_eta.
  Qed.
  Next Obligation.
    destruct gx as [[a s] f]; reflexivity.
  Qed.    

End DEP_SUM_CONTAINER.

Section COMP_CONTAINER.

  Variable C1 C2 : Type.
  
  Variable S1 : C2 -> Type.
  Variable P1 : forall c, S1 c -> C1 -> Type.

  Variable S2 : Type.
  Variable P2 : S2 -> C2 -> Type.

  Program Definition Comp_Container
    : @NatIso C1 _ _
              (@Comp_Functor _ _ (fun c => Container (@P1 c)) (Container P2) _ _)
              (Functor_Container (fun (s1 : sigT (fun s : S2 =>
                                 (forall (i : C2), P2 s i -> S1 i))) (j : C1) =>
                           sigT (fun (i : C2) => sigT (fun (p : P2 (projT1 s1) i) =>
                                                         P1 ((projT2 s1) i p) j))))
    :=
      Build_NatIso _ _ 
                   (fun X fx =>
                      existT _ (existT (fun s => forall i, P2 s i -> S1 i)
                                       (projT1 fx) (fun i p => projT1 (projT2 fx i p)))
                             (fun i p => projT2 (projT2 fx (projT1 p) (projT1 (projT2 p))) _
                                                (projT2 (projT2 p))))
                   (fun X fx =>
                      existT _ (projT1 (projT1 fx))
                             (fun i p1 => existT _ (projT2 (projT1 fx) i p1)
                                                 (fun j p2 => projT2 fx j (existT _ i
                                                                                  (existT _ p1 p2)))))
                   _ _ _ _ _.
  Next Obligation.
    split; intro.
    - destruct H as [j [fx0 [[p1 EQ1] [p2 EQ2]]]]. subst.
      exists (existT _ j (existT _ p1 p2)). reflexivity.
    - destruct H as [[j [p1 p2]] EQ]. simpl in *. subst.
      exists j. exists (projT2 fx _ p1). split.
      + exists p1. reflexivity.
      + exists p2. reflexivity.
  Qed.
  Next Obligation.
    giveup.
  Qed.
  Next Obligation.
    rewrite sigT_eta. f_equal.
    extensionality i. extensionality p1. symmetry. apply sigT_eta.
  Qed.
  Next Obligation.
    destruct gx as [[s1 s2] f]. simpl.
    rewrite sigT_eta. f_equal.
    extensionality i. extensionality p. simpl. f_equal.
    rewrite sigT_eta. f_equal.
    symmetry. apply sigT_eta.
  Qed.

End COMP_CONTAINER.