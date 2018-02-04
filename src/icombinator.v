Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor hott.

Arguments S {C} F {SPFunctor}.
Arguments P {C} F {SPFunctor}.
Arguments NT {C F G H H0} NatIso {X} f.
Arguments NTinv {C F G H H0} NatIso {X} f.

Axiom GIVEUP : forall (A : Type), A.
Ltac giveup := apply GIVEUP.

Section DEP_FUN.

  Variable C A : Type.
  Variable (B: A -> (C -> Type) -> Type).
  Context `{forall (a : A), SPFunctor (B a)}.

  Definition Dep_fun (X : C -> Type) := forall a, B a X.

  Program Definition Dep_fun_Functor : Functor Dep_fun
    := Build_Functor
         Dep_fun
         (fun _ _ f fx a => map f (fx a)) 
         (fun _ fx _ x => ex (fun a => mem (fx a) x))
         (fun _ _ R fx fy => forall (a : A), rel R (fx a) (fy a))
         (fun _ fx =>
            fun a => (map (sigImply _ (fun i x (MEM: mem (fx a) x)
                                       => ex_intro _ a MEM)) (tag _ (fx a)))) _.
  Next Obligation.
    extensionality a. rewrite MAP_COMPOSE. apply TAG.
  Qed.

End DEP_FUN.

Section DEP_FUN_ISO.

  Variable C A : Type.
  Variable (B1 B2 : A -> (C -> Type) -> Type).
  Context `{forall (a : A), SPFunctor (B1 a)}.
  Context `{forall (a : A), SPFunctor (B2 a)}.

  Context `{forall (a : A), @NatIso _ (B1 a) (B2 a) _ _}.

  Program Definition Dep_Fun_Iso : @NatIso C _ _ (Dep_fun_Functor B1)
                                           (Dep_fun_Functor B2) :=
    Build_NatIso _ _
                 (fun X fx a => NT _ (fx a))
                 (fun X fx a => NTinv _ (fx a))
                 _ _ _ _ _.
  Next Obligation.
    extensionality a. apply MAP_COMMUTE.
  Qed.
  Next Obligation.
    split; intro; destruct H2; exists x0;
      apply (@MEM_COMMUTE _ _ _ _ _ (H1 x0)) in H2; apply H2.
  Qed.
  Next Obligation.
    split; intros; apply (@REL_COMMUTE _ _ _ _ _ (H1 a)); apply H2.
  Qed.
  Next Obligation.
    extensionality a. apply BIJECTION1.
  Qed.
  Next Obligation.
    extensionality a. apply BIJECTION2.
  Qed.

End DEP_FUN_ISO.

Section COMP.

  Variable C1 C2 : Type.
  Variable F1 : C2 -> (C1 -> Type) -> Type.
  Variable F2 : (C2 -> Type) -> Type.

  Context `{SPFunctor _ F2}.
  Context `{forall (i : C2), SPFunctor (F1 i)}.

  Arguments map {C} F {Functor X Y}.
  Arguments mem {C} F {Functor X} f {i} x.
  Arguments rel {C} F {Functor X Y} R fx fy.

  Definition Comp (X : C1 -> Type) := F2 (fun (i : C2) => F1 i X).

  Program Definition Comp_Functor : Functor Comp
    := Build_Functor
         Comp
         (fun _ _ f fx => map F2 (fun i x => map (F1 i) f x) fx)
         (fun X fxx i x => exists (j : C2) (fx : F1 j X),
              mem F2 fxx fx /\ mem (F1 j) fx x)
         (fun X Y R => rel F2 (fun (i : C2) => rel (F1 i) R))
         (fun X fx =>
            map F2 (fun i X0 => map (F1 i)
                       (fun i0 x1 =>
                          sigImply (fun i1 x => exists j fx0, mem F2 fx fx0 /\ mem (F1 j) fx0 x)
                                   (fun i1 x (MEM : mem (F1 i) (projI1 X0) x) =>
                                      ex_intro _ i (ex_intro _ (projI1 X0) (conj (projI2 X0) MEM))) x1)
                       (tag X (projI1 X0))) (tag (fun i : C2 => F1 i X) fx))
         _.
  Next Obligation.
    rewrite MAP_COMPOSE. unfold Comp in *.
    pattern fx at 20. rewrite <- (TAG _ fx).
    f_equal. extensionality i. extensionality x.
    rewrite MAP_COMPOSE. apply TAG.
  Qed.

End COMP.

Section COMP_ISO.

  Variable C1 C2 : Type.
  Variable F1 F1' : C2 -> (C1 -> Type) -> Type.
  Variable F2 F2' : (C2 -> Type) -> Type.

  Context `{SPFunctor _ F2}.
  Context `{SPFunctor _ F2'}.
  Context `{forall (i : C2), SPFunctor (F1 i)}.
  Context `{forall (i : C2), SPFunctor (F1' i)}.

  Arguments map {C} F {Functor X Y}.
  Arguments mem {C} F {Functor X} f {i} x.
  Arguments rel {C} F {Functor X Y} R fx fy.
  
  Context `{@NatIso _ F2 F2' _ _}.
  Context `{forall (i : C2), @NatIso _ (F1 i) (F1' i) _ _}.

  Program Definition Comp_Iso : @NatIso C1 _ _
                                        (@Comp_Functor _ _ F1 F2 _ _)
                                        (@Comp_Functor _ _ F1' F2' _ _) :=
    Build_NatIso _ _ 
                 (fun X fx => NT H3 (map F2 (fun i => NT (H4 i)) fx))
                 (fun X fx => NTinv H3 (map F2' (fun i => NTinv (H4 i)) fx))
                 _ _ _ _ _.
  Next Obligation.
    repeat rewrite MAP_COMMUTE. repeat rewrite MAP_COMPOSE. f_equal.
    extensionality i. extensionality x. apply MAP_COMMUTE.
  Qed.    
  Next Obligation.    
    split; intro.
    - destruct H5 as [h [fx0 [H5 H6]]]. exists h. exists (NT _ fx0). split. 
      + apply (@MEM_COMMUTE _ _ _ _ _ H3).
        apply (MEM_MAP _ _ (fun i0 : C2 => NT (H4 i0)) _ _ _ H5).
      + apply (@MEM_COMMUTE _ _ _ _ _ (H4 h)). apply H6.
    -  destruct H5 as [j [fx0 [H5 H6]]]. exists j. exists (NTinv _ fx0). split.
      + apply (@MEM_COMMUTE _ _ _ _ _ H3) in H5.
        apply (MEM_MAP _ _ (fun i0 : C2 => NTinv (H4 i0))) in H5.
        rewrite MAP_COMPOSE in H5. unfold Comp in *.
        rewrite <- (MAP_ID _ fx).
        replace (fun (i0 : C2) (x0 : F1 i0 X) => x0) with
            (fun (i : C2) (x : F1 i X) => NTinv (H4 i) (NT (H4 i) x)); [apply H5|].
        extensionality i0. extensionality x0. apply BIJECTION1.
      + apply (@MEM_COMMUTE _ _ _ _ _ (H4 j)). rewrite BIJECTION2. apply H6.
  Qed.
  Next Obligation.
    split; intro. 
    - apply (@REL_COMMUTE _ _ _ _ _ H3). apply MAP_REL.
      apply (REL_EQ _ _ _ _ (fun (i : C2) => @REL_COMMUTE _ _ _ _ _ (H4 i) _ _ R)). 
      apply H5.
    - apply (@REL_COMMUTE _ _ _ _ _ H3) in H5. apply MAP_REL in H5.
      apply (REL_EQ _ _ _ _ (fun (i : C2) => @REL_COMMUTE _ _ _ _ _ (H4 i) _ _ R)). 
      apply H5.
  Qed.
  Next Obligation.
    rewrite MAP_COMMUTE. rewrite MAP_COMPOSE.
    replace (fun (i : C2) (x : F1 i X) => NTinv (H4 i) (NT (H4 i) x)) with
        (fun (i : C2) (x : F1 i X) => x).
    - rewrite MAP_ID. apply (@BIJECTION1 _ _ _ _ _ H3).
    - extensionality i. extensionality x. symmetry. apply BIJECTION1.
  Qed.
  Next Obligation.
    rewrite <- MAP_COMMUTE_R. rewrite MAP_COMPOSE.
    replace (fun (i : C2) (x : F1' i X) => NT (H4 i) (NTinv (H4 i) x)) with
        (fun (i : C2) (x : F1' i X) => x).
    - rewrite MAP_ID. apply (@BIJECTION2 _ _ _ _ _ H3).
    - extensionality i. extensionality x. symmetry. apply BIJECTION2.
  Qed.

End COMP_ISO.

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
                     (fun X Y R x y =>
                        match x return Prop with
                        | inl fx =>
                          match y return Prop with
                          | inl fy => rel R fx fy
                          | inr gy => False end
                        | inr gx =>
                          match y return Prop with
                          | inl fy => False
                          | inr gy => rel R gx gy end
                        end)
                     (fun X fx => match fx as fx' return
                                        (Coprod (sigI (_ X fx'))) with
                                  | inl f => inl (tag _ f)
                                  | inr g => inr (tag _ g)
                                  end)
                     _.
  Next Obligation.
    destruct fx; simpl; f_equal; apply TAG.
  Defined.

End COPROD.

Section COPROD_ISO.

  Variable C : Type.
  Variable (F1 G1 F2 G2 : (C -> Type) -> Type).
  Context `{SPFunctor _ F1}.
  Context `{SPFunctor _ G1}.
  Context `{SPFunctor _ F2}.
  Context `{SPFunctor _ G2}.

  Context `{@NatIso _ F1 F2 _ _}.
  Context `{@NatIso _ G1 G2 _ _}.

  Program Instance Coprod_Iso : @NatIso _ _ _ (@Coprod_Functor _ F1 G1 _ _ )
                                        (@Coprod_Functor _ F2 G2 _ _) :=
    Build_NatIso _ _ 
                 (fun X x => match x return (Coprod F2 G2 X) with
                             | inl fx => inl (NT _ fx)
                             | inr gx => inr (NT _ gx)
                             end)
                 (fun X x => match x return (Coprod F1 G1 X) with
                             | inl fx => inl (NTinv _ fx)
                             | inr gx => inr (NTinv _ gx)
                             end) _ _ _ _ _.
  Next Obligation.
    destruct fx; f_equal; apply MAP_COMMUTE.
  Qed.
  Next Obligation.
    destruct fx; apply MEM_COMMUTE.
  Qed.
  Next Obligation.
    destruct fx, fy; try reflexivity; apply REL_COMMUTE.
  Qed.
  Next Obligation.
    destruct fx; f_equal; apply BIJECTION1.
  Qed.
  Next Obligation.
    destruct gx; f_equal; apply BIJECTION2.
  Qed.

End COPROD_ISO.
     
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

End PROD.

Section PROD_ISO.

  Variable C : Type.
  Variable (F1 G1 F2 G2 : (C -> Type) -> Type).
  Context `{SPFunctor _ F1}.
  Context `{SPFunctor _ G1}.
  Context `{SPFunctor _ F2}.
  Context `{SPFunctor _ G2}.

  Context `{@NatIso _ F1 F2 _ _}.
  Context `{@NatIso _ G1 G2 _ _}.

  Program Instance Prod_Iso : @NatIso _ _ _ (@Prod_Functor _ F1 G1 _ _)
                                      (@Prod_Functor _ F2 G2 _ _)
    := Build_NatIso _ _
                     (fun X x => (NT _ (fst x), NT _ (snd x)))
                     (fun X x => (NTinv _ (fst x), NTinv _ (snd x))) _ _ _ _ _.
  Next Obligation.
    f_equal; apply MAP_COMMUTE.
  Qed.
  Next Obligation.
    split; intro MEM; destruct MEM.
    - left. apply (@MEM_COMMUTE _ _ _ _ _ H3), H5.
    - right. apply (@MEM_COMMUTE _ _ _ _ _ H4), H5.
    - left. apply (@MEM_COMMUTE _ _ _ _ _ H3), H5.
    - right. apply (@MEM_COMMUTE _ _ _ _ _ H4), H5.
  Qed.
  Next Obligation.
    split; intro REL; destruct REL; split.
    - apply (@REL_COMMUTE _ _ _ _ _ H3), H5.
    - apply (@REL_COMMUTE _ _ _ _ _ H4), H6.
    - apply (@REL_COMMUTE _ _ _ _ _ H3), H5.
    - apply (@REL_COMMUTE _ _ _ _ _ H4), H6.
  Qed.
  Next Obligation.
    repeat rewrite BIJECTION1. symmetry. apply surjective_pairing.
  Qed.
  Next Obligation.
    repeat rewrite BIJECTION2. symmetry. apply surjective_pairing.
  Qed.

End PROD_ISO.

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

End DEP_SUM.

Section DEP_SUM_ISO.

  Variable C A : Type.
  Variable (B1 B2 : A -> (C -> Type) -> Type).
  Context `{forall (a : A), SPFunctor (B1 a)}.
  Context `{forall (a : A), SPFunctor (B2 a)}.

  Context `{forall (a : A), @NatIso _ (B1 a) (B2 a) _ _}.

  Program Definition Dep_sum_Iso : @NatIso _ _ _ (Dep_sum_Functor B1)
                                           (Dep_sum_Functor B2) :=
    Build_NatIso _ _
                 (fun X fx => existT _ (projT1 fx) (NT _ (projT2 fx)))
                 (fun X fx => existT _ (projT1 fx) (NTinv _ (projT2 fx))) _ _ _ _ _.
  Next Obligation.
    f_equal. apply MAP_COMMUTE.
  Qed.
  Next Obligation. 
    apply MEM_COMMUTE.
  Qed.
  Next Obligation.
    split; intro; apply DEP_SUM_REL in H2; apply DEP_SUM_REL;
      destruct H2 as [e REL]; exists e; simpl in *.
    - apply (@REL_COMMUTE _ _ _ _ _ (H1 _)) in REL.
      destruct fx, fy. simpl in *. destruct e. apply REL.
    - apply (@REL_COMMUTE _ _ _ _ _ (H1 _)).
      destruct fx, fy. simpl in *. destruct e. apply REL.
  Qed.
  Next Obligation.
    pattern fx at 17.
    rewrite sigT_eta. f_equal.
    apply BIJECTION1.
  Qed.
  Next Obligation.
    pattern gx at 17.
    rewrite sigT_eta. f_equal.
    apply BIJECTION2.
  Qed.

End DEP_SUM_ISO.
