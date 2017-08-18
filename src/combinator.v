Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor.

(* comp list embed
const id option prod coprod function dep_prod dep_sum *)


Program Definition id_SPFunctorMixin :=
  @SPFunctor.Mixin
    id id_functorMixin.(Functor.map) id_sFunctorMixin.(SFunctor.mem) id_sFunctorMixin.(SFunctor.rel)
    () Empty_set
    (fun _ x _ => inl x)
    _ _ _ _.
Next Obligation.
  eapply fapp in EQ; [|apply ()]. inv EQ. auto.
Qed.
Next Obligation.
  split; intros.
  - econstructor; [apply ()|].
    subst. constructor.
  - inv H. inv MEM. auto.
Qed.
Next Obligation.
  simplify. constructor; intros.
  - specialize (H ()). inv H. auto.
  - econstructor. auto.
Qed.
Canonical Structure id_SPFunctorType := spFunctorType _ id_SPFunctorMixin.


Program Definition option_SPFunctorMixin :=
  @SPFunctor.Mixin
    option option_functorMixin.(Functor.map) option_sFunctorMixin.(SFunctor.mem) option_sFunctorMixin.(SFunctor.rel)
    () ()
    (fun _ x _ =>
       match x with
       | Some x => inl x
       | None => inr ()
       end)
    _ _ _ _.
Next Obligation.
  destruct x1, x2; simplify; auto.
  - eapply fapp in EQ; [|apply ()]. inv EQ. auto.
  - eapply fapp in EQ; [|apply ()]. inv EQ.
  - eapply fapp in EQ; [|apply ()]. inv EQ.
Qed.
Next Obligation.
  destruct fx1; auto.
Qed.
Next Obligation.
  split; intros.
  - econstructor; [apply ()|].
    subst. constructor.
  - inv H. destruct fx; simplify; inv MEM; auto.
Qed.
Next Obligation.
  destruct fx1, fx2; simplify; auto; constructor; intros;
    repeat (match goal with
            | [H: () -> _ |- _] => specialize (H ())
            | [H: option_frel _ _ _ |- _] => inv H
            | [H: coproduct_rel _ _ _ _ _ |- _] => inv H
            | [|- option_frel _ _ _] => econstructor
            | [|- coproduct_rel _ _ _ _ _] => econstructor
            end; auto).
  econstructor.
Qed.
Canonical Structure option_SPFunctorType := spFunctorType _ option_SPFunctorMixin.


Definition const_embed D X (a: D) (s: unit) : X + D := inr a.

Program Definition const_SPFunctorMixin (D: Type) :=
  @SPFunctor.Mixin
    (fun X => D) (const_functorMixin D).(Functor.map) (const_sFunctorMixin D).(SFunctor.mem) (const_sFunctorMixin D).(SFunctor.rel)
    _ _
    (@const_embed D)
    _ _ _ _.
Next Obligation.
  apply equal_f with tt in EQ. unfold const_embed in EQ.
  inv EQ. auto.
Qed.
Next Obligation.
  split; intros.
  - inv H.
  - inv H. inv MEM.
Qed.
Next Obligation.
  split; intros.
  - simplify. specialize (H tt).
    simplify. inv H. inv REL. auto.
  - subst. econstructor. econstructor.
Qed.
Canonical Structure const_SPFunctorType (D: Type) := spFunctorType (const_sFunctorType D) (const_SPFunctorMixin D).

Definition prod_embed (F G: SPFunctorType) X (x: prod (F X) (G X)) (s: sum F.(SPFunctor.Sh1) G.(SPFunctor.Sh1)) :=
  match x with
  | (xl, xr) =>
    match s with
    | inl s' =>
      match (F.(SPFunctor.embedding) _ xl s') with
      | inl a => inl a
      | inr b => inr (inl b)
      end
    | inr s' =>
      match (G.(SPFunctor.embedding) _ xr s') with
      | inl a => inl a
      | inr b => inr (inr b)
      end
    end
  end.

Program Definition prod_SPFunctorMixin (F1 F2 : SPFunctorType) :=
  @SPFunctor.Mixin
    (fun X => prod (F1 X) (F2 X)) (product_functorMixin F1 F2).(Functor.map) (product_sFunctorMixin F1 F2).(SFunctor.mem) (product_sFunctorMixin F1 F2).(SFunctor.rel)
    _ _
    (@prod_embed F1 F2)
    _ _ _ _.
Next Obligation.
  f_equal; apply SPFunctorFacts.INJECTIVE; extensionality a.
  - apply equal_f with (inl a) in EQ. simplify.
    destruct (SPFunctor.embedding F1 T s1 a), (SPFunctor.embedding F1 T s a);
      inv EQ; auto.
  - apply equal_f with (inr a) in EQ. simplify.
    destruct (SPFunctor.embedding F2 T s2 a), (SPFunctor.embedding F2 T s0 a);
      inv EQ; auto.
Qed.
Next Obligation.
  unfold prod_embed, product_map. extensionality a. destruct a;
  simplify; rewrite SPFunctor._NATURAL_MAP; simplify.
  - destruct (SPFunctor.embedding F1 T1 s s1); auto.
  - destruct (SPFunctor.embedding F2 T1 s0 s1); auto.
Qed.
Next Obligation.
  split; intros.
  - inv H; apply SPFunctorFacts.NATURAL_MEM in H0; inv H0.
    + apply Function_mem with (d := inl d). simplify.
      destruct (SPFunctor.embedding F1 X s d); inv MEM. auto.
    + apply Function_mem with (d := inr d). simplify.
      destruct (SPFunctor.embedding F2 X s0 d); inv MEM. auto.
  - inv H. destruct d; unfold product_mem;
             [left | right]; apply SPFunctorFacts.NATURAL_MEM; simplify;
               apply Function_mem with (d := s1); simplify.
    + destruct (SPFunctor.embedding F1 X s s1); inv MEM; auto.
    + destruct (SPFunctor.embedding F2 X s0 s1); inv MEM; auto.
Qed.
Next Obligation.  
  split; intros.
  - unfold product_rel.
    unfold product_rel; split;
    apply SPFunctorFacts.NATURAL_REL; simplify; intro.
    + specialize (H (inl d)). simplify. inv H;
      destruct (SPFunctor.embedding F1 T1 s1 d); inv H1;
      destruct (SPFunctor.embedding F1 T2 s d); inv H2; try inv REL;
      repeat constructor; auto.
    + specialize (H (inr d)). simplify. inv H;
      destruct (SPFunctor.embedding F2 T1 s2 d); inv H1;
      destruct (SPFunctor.embedding F2 T2 s0 d); inv H2; try inv REL;
      repeat constructor; auto.
  - inv H.
    apply SPFunctorFacts.NATURAL_REL in H0. apply SPFunctorFacts.NATURAL_REL in H1.
    simplify. intro. destruct d;
    [specialize (H0 s3); inv H0 | specialize (H1 s3); inv H1];
    try inv REL; repeat constructor; auto.
Qed.
Canonical Structure prod_SPFunctorType (F1 F2: SPFunctorType) := spFunctorType (product_sFunctorType F1 F2) (prod_SPFunctorMixin F1 F2).



Definition coprod_embed (F G : SPFunctorType) X (x: sum (F X) (G X))
           (s: sum (sum unit F.(SPFunctor.Sh1)) (sum unit G.(SPFunctor.Sh1))) :=
  match x with
  | inl x' =>
    match s with
    | inl (inl _) => inr (inl true)
    | inl (inr s') =>
      match F.(SPFunctor.embedding) _ x' s' with
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
      match G.(SPFunctor.embedding) _ x' s' with
      | inl a => inl a
      | inr b => inr (inr (inr b))
      end
    end  
  end.

Program Definition coprod_SPFunctorMixin (F1 F2 : SPFunctorType) :=
  @SPFunctor.Mixin
    (fun X => sum (F1 X) (F2 X)) (coproduct_functorMixin F1 F2).(Functor.map) (coproduct_sFunctorMixin F1 F2).(SFunctor.mem) (coproduct_sFunctorMixin F1 F2).(SFunctor.rel)
    _ _
    (@coprod_embed F1 F2)
    _ _ _ _.
Next Obligation.
  unfold coprod_embed in EQ. destruct x1, x2; inv EQ.
  - f_equal. apply SPFunctorFacts.INJECTIVE.
    simplify. extensionality a.
    apply equal_f with (x := (inl (inr a))) in H0.
    destruct (SPFunctor.embedding F1 T s a), (SPFunctor.embedding F1 T s0 a);
    inv H0; auto.
  - apply equal_f with (x := (inl (inl tt))) in H0; inv H0.
  - apply equal_f with (x := (inl (inl tt))) in H0; inv H0.
  - f_equal. apply SPFunctorFacts.INJECTIVE.
    simplify. extensionality a.
    apply equal_f with (x := (inr (inr a))) in H0.
    destruct (SPFunctor.embedding F2 T s a), (SPFunctor.embedding F2 T s0 a);
    inv H0; auto.
Qed.
Next Obligation.
  unfold coprod_embed; destruct fx1; extensionality a;
    destruct a; destruct s0; simplify; auto;
  repeat rewrite SPFunctor._NATURAL_MAP; simplify.
  - destruct (SPFunctor.embedding F1 T1 s s0); auto.
  - destruct (SPFunctor.embedding F2 T1 s s0); auto.
Qed.
Next Obligation.
  split; intros.
  - destruct fx; unfold coproduct_mem in H; apply SPFunctorFacts.NATURAL_MEM in H;
    inv H; simplify.
    + apply (Function_mem _ _ _ (inl (inr d))).
      simplify. destruct (SPFunctor.embedding F1 X s d); inv MEM; auto.
    + apply (Function_mem _ _ _ (inr (inr d))).
      simplify. destruct (SPFunctor.embedding F2 X s d); inv MEM; auto.
  - inv H. destruct fx; simpl;
    apply SPFunctorFacts.NATURAL_MEM; simplify; destruct d; destruct s0;
      try inv MEM; apply (Function_mem _ _ _ s0); simplify.
    + destruct (SPFunctor.embedding F1 X s s0); inv MEM; auto.
    + destruct (SPFunctor.embedding F2 X s s0); inv MEM; auto.
Qed.
Next Obligation.
  split; intros.
  - destruct fx1, fx2; simplify.
    + constructor. apply SPFunctorFacts.NATURAL_REL. simplify. intro.
      specialize (H (inl (inr d))). simplify.
      destruct (SPFunctor.embedding F1 T1 s d), (SPFunctor.embedding F1 T2 s0 d);
        inv H; try inv REL; repeat constructor; auto.
    + specialize (H (inl (inl tt))). inv H. inv REL.
    + specialize (H (inl (inl tt))). inv H. inv REL.
    + constructor. apply SPFunctorFacts.NATURAL_REL. simplify. intro.
      specialize (H (inr (inr d))). simplify.
      destruct (SPFunctor.embedding F2 T1 s d), (SPFunctor.embedding F2 T2 s0 d);
        inv H; try inv REL; repeat constructor; auto.
  - inv H; apply SPFunctorFacts.NATURAL_REL in REL; simplify;
      intro; destruct d; destruct s; repeat constructor.
    + specialize (REL s); inv REL; try inv REL0; repeat constructor; auto.
    + specialize (REL s); inv REL; try inv REL0; repeat constructor; auto.
Qed.
Canonical Structure coprod_SPFunctorType (F1 F2: SPFunctorType) := spFunctorType (coproduct_sFunctorType F1 F2) (coprod_SPFunctorMixin F1 F2).


Definition function_embed D (F: SPFunctorType) X (x: D -> F X)
           (s: D * F.(SPFunctor.Sh1)) : (X + F.(SPFunctor.Sh2)) :=
  match s with
  | (d, s') => F.(SPFunctor.embedding) _ (x d) s' end.

Program Definition function_SPFunctorMixin D (F : SPFunctorType) :=
  @SPFunctor.Mixin
    (fun T => D -> F T) (function_functorMixin D F).(Functor.map) (function_sFunctorMixin D F).(SFunctor.mem) (function_sFunctorMixin D F).(SFunctor.rel)
    _ _
    (@function_embed D F)
    _ _ _ _.
Next Obligation.
  extensionality d. apply SPFunctorFacts.INJECTIVE. extensionality s.
  apply equal_f with (d, s) in EQ. auto.
Qed.
Next Obligation.
  extensionality a. destruct a. unfold function_embed. simplify.
  rewrite SPFunctor._NATURAL_MAP. auto.
Qed.
Next Obligation.
  split; intros.
  - inv H. apply SPFunctorFacts.NATURAL_MEM in MEM. inv MEM.
    apply (Function_mem _ _ _ (d, d0)). auto.
  - inv H. destruct d.
    econstructor. apply SPFunctorFacts.NATURAL_MEM.
    simplify. econstructor. simplify. apply MEM.
Qed.
Next Obligation.
  split; intros.
  - simplify. intro.
    apply SPFunctorFacts.NATURAL_REL. simplify. intro.
    specialize (H (d, d0)). eauto.
  - simplify. intro. destruct d.
    specialize (H d). apply SPFunctorFacts.NATURAL_REL in H. simplify.
    specialize (H s). auto.
Qed.
Canonical Structure function_SPFunctorType D (F: SPFunctorType) := spFunctorType (function_sFunctorType D F) (function_SPFunctorMixin D F).


Definition dep_prod_embed A (B : A -> SPFunctorType) X (x: forall a : A, B a X)
           (s: sigT (fun a => (B a).(SPFunctor.Sh1))) : (X + (sigT (fun a => (B a).(SPFunctor.Sh2)))) :=
match s with
| existT _ a sh =>
  match (B a).(SPFunctor.embedding) _ (x a) sh with
  | inl v => inl v
  | inr v => inr (existT _ a v)
  end
end.

Program Definition dep_prod_SPFunctorMixin A (B : A -> SPFunctorType) :=
  @SPFunctor.Mixin
    (fun X => forall a : A, B a X) (dep_prod_functorMixin B).(Functor.map) (dep_prod_sFunctorMixin B).(SFunctor.mem) (dep_prod_sFunctorMixin B).(SFunctor.rel)
    _ _
    (@dep_prod_embed A B)
    _ _ _ _.
Next Obligation.
  extensionality a. apply SPFunctorFacts.INJECTIVE. extensionality s.
  apply equal_f with (existT _ a s) in EQ. simplify.
  destruct (SPFunctor.embedding (B a) T (x1 a) s),
  (SPFunctor.embedding (B a) T (x2 a) s); inv EQ; auto.
  dependent destruction H0. auto.
Qed.
Next Obligation.
  extensionality s. destruct s.
  unfold dep_prod_map, dep_prod_embed. rewrite SPFunctor._NATURAL_MAP.
  simplify. destruct (SPFunctor.embedding (B x) T1 (fx1 x) s); auto.
Qed.
Next Obligation.
  split; intros.
  - inv H. apply SPFunctorFacts.NATURAL_MEM in H0. inv H0.
    apply (Function_mem _ _ _ (existT _ x0 d)). simplify. 
    destruct (SPFunctor.embedding (B x0) X (fx x0) d); auto.
  - inv H. destruct d.
    unfold dep_prod_mem. exists x0.
    apply SPFunctorFacts.NATURAL_MEM. simplify.
    apply (Function_mem _ _ _ s).
    destruct (SPFunctor.embedding (B x0) X (fx x0) s); auto.
Qed.
Next Obligation.
  split; intros.
  - simplify. unfold dep_prod_rel. intros.
    apply SPFunctorFacts.NATURAL_REL. simplify. intro.
    specialize (H (existT _ a d)). simplify. inv H;
    destruct (SPFunctor.embedding (B a) T1 (fx1 a) d); inv H1;
    destruct (SPFunctor.embedding (B a) T2 (fx2 a) d); inv H2.
    + constructor; auto.
    + constructor. simplify. dependent destruction REL. auto.     
  - simplify. intro. destruct d.
    unfold dep_prod_rel in H. specialize (H x).
    apply SPFunctorFacts.NATURAL_REL in H. simplify. specialize (H s).
    inv H; constructor; auto.
    simplify. subst. auto.
Qed.
Canonical Structure dep_prod_SPFunctorType A (B: A -> SPFunctorType) := spFunctorType (dep_prod_sFunctorType B) (dep_prod_SPFunctorMixin B).


Definition dep_sum_embed A (B : A -> SPFunctorType) X (x: sigT (fun a => (B a) X))
           (s: sigT (fun a => sum unit (B a).(SPFunctor.Sh1))) :
  sum X (sum bool (sigT (fun a => (B a).(SPFunctor.Sh2)))) :=
  match x with
  | existT _ a x' =>
    match s with
    | existT _ a' sh =>
      match (excluded_middle_informative (a = a')) with
      | left pf =>
        match sh with
        | inl _ => inr (inl true)
        | inr sh' =>
          match (B a').(SPFunctor.embedding) _ (eq_rect _ (fun y => (B y) X) x' _ pf) sh' with
          | inl a => inl a
          | inr b => inr (inr (existT _ a' b)) end
        end
      | right _ => inr (inl false)
      end
    end
  end.

Ltac eq_dec x y := let p := fresh "p" in
                   destruct (excluded_middle_informative (x=y)) as [p|p];
                   [subst | ];
                   eauto; try intuition; repeat rewrite <- eq_rect_eq in *.

Program Definition dep_sum_SPFunctorMixin A (B : A -> SPFunctorType) :=
  @SPFunctor.Mixin
    (fun X => sigT (fun a => (B a) X)) (dep_sum_functorMixin B).(Functor.map) (dep_sum_sFunctorMixin B).(SFunctor.mem) (dep_sum_sFunctorMixin B).(SFunctor.rel)
    _ _
    (@dep_sum_embed A B)
    _ _ _ _.
Next Obligation.
  unfold dep_sum_embed in EQ. eq_dec x1 x2.
  - f_equal.
    apply SPFunctorFacts.INJECTIVE. simplify. extensionality s.
    apply equal_f with (existT _ x2 (inr s)) in EQ.
    eq_dec x2 x2.
    destruct (SPFunctor.embedding (B x2) T X0 s), (SPFunctor.embedding (B x2) T X s);
      inv EQ; auto.
    dependent destruction H0. auto.
  - apply equal_f with (existT _ x1 (inl tt)) in EQ.
    eq_dec x1 x1. eq_dec x2 x1. inv EQ.
Qed.
Next Obligation.
  extensionality s. destruct s. destruct s; simplify; eq_dec fx1 x.
  rewrite SPFunctor._NATURAL_MAP. simplify.
  destruct (SPFunctor.embedding (B x) T1 X s); auto.
Qed.
Next Obligation.
  split; intros.
  - simplify. apply SPFunctorFacts.NATURAL_MEM in H.
    inv H. apply (Function_mem _ _ _ (existT _ fx (inr d))). simplify.
    eq_dec fx fx.
    destruct (SPFunctor.embedding (B fx) X X0 d); inv MEM. auto.
  - inv H. destruct d. destruct s; simplify; eq_dec fx x0.
    apply SPFunctorFacts.NATURAL_MEM. simplify.
    apply (Function_mem _ _ _ s). simplify.
    destruct (SPFunctor.embedding (B x0) X X0 s); inv MEM; auto.
Qed.
Next Obligation.
  split; intros; simplify.
  - eq_dec fx1 fx2.
    + constructor. apply SPFunctorFacts.NATURAL_REL. simplify.
      intro. specialize (H (existT _ fx2 (inr d))). simplify.
      eq_dec fx2 fx2.
      destruct (SPFunctor.embedding (B fx2) T1 X0 d),
      (SPFunctor.embedding (B fx2) T2 X d); inv H; constructor; auto.
      simplify. dependent destruction REL. auto.
    + specialize (H (existT _ fx1 (inl tt))). simplify.
      eq_dec fx1 fx1. eq_dec fx2 fx1. inv H. inv REL.
  - dependent destruction H. apply SPFunctorFacts.NATURAL_REL in r0. simplify.
    intros. destruct d. destruct s; eq_dec fx2 x; repeat constructor.
    specialize (r0 s). inv r0; repeat constructor; auto.
    simplify. subst. auto.
Qed.
Canonical Structure dep_sum_SPFunctorType A (B: A -> SPFunctorType) := spFunctorType (dep_sum_sFunctorType B) (dep_sum_SPFunctorMixin B).

Definition comp_embed' (F G: SPFunctorType) X
           (x': F.(SPFunctor.Sh1) -> (sum (G.(SPFunctor.Sh1) ->
                                           (sum X G.(SPFunctor.Sh2))) F.(SPFunctor.Sh2)))
           (s: prod (sum unit G.(SPFunctor.Sh1)) F.(SPFunctor.Sh1)) :=
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

Lemma comp_embed'_injective F G X x y
  : @comp_embed' F G X x = @comp_embed' F G X y -> x = y.
Proof.
  unfold comp_embed'. intros.
  extensionality s. destruct (x s) eqn : H1; destruct (y s) eqn : H2.
  - f_equal.
    extensionality t.
    apply equal_f with (inr t, s) in H.
    rewrite H1 in H. rewrite H2 in H.
    destruct (s0 t); destruct (s1 t); inversion H; eauto.
  - apply equal_f with (inl tt, s) in H.
    rewrite H1 in H. rewrite H2 in H. inversion H.
  - apply equal_f with (inl tt, s) in H.
    rewrite H1 in H. rewrite H2 in H. inversion H.
  - f_equal.
    apply equal_f with (inl tt, s) in H.
    rewrite H1 in H. rewrite H2 in H. inversion H. eauto.
Qed.

Definition comp_embed (F G: SPFunctorType) X (x: F (G X)) :=
  comp_embed' F G (F.(SPFunctor.embedding) _ (F.(Functor.map) (G.(SPFunctor.embedding) X) x)).

Program Definition compose_SPFunctorMixin (F G : SPFunctorType) :=
  @SPFunctor.Mixin
    (fun X => G (F X)) (compose_functorMixin F G).(Functor.map) (compose_sFunctorMixin F G).(SFunctor.mem) (compose_sFunctorMixin F G).(SFunctor.rel)
    _ _
    (@comp_embed G F)
    _ _ _ _.
Next Obligation.
  unfold comp_embed in EQ.
  apply comp_embed'_injective in EQ. apply SPFunctorFacts.INJECTIVE in EQ.
  apply SPFunctorFacts.map_injective in EQ; auto. apply SPFunctorFacts.INJECTIVE.
Qed.
Next Obligation.
  unfold comp_embed. unfold comp_embed'. extensionality s. destruct s.
  - do 3 (rewrite SPFunctor._NATURAL_MAP). simplify. destruct s;
    destruct (SPFunctor.embedding G (F T1) fx1 s0); auto.
    rewrite SPFunctor._NATURAL_MAP. simplify.
    destruct (SPFunctor.embedding F T1 s1 s); auto.
Qed.
Next Obligation.
  split; intros.
  - inv H.
    apply SPFunctorFacts.NATURAL_MEM in HF. apply SPFunctorFacts.NATURAL_MEM in HG.
    inv HG. inv HF. simplify.
    apply (Function_mem _ _ _ (inr d, d0)). simplify.
    rewrite SPFunctor._NATURAL_MAP. simplify.
    destruct (SPFunctor.embedding G (F X) fx d0); inv MEM0.
    destruct (SPFunctor.embedding F X gx d); inv MEM. auto.
  - inv H. destruct d. unfold comp_embed, comp_embed' in MEM.
    rewrite SPFunctor._NATURAL_MAP in MEM; simplify.
    destruct (SPFunctor.embedding G (F X) fx s0) eqn : EQ1; destruct s; try inv MEM.
    destruct (SPFunctor.embedding F X s1 s) eqn : EQ2; inv MEM.
    apply (_comp_mem _ _ x s1); apply SPFunctorFacts.NATURAL_MEM; simplify.
    + econstructor. simplify. rewrite EQ2. auto.
    + econstructor. simplify. rewrite EQ1. auto.
Qed.    
Next Obligation.
  split; intros.
  - simplify. apply SPFunctorFacts.NATURAL_REL. simplify. intro.
    unfold comp_embed, comp_embed' in H.
    destruct (SPFunctor.embedding G (F T2) fx2 d) eqn : EQ1;
    destruct (SPFunctor.embedding G (F T1) fx1 d) eqn : EQ2.
    + apply (coproduct_rel_inl id_sFunctorType (const_sFunctorType (SPFunctor.Sh2 G)) (SFunctor.rel F r) s0 s).
      apply SPFunctorFacts.NATURAL_REL. simplify. intro.
      apply (coproduct_rel_inl id_sFunctorType (const_sFunctorType Empty_set) (SFunctor.rel F r) s0 s). simplify.
      apply SPFunctorFacts.NATURAL_REL. simplify. intro.
      specialize (H (inr d1, d)). simplify.
      do 2 (rewrite SPFunctor._NATURAL_MAP in H). simplify.
      rewrite EQ1 in H. rewrite EQ2 in H.
      destruct (SPFunctor.embedding F T1 s0 d1), (SPFunctor.embedding F T2 s d1);
        inv H.
      * constructor. auto.
      * inv REL. repeat constructor.
    +  specialize (H (inl tt, d)). simplify.
       do 2 (rewrite SPFunctor._NATURAL_MAP in H). simplify.
       rewrite EQ1 in H. rewrite EQ2 in H.
       inv H. inv REL.
    +  specialize (H (inl tt, d)). simplify.
       do 2 (rewrite SPFunctor._NATURAL_MAP in H). simplify.
       rewrite EQ1 in H. rewrite EQ2 in H.
       inv H. inv REL.
    + apply (coproduct_rel_inr id_sFunctorType (const_sFunctorType (SPFunctor.Sh2 G)) (SFunctor.rel F r) s0 s).
      simplify.
      specialize (H (inl tt, d)).
      do 2 (rewrite SPFunctor._NATURAL_MAP in H). simplify.
      rewrite EQ1 in H. rewrite EQ2 in H.
      inv H. simplify. inv REL. auto.
  - simplify. apply SPFunctorFacts.NATURAL_REL in H. simplify.
    intros. destruct d. specialize (H s0). simplify.
    do 2 (rewrite SPFunctor._NATURAL_MAP). simplify.
    destruct s; inv H.
    + repeat constructor.
    + repeat constructor. simplify. subst. auto.
    + simplify.
      apply SPFunctorFacts.NATURAL_REL in REL. simplify. specialize (REL s).
      inv REL; repeat constructor; auto.
      simplify. subst. auto.
    + repeat constructor.
Qed.
Canonical Structure compose_SPFunctorType (F G: SPFunctorType) := spFunctorType (compose_sFunctorType F G) (compose_SPFunctorMixin F G).


Fixpoint list_embed X (l: list X) (s: list unit) : X + unit :=
  match l with
  | nil => inr tt
  | cons hd tl => 
      match s with 
      | cons _ nil => inl hd
      | cons _ stl => list_embed tl stl
      | _ => inr tt
      end
  end.

Program Definition list_functorMixin :=
  @Functor.Mixin list List.map _ _.
Next Obligation.
  apply functional_extensionality. induction x; auto.
  simplify. f_equal. auto.
Qed.
Next Obligation.
  induction x1; auto.
  simpl. f_equal. apply IHx1.
Qed.
Canonical Structure list_functorType := FunctorType list_functorMixin.


Fixpoint list_mem X (l: list X) (x: X) : Prop :=
match l with
| nil => False
| cons hd tl => eq hd x \/ list_mem tl x end.

Inductive list_rel (X Y : Type) (RE: X -> Y -> Prop) : list X -> list Y -> Prop :=
| _list_rel_nil : list_rel RE nil nil
| _list_rel_cons hd1 hd2 tl1 tl2 (HD: RE hd1 hd2) (TL: list_rel RE tl1 tl2) : 
    (list_rel RE (cons hd1 tl1) (cons hd2 tl2)).

Definition list_map_dep X Y (x: list X) (ALL: forall y, list_mem x y -> Y) : list Y.
  induction x.
  - apply nil.
  - apply cons.
    + apply (ALL a (or_introl (eq_refl a))).
    + apply IHx. intros.
      apply (ALL y (or_intror H)).
Defined.

Program Definition list_sFunctorMixin :=
  @SFunctor.Mixin
    list list_functorMixin.(Functor.map)
    list_mem
    list_map_dep
    list_rel
    _ _.
Next Obligation.
  induction fx; inversion MEM; simplify; subst; auto.
Qed.
Next Obligation.
  induction fx; auto.
  simpl. f_equal; auto.
Qed.
Canonical Structure list_sFunctorType := SFunctorType _ list_sFunctorMixin.

Program Definition list_SPFunctorMixin :=
  @SPFunctor.Mixin
    list list_functorMixin.(Functor.map) list_sFunctorMixin.(SFunctor.mem) list_sFunctorMixin.(SFunctor.rel)
    _ _ list_embed
    _ _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
