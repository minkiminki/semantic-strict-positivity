Require Import FunctionalExtensionality ClassicalDescription.
Require Import Coq.Logic.Eqdep_dec.
Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.
Require Import ssp.

Arguments proj1_sig {A P} e.
Arguments projT1 {A P} x.

Section Constant_SSPF.

Variable A : Type.

Definition const_eq (X : Type) (EQ: X -> X -> Prop) : A -> A -> Prop := (@eq A).

Program Definition const_Fn :=
  (@PFunctor.mk_data (fun X => A) (fun _ _ _ => False) const_eq
                     (fun X Y (f: X -> Y) x => x) (fun _ _ a _ => a) _).

Definition const_embed X (a: A) (s: unit) : X + A := inr a.

Program Definition Const : SSPF.t := 
  @SSPF.mk const_Fn unit A const_embed _ _ _ _ _.
Next Obligation.
  inversion H.
Defined.
Next Obligation.
  unfold const_embed in X0.
  inversion X0. inversion EQ.
Defined.
Next Obligation.
  split; unfold SPUF.u_eq, const_eq, const_embed; intros.
  - split; intros.
    + subst. tauto.
    + inversion H0.
  - destruct H. specialize (H tt fx1).
    destruct H. specialize (H eq_refl).
    inversion H. auto.
Defined.
Next Obligation.
  unfold const_embed in EQ.
  apply equal_f with tt in EQ.
  inversion EQ. auto.
Defined.

End Constant_SSPF.

Section Identity_SSPF.

Definition ident_embed X (x: X) (s: unit) : X + False := inl x.

Program Definition Ident : SSPF.t := 
  @SSPF.mk ident_Fn unit False ident_embed _ _ _ _ _.
Next Obligation.
  unfold ident_embed.
  apply (SPUF._u_mem _ tt). auto.
Defined.
Next Obligation.
  unfold ident_embed in X0.
  inversion X0. inversion EQ. constructor.
Defined.
Next Obligation.
  split; unfold ident_embed, SPUF.u_eq; intros.
  - split; intros.
    + destruct e.
    + inversion H0. inversion H1. subst. auto.
  - destruct H.
    specialize (H0 tt fx1 fx2). tauto.
Defined.
Next Obligation.
  apply equal_f with tt in EQ.
  inversion EQ. auto.
Qed.

End Identity_SSPF.

Section Coproduct_SSPF.

Variable F G : SSPF.t.

Definition coprod_map X Y (f: X -> Y) x :=
  match x with
  | inl xl => inl (F.(PFunctor.map) f xl)
  | inr xr => inr (G.(PFunctor.map) f xr)
  end.

Definition coprod_mem X (x: F X + G X) : X -> Type :=
  match x with
  | inl fx => F.(PFunctor.mem) fx
  | inr gx => G.(PFunctor.mem) gx end.

Inductive coprod_eq X (EQ: X -> X -> Prop) : (F X + G X) -> (F X + G X) -> Prop :=
  | _copr_eql fx1 fx2 : F.(PFunctor.eq) EQ fx1 fx2 -> coprod_eq EQ (inl fx1) (inl fx2)
  | _copr_eqr gx1 gx2 : G.(PFunctor.eq) EQ gx1 gx2 -> coprod_eq EQ (inr gx1) (inr gx2).

Definition coprod_uni X Y (x: F X + G X) (ALL: forall y, coprod_mem x y -> Y)
  : F Y + G Y.
  destruct x.
  - apply (inl (F.(PFunctor.uni) f (fun y r => ALL _ r))).
  - apply (inr (G.(PFunctor.uni) f (fun y r => ALL _ r))).
Defined.

Program Definition coprod_Fn :=
  (@PFunctor.mk_data (fun X => sum (F X) (G X)) coprod_mem coprod_eq
                     coprod_map coprod_uni _).
Next Obligation.
Proof.
  unfold coprod_map. destruct a; unfold coprod_uni; f_equal.
  - apply F.(PFunctor.uni_correct).
    intros. apply INV.
  - apply G.(PFunctor.uni_correct).
    intros. apply INV.
Defined.

Definition coprod_embed X (x: sum (F X) (G X))
           (s: sum (sum unit F.(SSPF.Sh)) (sum unit G.(SSPF.Sh))) :=
  match x with
  | inl x' =>
    match s with
    | inl (inl _) => inr (inl true)
    | inl (inr s') =>
      match F.(SSPF.emb) _ x' s' with
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
      match G.(SSPF.emb) _ x' s' with
      | inl a => inl a
      | inr b => inr (inr (inr b))
      end
    end  
  end.

Program Definition Coprod : SSPF.t := 
  @SSPF.mk coprod_Fn _ _ coprod_embed _ _ _ _ _.
Next Obligation.
  unfold coprod_embed. destruct fx;
  apply SSPF.mem_nat1 in X0; destruct X0.
  - apply (SPUF._u_mem _ (inl (inr s))). rewrite EQ. auto.
  - apply (SPUF._u_mem _ (inr (inr s))). rewrite EQ. auto.
Defined.
Next Obligation.
Proof.
  destruct fx;
  inversion X0; subst; destruct s;
  try destruct s; inversion EQ; apply SSPF.mem_nat2.
  - apply (SPUF._u_mem _ s).
    destruct ((SSPF.emb F) X f); inversion H0. auto.
  - apply (SPUF._u_mem _ s).
    destruct ((SSPF.emb G) X f); inversion H0. auto.
Defined.
Next Obligation.
Proof.
  unfold coprod_embed, coprod_map.
  destruct x; destruct s; destruct s; try eauto;
  rewrite SSPF.map_nat; simpl; unfold SPUF.map;
  [destruct ((SSPF.emb F) X f0) | destruct ((SSPF.emb G) X f0)]; eauto.
Defined.
Next Obligation.
  destruct fx1, fx2; split; intros; inversion H; subst.
  - unfold SPUF.u_eq, coprod_embed; apply SSPF.eq_nat in H2; split; intros.
    + destruct s; destruct s; split; intro; auto;
      destruct (SSPF.emb F X f) eqn : EQ1; destruct (SSPF.emb F X f0) eqn : EQ2;
      inversion H0; destruct H2;
      try apply H1 in EQ1; try rewrite EQ1 in EQ2; inversion EQ2; auto.
      apply H1 in EQ2. rewrite EQ1 in EQ2. inversion EQ2.
    + destruct s; destruct s; inversion H0; inversion H1. inversion H2.
      destruct (SSPF.emb F X f) eqn : EQ1; destruct (SSPF.emb F X f0) eqn : EQ2;
      inversion H0; inversion H1; subst.
      apply (H6 _ _ _ EQ1 EQ2).
  - constructor. apply SSPF.eq_nat. constructor.
    + intros. split; intros;
      specialize (H0 (inl (inr s)) (inr (inl e))); unfold coprod_embed in H0;
      rewrite H2 in H0; destruct H0.
      * specialize (H0 eq_refl).
        destruct (SSPF.emb F X f0); inversion H0. auto.
      * specialize (H3 eq_refl).
        destruct (SSPF.emb F X f); inversion H3. auto.
    + intros. specialize (H1 (inl (inr s)) x1 x2); simpl in H1.
      rewrite H2 in H1. rewrite H3 in H1.
      apply (H1 eq_refl eq_refl).
  - specialize (H0 (inl (inl tt)) (inl true)). unfold coprod_embed in H0.
    destruct H0. specialize (H0 eq_refl). inversion H0.
  - specialize (H0 (inl (inl tt)) (inl true)). unfold coprod_embed in H0.
    destruct H0. specialize (H2 eq_refl). inversion H2.
 - unfold SPUF.u_eq, coprod_embed; apply SSPF.eq_nat in H2; split; intros.
    + destruct s; destruct s; split; intro; auto;
      destruct (SSPF.emb G X f) eqn : EQ1; destruct (SSPF.emb G X f0) eqn : EQ2;
      inversion H0; destruct H2;
      try apply H1 in EQ1; try rewrite EQ1 in EQ2; inversion EQ2; auto.
      apply H1 in EQ2. rewrite EQ1 in EQ2. inversion EQ2.
    + destruct s; destruct s; inversion H0; inversion H1. inversion H2.
      destruct (SSPF.emb G X f) eqn : EQ1; destruct (SSPF.emb G X f0) eqn : EQ2;
      inversion H0; inversion H1; subst.
      apply (H6 _ _ _ EQ1 EQ2).
  - constructor. apply SSPF.eq_nat. constructor.
    + intros. split; intros;
      specialize (H0 (inr (inr s)) (inr (inr e))); unfold coprod_embed in H0;
      rewrite H2 in H0; destruct H0.
      * specialize (H0 eq_refl).
        destruct (SSPF.emb G X f0); inversion H0. auto.
      * specialize (H3 eq_refl).
        destruct (SSPF.emb G X f); inversion H3. auto.
    + intros. specialize (H1 (inr (inr s)) x1 x2); simpl in H1.
      rewrite H2 in H1. rewrite H3 in H1.
      apply (H1 eq_refl eq_refl).
Defined.
Next Obligation.
Proof.
  destruct m; destruct n; unfold coprod_embed in EQ.
  - f_equal.
    apply SSPF.inj; extensionality s.
    apply equal_f with (inl (inr s)) in EQ.
    destruct ((SSPF.emb F) X f); destruct ((SSPF.emb F) X f0); inversion EQ; eauto.
  - exfalso.
    apply equal_f with (inl (inl tt)) in EQ.
    destruct ((SSPF.emb F) X f); inversion EQ.
  - exfalso.
    apply equal_f with (inl (inl tt)) in EQ.
    destruct ((SSPF.emb F) X f0); inversion EQ.
  - f_equal.
    apply SSPF.inj; extensionality s.
    apply equal_f with (inr (inr s)) in EQ.
    destruct ((SSPF.emb G) X f); destruct ((SSPF.emb G) X f0); inversion EQ; eauto.
Qed.

End Coproduct_SSPF.

Section Product_SSPF.

Variable F G: SSPF.t.

Definition prod_map X Y (f: X -> Y) x :=
  match x with
  | (xl, xr) => (F.(PFunctor.map) f xl, G.(PFunctor.map) f xr)
  end.

Definition prod_mem X (a: prod (F X) (G X)) (x: X) : Type :=
  match a with
  | (fx, gx) => (F.(PFunctor.mem) fx x) + (G.(PFunctor.mem) gx x) end.

Definition prod_eq X (EQ: X -> X -> Prop) (x1 x2: F X * G X) : Prop :=
  match x1, x2 with
  | (fx1, gx1), (fx2, gx2) => F.(PFunctor.eq) EQ fx1 fx2 /\ G.(PFunctor.eq) EQ gx1 gx2
  end.

Definition prod_uni X Y (x: F X * G X) (ALL: forall y, prod_mem x y -> Y) 
  : F Y * G Y.
  destruct x.
  apply (F.(PFunctor.uni) f (fun y r => ALL _ (inl r)),
         G.(PFunctor.uni) f0 (fun y r => ALL _ (inr r))).
Defined.

Program Definition prod_Fn :=
  (@PFunctor.mk_data (fun X => prod (F X) (G X)) prod_mem prod_eq prod_map prod_uni _).
Next Obligation.
Proof.
  unfold prod_map. unfold prod_uni. f_equal.
  - apply F.(PFunctor.uni_correct).
    intros. apply INV.
  - apply G.(PFunctor.uni_correct).
    intros. apply INV.
Defined.

Definition prod_embed X (x: prod (F X) (G X)) (s: sum F.(SSPF.Sh) G.(SSPF.Sh)) :=
  match x with
  | (xl, xr) =>
    match s with
    | inl s' =>
      match (F.(SSPF.emb) _ xl s') with
      | inl a => inl a
      | inr b => inr (inl b)
      end
    | inr s' =>
      match (G.(SSPF.emb) _ xr s') with
      | inl a => inl a
      | inr b => inr (inr b)
      end
    end
  end.

Program Definition Prod : SSPF.t := 
  @SSPF.mk prod_Fn _ _ prod_embed _ _ _ _ _.
Next Obligation.
  unfold prod_embed. inversion X0;
  apply SSPF.mem_nat1 in X1; inversion X1; subst.
  - apply (SPUF._u_mem _ (inl s)).
    rewrite EQ. auto.
  - apply (SPUF._u_mem _ (inr s)).
    rewrite EQ. auto.
Defined.
Next Obligation.
  unfold prod_embed in X0. inversion X0. subst.
  destruct s.
  - apply inl.
    apply F.(SSPF.mem_nat2).
    apply (SPUF._u_mem _ s).
    destruct ((SSPF.emb F) X f); inversion EQ. auto.
  - apply inr.
    apply G.(SSPF.mem_nat2).
    apply (SPUF._u_mem _ s).
    destruct ((SSPF.emb G) X f0); inversion EQ. auto.
Defined.
Next Obligation.  
  unfold prod_map, prod_embed.
  destruct s; rewrite SSPF.map_nat; unfold SPUF.map.
  - destruct (SSPF.emb F X f0 s); auto.
  - destruct (SSPF.emb G X f1 s); auto.
Defined.
Next Obligation.
Proof.
  split; unfold SPUF.u_eq, prod_embed, prod_eq; intros.
  - destruct H. apply SSPF.eq_nat in H. apply SSPF.eq_nat in H0.
    destruct H, H0. split; intros.
    + split; intros.
      destruct s;
      [destruct (SSPF.emb F X f) eqn : EQ1; destruct (SSPF.emb F X f1) eqn : EQ2;
       inversion H3; apply H in EQ2; rewrite EQ2 in EQ1; inversion EQ1; auto |
       destruct (SSPF.emb G X f0) eqn : EQ1; destruct (SSPF.emb G X f2) eqn : EQ2;
       inversion H3; apply H0 in EQ2; rewrite EQ2 in EQ1; inversion EQ1; auto ].
      destruct s;
      [destruct (SSPF.emb F X f) eqn : EQ1; destruct (SSPF.emb F X f1) eqn : EQ2;
       inversion H3; apply H in EQ1; rewrite EQ1 in EQ2; inversion EQ2; auto |
       destruct (SSPF.emb G X f0) eqn : EQ1; destruct (SSPF.emb G X f2) eqn : EQ2;
       inversion H3; apply H0 in EQ1; rewrite EQ1 in EQ2; inversion EQ2; auto ].
    + destruct s.
      destruct (SSPF.emb F X f1)  eqn : EQ1; destruct (SSPF.emb F X f)  eqn : EQ2;
      inversion H3; inversion H4; subst.
      apply (H1 _ _ _ EQ1 EQ2).
      destruct (SSPF.emb G X f2)  eqn : EQ1; destruct (SSPF.emb G X f0)  eqn : EQ2;
      inversion H3; inversion H4; subst.
      apply (H2 _ _ _ EQ1 EQ2).
  - split; apply SSPF.eq_nat; destruct H; split; intros.
    + split; intros; specialize (H (inl s) (inl e)); simpl in H; rewrite H1 in H.
      * destruct H. specialize (H eq_refl).
        destruct (SSPF.emb F X f); inversion H; auto.
      * destruct H. specialize (H2 eq_refl).
        destruct (SSPF.emb F X f1); inversion H2; auto.
    + specialize (H0 (inl s)); simpl in H0; rewrite H1 in H0; rewrite H2 in H0.
      apply H0; auto.
    + split; intros; specialize (H (inr s) (inr e)); simpl in H; rewrite H1 in H.
      * destruct H. specialize (H eq_refl).
        destruct (SSPF.emb G X f0); inversion H; auto.
      * destruct H. specialize (H2 eq_refl).
        destruct (SSPF.emb G X f2); inversion H2; auto.
    + specialize (H0 (inr s)); simpl in H0; rewrite H1 in H0; rewrite H2 in H0.
      apply H0; auto.
Qed.
Next Obligation.
  f_equal; apply SSPF.inj; extensionality s.
  - apply equal_f with (inl s) in EQ. unfold prod_embed in EQ.
    destruct ((SSPF.emb F) X f1 s); destruct ((SSPF.emb F) X f s);
    inversion EQ; f_equal; eauto.
  - apply equal_f with (inr s) in EQ. unfold prod_embed in EQ.
    destruct ((SSPF.emb G) X f2 s); destruct ((SSPF.emb G) X f0 s);
    inversion EQ; f_equal; eauto.
Qed.

End Product_SSPF.


Section Exponential_SSPF.

Variable A : Type.

Definition exp_map X Y (f: X -> Y) (x: A -> X) :=
  fun (a: A) => f (x a).

Inductive on_image X : (A -> X) -> X -> Type :=
  | _on_image f a : on_image f (f a).

Definition exp_uni X Y (x: A -> X) (ALL: forall y, on_image x y -> Y)
  : A -> Y := fun y => (ALL _ (_on_image x y)).

Definition exp_eq X (EQ: X -> X -> Prop) (x1 x2: A -> X) : Prop :=
  forall a, EQ (x1 a) (x2 a).

Program Definition exp_Fn :=
  (@PFunctor.mk_data (fun X => A -> X) on_image exp_eq exp_map exp_uni _).
Next Obligation.
Proof.
  unfold exp_map. unfold exp_uni.
  extensionality s.
  rewrite INV. auto.
Defined.

Definition exp_embed X (x: A -> X) (s: A) : (X + False) := inl (x s).

Program Definition Expn : SSPF.t := 
  @SSPF.mk exp_Fn _ _ exp_embed _ _ _ _ _.
Next Obligation.
  unfold exp_embed. destruct X0.
  apply (SPUF._u_mem _ a). auto.
Defined.
Next Obligation.
  unfold exp_embed. inversion X0.
  subst. inversion EQ. constructor.
Defined.
Next Obligation.
  unfold exp_embed, exp_eq. split; intros.
  - unfold SPUF.u_eq; split; intros.
    + destruct e.
    + inversion H0; inversion H1. apply H.
  - destruct H.
    apply (H0 a); auto.
Defined.
Next Obligation.
  unfold exp_embed in EQ.
  extensionality s. apply equal_f with s in EQ.
  inversion EQ. auto.
Defined.

End Exponential_SSPF.

Section Dependent_function_SSPF.

Variable A: Type.
Variable B: A -> SSPF.t.

Definition depfun_map X Y (f: X -> Y) (x: forall a : A, B a X) :=
  fun (a: A) => (B a).(PFunctor.map) f (x a).

Definition depfun_mem X (f: forall a : A, B a X) (x: X) : Type :=
  sigT (fun a => (B a).(PFunctor.mem) (f a) x).

Definition depfun_eq X (EQ: X -> X -> Prop) (x1 x2: forall a : A, B a X) : Prop :=
  forall a, (B a).(PFunctor.eq) EQ (x1 a) (x2 a).

Definition depfun_uni X Y (x: forall a : A, B a X)
           (ALL: forall y, depfun_mem x y -> Y) : forall a : A, B a Y :=
  (fun a => (B a).(PFunctor.uni) (x a)
      (fun y r =>ALL y (existT (fun a => (B a).(PFunctor.mem) (x a) y) _ r))).

Program Definition depfun_Fn :=
  (@PFunctor.mk_data (fun X => forall a : A, B a X)
                     depfun_mem depfun_eq depfun_map depfun_uni _).
Next Obligation.
Proof.
  unfold depfun_map. unfold depfun_uni.
  extensionality s.
  apply (B s).(PFunctor.uni_correct).
  intros. apply INV.
Defined.

Definition depfun_embed X (x: forall a : A, B a X) (s: sigT (fun a => SSPF.Sh (B a)))
: (X + (sigT (fun a => SSPF.Ext (B a)))) :=
  match s with
  | existT _ a sh =>
    match (B a).(SSPF.emb) _ (x a) sh with
    | inl v => inl v
    | inr v => inr (existT _ a v)
    end
  end.

Program Definition Depend_Fun : SSPF.t := 
  @SSPF.mk depfun_Fn _ _ depfun_embed _ _ _ _ _.
Next Obligation.
  unfold depfun_embed. inversion X0.
  apply (B x0).(SSPF.mem_nat1) in X1.
  inversion X1. subst.
  apply (SPUF._u_mem _ (existT _ x0 s)).
  rewrite EQ. auto.
Defined.
Next Obligation.
  inversion X0. subst.
  destruct s.
  apply (existT _ x0).
  apply (B x0).(SSPF.mem_nat2).
  apply (SPUF._u_mem _ s). simpl in *.
  destruct ((SSPF.emb (B x0)) X (fx x0)); inversion EQ. auto.
Defined.
Next Obligation.
  unfold depfun_map. unfold depfun_embed.
  rewrite SSPF.map_nat. unfold SPUF.map.
  destruct ((SSPF.emb (B s)) X (x s)); auto.
Defined.
Next Obligation.
  unfold depfun_eq, depfun_embed; split; intros.
  - split; intros; destruct s; specialize (H x); apply SSPF.eq_nat in H; destruct H.
    + split; intros.
      destruct (SSPF.emb (B x) X (fx1 x)) eqn : EQ1; inversion H1.
      apply H in EQ1. rewrite EQ1. auto.
      destruct (SSPF.emb (B x) X (fx2 x)) eqn : EQ1; inversion H1.
      apply H in EQ1. rewrite EQ1. auto.
    + destruct (SSPF.emb (B x) X (fx1 x)) eqn : EQ1; inversion H0;
      destruct (SSPF.emb (B x) X (fx2 x)) eqn : EQ2; inversion H1; subst.
      apply (H2 _ _ _ EQ1 EQ2).
  - destruct H. apply SSPF.eq_nat. split; intros.
    + split; intros;
      specialize (H (existT _ a s) (existT _ a e)); simpl in H; destruct H.
      * rewrite H1 in H. specialize (H eq_refl). 
        destruct (SSPF.emb (B a) X (fx2 a)); inversion H.
        dependent destruction H4. auto.
      * rewrite H1 in H2. specialize (H2 eq_refl). 
        destruct (SSPF.emb (B a) X (fx1 a)); inversion H2.
        dependent destruction H4. auto.
    + specialize (H0 (existT _ a s) x1 x2). simpl in H0.
      rewrite H1 in H0; rewrite H2 in H0.
      apply H0; auto.
Defined.
Next Obligation.
  extensionality s. apply SSPF.inj.
  extensionality sh.
  unfold depfun_embed in EQ.
  apply equal_f with (existT _ s sh) in EQ.
  destruct ((SSPF.emb (B s)) X (m s)), ((SSPF.emb (B s)) X (n s));
  inversion EQ; auto.
  dependent destruction H0.
  auto.
Qed.

End Dependent_function_SSPF.

Section Dependent_sum_SSPF.

Variable A: Type.
Variable B: A -> SSPF.t.

Definition depsum_map X Y (f: X -> Y) (x: sigT (fun a => (B a) X)) : (sigT (fun a => (B a) Y)) :=
  match x with
  | existT _ a x' => existT _ a ((B a).(PFunctor.map) f x') end.

Definition depsum_mem X (x: sigT (fun a => (B a) X)) : X -> Type :=
  match x with
  | existT _ a x' => (B a).(PFunctor.mem) x' end.

Inductive depsum_eq X (EQ: X -> X -> Prop)
  : (sigT (fun a => (B a) X)) -> (sigT (fun a => (B a) X)) -> Prop :=
  | _depsum_eq a fx1 fx2 : (B a).(PFunctor.eq) EQ fx1 fx2 ->
                           depsum_eq EQ (existT _ a fx1) (existT _ a fx2).

Definition depsum_uni X Y (x: sigT (fun a => (B a) X))
           (ALL: forall y, depsum_mem x y -> Y) : (sigT (fun a => (B a) Y)).
  destruct x.
  apply (existT _ x ((B x).(PFunctor.uni) f (fun x0 r => ALL _ r))).
Defined.

Program Definition depsum_Fn :=
  (@PFunctor.mk_data (fun X => sigT (fun a => (B a) X)) depsum_mem depsum_eq
                     depsum_map depsum_uni _).
Next Obligation.
Proof.
  unfold depsum_map. unfold depsum_uni.
  f_equal. apply (B a).(PFunctor.uni_correct).
  intros. apply INV.
Defined.

Definition depsum_embed X (x: sigT (fun a => (B a) X))
           (s: sigT (fun a => sum unit (B a).(SSPF.Sh))) :
  sum X (sum bool (sigT (fun a => (B a).(SSPF.Ext)))) :=
match x with
| existT _ a x' =>
  match s with
  | existT _ a' sh =>
    match (excluded_middle_informative (a = a')) with
    | left pf =>
      match sh with
      | inl _ => inr (inl true)
      | inr sh' =>
        match (B a').(SSPF.emb) _ (eq_rect _ (fun y => (B y) X) x' _ pf) sh' with
        | inl a => inl a
        | inr b => inr (inr (existT _ a' b)) end
      end
    | right _ => inr (inl false)
    end
  end
end.

Program Definition Depend_Sum : SSPF.t :=
  @SSPF.mk depsum_Fn _ _ depsum_embed _ _ _ _ _.
Next Obligation.
  unfold depsum_embed. simpl in X0.
  apply (B fx).(SSPF.mem_nat1) in X0.
  inversion X0. subst.
  apply (SPUF._u_mem _ (existT _ fx (inr s))).
  destruct (excluded_middle_informative (fx = fx)).
  - rewrite <- eq_rect_eq.
    destruct ((SSPF.emb (B fx)) X X1); inversion EQ. auto.
  - destruct n. auto.
Defined.
Next Obligation.
  unfold depsum_embed in X0.
  inversion X0. subst.
  destruct s. destruct s.
  - destruct (excluded_middle_informative (fx = x0)); inversion EQ.
  - destruct (excluded_middle_informative (fx = x0)); subst; simpl.
    + rewrite <- eq_rect_eq in EQ.
      apply SSPF.mem_nat2.
      apply (SPUF._u_mem _ s).
      destruct (SSPF.emb (B x0) X X1); inversion EQ. auto.
    + inversion EQ.
Defined.
Next Obligation.
Proof.
  unfold depsum_embed, depsum_map, SPUF.map.
  destruct X0;
  destruct (excluded_middle_informative (x = s)); auto.
  destruct e. simpl.
  rewrite SSPF.map_nat. unfold SPUF.map.
  destruct ((SSPF.emb (B x)) X X1); auto.
Defined.
Next Obligation.
  unfold depsum_embed; split; intros.
  - dependent destruction H.
    apply SSPF.eq_nat in H. inversion H.
    split; intros; dependent destruction s; dependent destruction s; subst.
    + destruct (excluded_middle_informative (fx2 = x)); tauto.
    + split; intros;
      destruct (excluded_middle_informative (fx2 = x)); auto;
      destruct (SSPF.emb (B x) X (eq_rect fx2 (fun y : A => (B y) X) X1 x e0)) eqn : EQ1;        
      destruct (SSPF.emb (B x) X (eq_rect fx2 (fun y : A => (B y) X) X0 x e0)) eqn : EQ2; inversion H2; subst;
      replace (eq_rect x (fun y : A => (B y) X) X1 x eq_refl) with X1 in EQ1;
      replace (eq_rect x (fun y : A => (B y) X) X0 x eq_refl) with X0 in EQ2;
      try (apply H0 in EQ1; rewrite EQ1 in EQ2; inversion EQ2);
      try (apply H0 in EQ2; rewrite EQ1 in EQ2; inversion EQ2);
      try (rewrite <- eq_rect_eq; auto); auto.
    + destruct (excluded_middle_informative (fx2 = x)); inversion H2.
    + destruct (excluded_middle_informative (fx2 = x)); subst.
      replace (eq_rect x (fun y : A => (B y) X) X1 x eq_refl) with X1 in H2;
      replace (eq_rect x (fun y : A => (B y) X) X0 x eq_refl) with X0 in H3.
      destruct (SSPF.emb (B x) X X0 s) eqn : EQ1;
      destruct (SSPF.emb (B x) X X1 s) eqn : EQ2; inversion H3; inversion H2; subst.
      apply (H1 _ _ _ EQ2 EQ1).
      { rewrite <- eq_rect_eq; auto. }
      { rewrite <- eq_rect_eq; auto. }
      { rewrite <- eq_rect_eq; auto. }
      inversion H2.
  - destruct H.
    assert (fx2 = fx1).
    { specialize (H (existT _ fx2 (inl tt) : {a : A & (unit + SSPF.Sh (B a))%type}) 
                    (inl false)). simpl in H.
      destruct (excluded_middle_informative (fx1 = fx2)); auto.
      destruct (excluded_middle_informative (fx2 = fx2)).
      - destruct H. specialize (H eq_refl). inversion H.
      - destruct n0; auto. } subst.
    constructor. apply SSPF.eq_nat.
    split; intros.
    + split; intros.
      * clear H0.
        specialize (H (existT _ fx1 (inr s) : {a : A & (unit + SSPF.Sh (B a))%type})
                   (inr (existT _ fx1 e))). simpl in H.
        destruct (excluded_middle_informative (fx1 = fx1)).
        replace (eq_rect fx1 (fun y : A => (B y) X) X1 fx1 e0) with X1 in H.
        replace (eq_rect fx1 (fun y : A => (B y) X) X0 fx1 e0) with X0 in H.
        rewrite H1 in H. destruct H. specialize (H eq_refl).
        destruct (SSPF.emb (B fx1) X X0 s); inversion H.
        dependent destruction H3. auto.
        { rewrite <- eq_rect_eq. auto. }
        { rewrite <- eq_rect_eq. auto. }
        destruct n; auto.
      * clear H0.
        specialize (H (existT _ fx1 (inr s) : {a : A & (unit + SSPF.Sh (B a))%type})
                   (inr (existT _ fx1 e))). simpl in H.
        destruct (excluded_middle_informative (fx1 = fx1)).
        replace (eq_rect fx1 (fun y : A => (B y) X) X1 fx1 e0) with X1 in H.
        replace (eq_rect fx1 (fun y : A => (B y) X) X0 fx1 e0) with X0 in H.
        rewrite H1 in H. destruct H. specialize (H0 eq_refl).
        destruct (SSPF.emb (B fx1) X X1 s); inversion H0.
        dependent destruction H3. auto.
        { rewrite <- eq_rect_eq. auto. }
        { rewrite <- eq_rect_eq. auto. }
        destruct n; auto.
    + clear H.
      specialize (H0 (existT _ fx1 (inr s) : {a : A & (() + SSPF.Sh (B a))%type}) 
                     x1 x2). simpl in H0.
      destruct (excluded_middle_informative (fx1 = fx1)).
      replace (eq_rect fx1 (fun y : A => (B y) X) X1 fx1 e) with X1 in H0.
      replace (eq_rect fx1 (fun y : A => (B y) X) X0 fx1 e) with X0 in H0.
      rewrite H1 in H0. rewrite H2 in H0.
      apply H0; auto.
      { rewrite <- eq_rect_eq. auto. }
      { rewrite <- eq_rect_eq. auto. }
      destruct n; auto.
Qed.
Next Obligation.
  unfold depsum_embed in EQ.
  assert (H:= equal_f EQ (existT _ m (inl tt))). simpl in H.
  destruct (excluded_middle_informative (m = m));
  destruct (excluded_middle_informative (n = m)); inversion H; subst.
  - f_equal. apply SSPF.inj. extensionality s.
    apply equal_f with (x:= (existT _ m (inr s))) in EQ.
    destruct (excluded_middle_informative (m = m)).
    + replace (eq_rect m (fun y : A => (B y) X) X1 m e0) with X1 in EQ.
      replace (eq_rect m (fun y : A => (B y) X) X0 m e0) with X0 in EQ.
      destruct (SSPF.emb (B m) X X1),(SSPF.emb (B m) X X0); inversion EQ; auto.      
      dependent destruction H1. auto.
      { rewrite <- eq_rect_eq. auto. }
      { rewrite <- eq_rect_eq. auto. }
    + destruct n. auto.
  - destruct n0. auto.
Defined.

End Dependent_sum_SSPF.

Section Option_SSPF.

Definition opt_mem X (x: option X) : X -> Type :=
  match x with
  | None => (fun y => False)
  | Some x' => eq x' end.

Inductive opt_eq (X : Type) (EQ: X -> X -> Prop) : option X -> option X -> Prop :=
  | _opt_eq_none : opt_eq EQ None None
  | _opt_eq_some x1 x2 : EQ x1 x2 -> opt_eq EQ (Some x1) (Some x2).

Definition opt_uni X Y (x: option X) (ALL: forall y, opt_mem x y -> Y)
  : option Y.
  destruct x.
  - apply (Some (ALL _ (eq_refl x))).
  - apply None.
Defined.

Program Definition opt_Fn :=
  (@PFunctor.mk_data option opt_mem opt_eq option_map opt_uni _).
Next Obligation.
Proof.
  unfold option_map. destruct a; unfold opt_uni.
  - rewrite INV. auto.
  - auto.
Defined.

Definition opt_embed X (x: option X) (s: unit) :=
  match x with
  | Some x' => inl x'
  | None => inr tt
  end.

Program Definition Option_sspf : SSPF.t := 
  @SSPF.mk opt_Fn _ _ opt_embed _ _ _ _ _.
Next Obligation.
  unfold opt_embed. destruct fx; inversion X0.
  - apply (SPUF._u_mem _ tt). auto.
Defined.
Next Obligation.
  unfold opt_embed in X0. inversion X0. subst.
  destruct fx; inversion EQ.
  constructor.
Defined.
Next Obligation.
  destruct x; auto.
Defined.
Next Obligation.
  unfold opt_embed; split; intros.
  - inversion H; split; intros.
    + tauto.
    + inversion H2.
    + split; intro; inversion H3.
    + inversion H3. inversion H4. subst. auto.
  - inversion H. destruct fx1, fx2.
    + constructor. apply (H1 tt); auto.
    + destruct (H0 tt tt). specialize (H3 eq_refl). inversion H3.
    + destruct (H0 tt tt). specialize (H2 eq_refl). inversion H2.
    + constructor.
Defined.
Next Obligation.
Proof.
  apply equal_f with tt in EQ.
  destruct m, n; inversion EQ; auto.
Qed.

End Option_SSPF.


Section Composition_SSPF.

Variable F G: SSPF.t.

Definition comp_embed' X (x': F.(SSPF.Sh) -> (sum (G.(SSPF.Sh) ->
                                                 (sum X G.(SSPF.Ext))) F.(SSPF.Ext)))
           (s: prod (sum unit G.(SSPF.Sh)) F.(SSPF.Sh)) :=
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

Lemma comp_embed'_injective X x y : @comp_embed' X x = comp_embed' y -> x = y.
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

Definition comp_embed X (x: F (G X)) :=
  comp_embed' (F.(SSPF.emb) _ (F.(PFunctor.map) (G.(SSPF.emb) X) x)).

Program Definition Comp : SSPF.t := 
  @SSPF.mk (comp_Fn F G) _ _ comp_embed _ _ _ _ _.
Next Obligation.
  unfold comp_embed, comp_embed'.
  inversion X0. subst.
  apply F.(SSPF.mem_nat1) in HF.
  apply G.(SSPF.mem_nat1) in HG.
  inversion HG. inversion HF. subst.
  apply (SPUF._u_mem _ (inr s, s0)).
  repeat rewrite SSPF.map_nat. simpl. unfold SPUF.map.
  destruct ((SSPF.emb F) (G X) fx); inversion EQ0.
  destruct ((SSPF.emb G) X gx); inversion EQ. auto.
Defined.
Next Obligation.
  unfold comp_embed, comp_embed' in X0.
  inversion X0. clear X0. subst.
  destruct s. destruct s;
  repeat rewrite SSPF.map_nat in EQ; unfold SPUF.map in EQ;
  destruct ((SSPF.emb F) (G X) fx) eqn: H1; inversion EQ.
  destruct ((SSPF.emb G) X f) eqn: H2; inversion EQ. subst.
  apply (_comp_mem F G _ f).
  apply G.(SSPF.mem_nat2). simpl. apply (SPUF._u_mem _ s H2).
  apply F.(SSPF.mem_nat2). simpl. apply (SPUF._u_mem _ s0 H1).
Defined.
Next Obligation.
  destruct s;
  unfold SPUF.map, comp_embed, comp_map, comp_embed';
  repeat rewrite SSPF.map_nat; unfold SPUF.map;
  rewrite SSPF.map_nat; unfold SPUF.map;
  destruct (SSPF.emb F (G X) x); auto.
  rewrite SSPF.map_nat; unfold SPUF.map.
  destruct (SSPF.emb G X f0); auto.
Defined.
Next Obligation.
  unfold comp_embed, comp_eq, comp_embed'. split; intros.
  - split; intros.
    + split; intros; destruct s.
      * destruct s.
        --apply SSPF.eq_nat in H.
          inversion H.
          rewrite SSPF.map_nat. rewrite SSPF.map_nat in H0. unfold SPUF.map in *.
          destruct (SSPF.emb F (G X) fx1) eqn : EQ1;
          destruct (SSPF.emb F (G X) fx2) eqn : EQ2.
          ++auto.
          ++apply H1 in EQ2. simpl in *. rewrite EQ2 in EQ1. inversion EQ1.
          ++apply H1 in EQ1. simpl in *. rewrite EQ2 in EQ1. inversion EQ1.
          ++apply H1 in EQ1. simpl in *. rewrite EQ2 in EQ1. inversion EQ1.
            symmetry. auto.
        --repeat rewrite SSPF.map_nat in *. unfold SPUF.map in *.
          apply SSPF.eq_nat in H. inversion H.
          destruct (SSPF.emb F (G X) fx1) eqn : EQ1;
          destruct (SSPF.emb F (G X) fx2) eqn : EQ2.

          destruct (SSPF.emb G X f) eqn : EQ3;
          destruct (SSPF.emb G X f0) eqn : EQ4; inversion H0;
          specialize (H2 _ _ _ EQ1 EQ2); apply SSPF.eq_nat in H2; inversion H2.
          ++apply H3 in EQ3. rewrite EQ3 in EQ4. inversion EQ4.
          ++apply H3 in EQ3. rewrite EQ3 in EQ4. inversion EQ4. auto.

          ++destruct (SSPF.emb G X f); inversion H0.
            apply H1 in EQ2. simpl in *. rewrite EQ1 in EQ2. inversion EQ2.
          ++apply H1 in EQ1. simpl in *. rewrite EQ1 in EQ2. inversion EQ2.
          ++apply H1 in EQ1. simpl in *. rewrite EQ1 in EQ2. inversion EQ2. auto.
      * destruct s.
        --repeat rewrite SSPF.map_nat in *. unfold SPUF.map in *.
          apply SSPF.eq_nat in H. destruct H.
          destruct (SSPF.emb F (G X) fx1) eqn : EQ1;
          destruct (SSPF.emb F (G X) fx2) eqn : EQ2; inversion H0; auto.
          ++apply H in EQ2. simpl in *. rewrite EQ2 in EQ1. inversion EQ1.
          ++apply H in EQ1. simpl in *. rewrite EQ2 in EQ1. inversion EQ1.
          ++apply H in EQ2. simpl in *. rewrite EQ2 in EQ1. inversion EQ1. auto.
        --repeat rewrite SSPF.map_nat in *. unfold SPUF.map in *.
          apply SSPF.eq_nat in H. destruct H.
          destruct (SSPF.emb F (G X) fx1) eqn : EQ1;
          destruct (SSPF.emb F (G X) fx2) eqn : EQ2.
          ++specialize (H1 _ _ _ EQ1 EQ2). apply SSPF.eq_nat in H1. destruct H1.
            destruct (SSPF.emb G X f0) eqn : EQ3;
            destruct (SSPF.emb G X f) eqn : EQ4; inversion H0.
            **apply H1 in EQ3. rewrite EQ3 in EQ4. inversion EQ4.
            **apply H1 in EQ3. rewrite EQ3 in EQ4. inversion EQ4. auto.
          ++apply H in EQ2. simpl in *. rewrite EQ2 in EQ1. inversion EQ1.
          ++apply H in EQ1. simpl in *. rewrite EQ2 in EQ1. inversion EQ1.
          ++apply H in EQ2. simpl in *. rewrite EQ2 in EQ1. inversion EQ1. auto.
    + destruct s. repeat rewrite SSPF.map_nat in *. unfold SPUF.map in *.
      repeat rewrite SSPF.map_nat in *. apply SSPF.eq_nat in H. destruct H.
      destruct s.
      * destruct (SSPF.emb F (G X) fx1) eqn : EQ1;
        destruct (SSPF.emb F (G X) fx2) eqn : EQ2; inversion H0; inversion H1.
      * destruct (SSPF.emb F (G X) fx1) eqn : EQ1;
        destruct (SSPF.emb F (G X) fx2) eqn : EQ2; inversion H0; inversion H1.
        specialize (H2 _ _ _ EQ1 EQ2). apply SSPF.eq_nat in H2. destruct H2.
        destruct (SSPF.emb G X f s) eqn : EQ3;
        destruct (SSPF.emb G X f0 s) eqn : EQ4; inversion H4; inversion H5.
        subst. apply (H3 _ _ _ EQ3 EQ4).
  - apply SSPF.eq_nat. destruct H. split; intros.
    + split; intros;
      specialize (H (inl tt, s) (inr (inr e))); simpl in *; clear H0;
      repeat rewrite SSPF.map_nat in H; unfold SPUF.map in H;
      rewrite H1 in H; destruct H.
      * specialize (H eq_refl);
        destruct (SSPF.emb F (G X) fx2 s); inversion H. auto.
      * specialize (H0 eq_refl);
        destruct (SSPF.emb F (G X) fx1 s); inversion H0. auto.
    + apply SSPF.eq_nat. split; intros.
      * split; intros;
        specialize (H (inr s0, s) (inr (inl e))); simpl in *; clear H0;
        repeat rewrite SSPF.map_nat in H; unfold SPUF.map in H;
        rewrite H1 in H; rewrite H2 in H; rewrite H3 in H;
        destruct H.
        -- specialize (H eq_refl);
           destruct (SSPF.emb G X x2 s0); inversion H. auto.
        -- specialize (H0 eq_refl).
           destruct (SSPF.emb G X x1 s0); inversion H0. auto.
      * specialize (H0 (inr s0, s) x0 x3). simpl in *. clear H.
        repeat rewrite SSPF.map_nat in H0. unfold SPUF.map in H0.
        rewrite H1 in H0. rewrite H2 in H0. rewrite H3 in H0. rewrite H4 in H0.
        apply H0; auto.
Qed.
Next Obligation.
  unfold comp_embed in EQ.
  apply comp_embed'_injective in EQ.
  apply SSPF.inj in EQ. apply SSPF.map_injective in EQ.
  apply EQ. apply SSPF.inj.
Defined.

End Composition_SSPF.


Section Dependent_sum_dec_SSPF.

Variable A: Type.
Variable B: A -> SSPF.t.
Variable eq_dec: forall (a1 a2 : A), {a1=a2} + {a1<>a2}.

Definition depsum_dec_map X Y (f: X -> Y) (x: sigT (fun a => (B a) X))
  : (sigT (fun a => (B a) Y)) :=
  match x with
  | existT _ a x' => existT _ a ((B a).(PFunctor.map) f x') end.

Definition depsum_dec_mem X (x: sigT (fun a => (B a) X)) : X -> Type :=
  match x with
  | existT _ a x' => (B a).(PFunctor.mem) x' end.

Inductive depsum_dec_eq X (EQ: X -> X -> Prop)
  : (sigT (fun a => (B a) X)) -> (sigT (fun a => (B a) X)) -> Prop :=
  | _depsum_dec_eq a fx1 fx2 : (B a).(PFunctor.eq) EQ fx1 fx2 -> 
                         depsum_dec_eq EQ (existT _ a fx1) (existT _ a fx2).

Definition depsum_dec_uni X Y (x: sigT (fun a => (B a) X))
           (ALL: forall y, depsum_dec_mem x y -> Y) : (sigT (fun a => (B a) Y)).
  destruct x.
  apply (existT _ x ((B x).(PFunctor.uni) f (fun x0 r => ALL _ r))).
Defined.

Program Definition depsum_dec_Fn :=
  (@PFunctor.mk_data (fun X => sigT (fun a => (B a) X)) depsum_dec_mem
                     depsum_dec_eq depsum_dec_map depsum_dec_uni _).
Next Obligation.
Proof.
  unfold depsum_dec_map. unfold depsum_dec_uni.
  f_equal. apply (B a).(PFunctor.uni_correct).
  intros. apply INV.
Defined.

Definition depsum_dec_embed X (x: sigT (fun a => (B a) X))
           (s: sigT (fun a => sum unit (B a).(SSPF.Sh))) :
  sum X (sum bool (sigT (fun a => (B a).(SSPF.Ext)))) :=
match x with
| existT _ a x' =>
  match s with
  | existT _ a' sh =>
    match (eq_dec a a') with
    | left pf =>
      match sh with
      | inl _ => inr (inl true)
      | inr sh' =>
        match (B a').(SSPF.emb) _ (eq_rect _ (fun y => (B y) X) x' _ pf) sh' with
        | inl a => inl a
        | inr b => inr (inr (existT _ a' b)) end
      end
    | right _ => inr (inl false)
    end
  end
end.

Program Definition Depend_dec_Sum : SSPF.t :=
  @SSPF.mk depsum_dec_Fn _ _ depsum_dec_embed _ _ _ _ _.
Next Obligation.
  unfold depsum_dec_embed. simpl in X0.
  apply (B fx).(SSPF.mem_nat1) in X0.
  inversion X0. subst.
  apply (SPUF._u_mem _ (existT _ fx (inr s))).
  destruct (eq_dec fx fx).
  - rewrite <- (eq_rect_eq_dec eq_dec).
    destruct ((SSPF.emb (B fx)) X X1); inversion EQ. auto.
  - destruct n. auto.
Defined.
Next Obligation.
  unfold depsum_dec_embed in X0.
  inversion X0. subst.
  destruct s. destruct s.
  - destruct (eq_dec fx x0); inversion EQ.
  - destruct (eq_dec fx x0); subst; simpl.
    + rewrite <- (eq_rect_eq_dec eq_dec) in EQ.
      apply SSPF.mem_nat2.
      apply (SPUF._u_mem _ s).
      destruct (SSPF.emb (B x0) X X1); inversion EQ. auto.
    + inversion EQ.
Defined.
Next Obligation.
Proof.
  unfold depsum_dec_embed, depsum_dec_map, SPUF.map.
  destruct X0;
  destruct (eq_dec x s); auto.
  destruct e. simpl.
  rewrite SSPF.map_nat. unfold SPUF.map.
  destruct ((SSPF.emb (B x)) X X1); auto.
Defined.
Next Obligation.
  unfold depsum_dec_embed; split; intros.
  - dependent destruction H.
    apply SSPF.eq_nat in H. inversion H.
    split; intros; dependent destruction s; dependent destruction s; subst.
    + destruct (eq_dec fx2 x); tauto.
    + split; intros;
      destruct (eq_dec fx2 x); auto;
      destruct (SSPF.emb (B x) X (eq_rect fx2 (fun y : A => (B y) X) X1 x e0)) eqn : EQ1;        
      destruct (SSPF.emb (B x) X (eq_rect fx2 (fun y : A => (B y) X) X0 x e0)) eqn : EQ2; inversion H2; subst;
      replace (eq_rect x (fun y : A => (B y) X) X1 x eq_refl) with X1 in EQ1;
      replace (eq_rect x (fun y : A => (B y) X) X0 x eq_refl) with X0 in EQ2;
      try (apply H0 in EQ1; rewrite EQ1 in EQ2; inversion EQ2);
      try (apply H0 in EQ2; rewrite EQ1 in EQ2; inversion EQ2);
      try (rewrite <- (eq_rect_eq_dec eq_dec); auto); auto.
    + destruct (eq_dec fx2 x); inversion H2.
    + destruct (eq_dec fx2 x); subst.
      replace (eq_rect x (fun y : A => (B y) X) X1 x eq_refl) with X1 in H2;
      replace (eq_rect x (fun y : A => (B y) X) X0 x eq_refl) with X0 in H3.
      destruct (SSPF.emb (B x) X X0 s) eqn : EQ1;
      destruct (SSPF.emb (B x) X X1 s) eqn : EQ2; inversion H3; inversion H2; subst.
      apply (H1 _ _ _ EQ2 EQ1).
      { rewrite <- (eq_rect_eq_dec eq_dec); auto. }
      { rewrite <- (eq_rect_eq_dec eq_dec); auto. }
      { rewrite <- (eq_rect_eq_dec eq_dec); auto. }
      inversion H2.
  - destruct H.
    assert (fx2 = fx1).
    { specialize (H (existT _ fx2 (inl tt) : {a : A & (unit + SSPF.Sh (B a))%type}) 
                    (inl false)). simpl in H.
      destruct (eq_dec fx1 fx2); auto.
      destruct (eq_dec fx2 fx2).
      - destruct H. specialize (H eq_refl). inversion H.
      - destruct n0; auto. } subst.
    constructor. apply SSPF.eq_nat.
    split; intros.
    + split; intros.
      * clear H0.
        specialize (H (existT _ fx1 (inr s) : {a : A & (unit + SSPF.Sh (B a))%type})
                   (inr (existT _ fx1 e))). simpl in H.
        destruct (eq_dec fx1 fx1).
        replace (eq_rect fx1 (fun y : A => (B y) X) X1 fx1 e0) with X1 in H.
        replace (eq_rect fx1 (fun y : A => (B y) X) X0 fx1 e0) with X0 in H.
        rewrite H1 in H. destruct H. specialize (H eq_refl).
        destruct (SSPF.emb (B fx1) X X0 s); inversion H.
        dependent destruction H3. auto.
        { rewrite <- (eq_rect_eq_dec eq_dec). auto. }
        { rewrite <- (eq_rect_eq_dec eq_dec). auto. }
        destruct n; auto.
      * clear H0.
        specialize (H (existT _ fx1 (inr s) : {a : A & (unit + SSPF.Sh (B a))%type})
                   (inr (existT _ fx1 e))). simpl in H.
        destruct (eq_dec fx1 fx1).
        replace (eq_rect fx1 (fun y : A => (B y) X) X1 fx1 e0) with X1 in H.
        replace (eq_rect fx1 (fun y : A => (B y) X) X0 fx1 e0) with X0 in H.
        rewrite H1 in H. destruct H. specialize (H0 eq_refl).
        destruct (SSPF.emb (B fx1) X X1 s); inversion H0.
        dependent destruction H3. auto.
        { rewrite <- (eq_rect_eq_dec eq_dec). auto. }
        { rewrite <- (eq_rect_eq_dec eq_dec). auto. }
        destruct n; auto.
    + clear H.
      specialize (H0 (existT _ fx1 (inr s) : {a : A & (() + SSPF.Sh (B a))%type}) 
                     x1 x2). simpl in H0.
      destruct (eq_dec fx1 fx1).
      replace (eq_rect fx1 (fun y : A => (B y) X) X1 fx1 e) with X1 in H0.
      replace (eq_rect fx1 (fun y : A => (B y) X) X0 fx1 e) with X0 in H0.
      rewrite H1 in H0. rewrite H2 in H0.
      apply H0; auto.
      { rewrite <- (eq_rect_eq_dec eq_dec). auto. }
      { rewrite <- (eq_rect_eq_dec eq_dec). auto. }
      destruct n; auto.
Qed.
Next Obligation.
  unfold depsum_dec_embed in EQ.
  assert (H:= equal_f EQ (existT _ m (inl tt))). simpl in H.
  destruct (eq_dec m m);
  destruct (eq_dec n m); inversion H; subst.
  - f_equal. apply SSPF.inj. extensionality s.
    apply equal_f with (x:= (existT _ m (inr s))) in EQ.
    destruct (eq_dec m m).
    + replace (eq_rect m (fun y : A => (B y) X) X1 m e0) with X1 in EQ.
      replace (eq_rect m (fun y : A => (B y) X) X0 m e0) with X0 in EQ.
      destruct (SSPF.emb (B m) X X1),(SSPF.emb (B m) X X0); inversion EQ; auto.
      apply (inj_pair2_eq_dec _ eq_dec) in H1. subst. auto.
      { rewrite <- (eq_rect_eq_dec eq_dec). auto. }
      { rewrite <- (eq_rect_eq_dec eq_dec). auto. }
    + destruct n. auto.
  - destruct n0. auto.
Defined.

End Dependent_sum_dec_SSPF.

Section List_SSPF.

Fixpoint list_mem X (l: list X) (x: X) : Type :=
  match l with
  | nil => False
  | cons hd tl => eq hd x + list_mem tl x end.

Inductive list_eq (X : Type) (EQ: X -> X -> Prop) : list X -> list X -> Prop :=
  | _list_eq_nil : list_eq EQ nil nil
  | _list_eq_cons hd1 hd2 tl1 tl2 (HD: EQ hd1 hd2) (TL: list_eq EQ tl1 tl2) : 
      (list_eq EQ (cons hd1 tl1) (cons hd2 tl2)).

Definition list_uni X Y (x: list X) (ALL: forall y, list_mem x y -> Y) : list Y.
  induction x.
  - apply nil.
  - apply cons.
    + apply (ALL a (inl (eq_refl a))).
    + apply IHx. intros.
      apply (ALL y (inr X0)).
Defined.

Definition list_uni_correct : forall X Y (a: list X) (ALL: forall x, list_mem a x -> Y)
                       (f: Y -> X) (INV: forall x r, f (ALL x r) = x),
    List.map f (list_uni _ ALL) = a.
Proof.
  intros. induction a.
  - auto.
  - simpl. f_equal.
    + apply INV.
    + apply IHa. intros. apply INV.
Defined.

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

Program Definition List_sspf : SSPF.t := 
  @SSPF.mk (PFunctor.mk_data list list_mem list_eq List.map list_uni 
                             list_uni_correct) _ _ list_embed _ _ _ _ _.
Next Obligation.
  induction fx; inversion X0; subst.
  - apply (SPUF._u_mem _ (cons tt nil)). auto.
  - apply IHfx in X1.
    inversion X1. subst.
    apply (SPUF._u_mem _ (cons tt s)).
    destruct s.
    + destruct fx; inversion EQ.
    + auto.
Defined.
Next Obligation. 
  induction fx; inversion X0; subst.
  - inversion EQ.
  - destruct s; inversion EQ. destruct s; inversion EQ.
    + repeat constructor.
    + apply inr. apply IHfx.
      apply (SPUF._u_mem _ (cons u0 s) EQ).
Defined.
Next Obligation.
  revert s.
  induction x; auto.
  intros. destruct s; auto. destruct s; auto.
  unfold SPUF.map in *. simpl.
  apply (IHx (cons u0 s)).
Defined.
Next Obligation.
  revert fx2. induction fx1; intros; split; intros.
  - inversion H. subst. unfold list_embed. split; intros.
    + tauto.
    + inversion H0.
  - destruct fx2. constructor. destruct H.
    specialize (H (cons tt nil) tt). unfold list_embed in H.
    destruct H. specialize (H eq_refl). inversion H.
  - inversion H. subst. clear H.
    split; intros; apply (IHfx1 tl2) in TL; destruct TL.
    + split; (intros; simpl in *;
      destruct s; [auto | ]; destruct s; [inversion H1| ]);
      apply H; auto.
    + destruct s. simpl in *. inversion H.
      simpl in *. destruct s. inversion H. inversion H0. subst. auto.
      apply (H2 _ _ _ H H0).
  - destruct H. destruct fx2.
    + specialize (H (cons tt nil) tt). destruct H.
      simpl in H1. specialize (H1 eq_refl). inversion H1.
    + specialize (IHfx1 fx2). destruct IHfx1.
      constructor.
      specialize (H0 (cons tt nil)). simpl in H0.
      apply H0; auto.
      
      apply H2.
      split; intros.
      * split; intros;
        specialize (H (cons tt s) tt); simpl in H;
        destruct s.
        -- destruct fx1. simpl in H3. inversion H3.
           destruct fx2. simpl. auto.
           simpl. auto.
           simpl in H3.
           destruct fx2. auto. auto.
        -- destruct e. apply H. auto.
        -- destruct fx2. simpl in H3. inversion H3.
           destruct fx1. simpl. auto.
           simpl. auto.
           simpl in H3.
           destruct fx1. auto. simpl. auto.
        -- destruct e. apply H. auto.
      * specialize (H0 (cons tt s) x1 x2). simpl in H0.
        destruct s. 
        destruct fx1. inversion H3. inversion H3.
        apply (H0 H3 H4).
Qed.
Next Obligation.
Proof.
  assert (EQ' := equal_f EQ). clear EQ.
  revert n EQ'. induction m; intros.
  - destruct n; eauto. 
    specialize (EQ' (cons tt nil)). inversion EQ'.
  - destruct n.
    + specialize (EQ' (cons tt nil)). inversion EQ'.
    + rewrite (IHm n).
      * specialize (EQ' (cons tt nil)). inversion EQ'; subst; auto.
      * intros. specialize (EQ' (cons tt x0)). 
        destruct x0; eauto.
        destruct m, n; eauto.
Defined.

End List_SSPF.


Section Embedded_SSPF.

Variable F: PFunctor.t_data.
Variable G: SSPF.t.
Variable Nt: PNatTrans.t F G.
Hypothesis inj: forall X (m n: F X) (EQ: Nt _ m = Nt _ n), m = n.

Definition embedded_embed X (x : F X) := G.(SSPF.emb) _ (Nt _ x).

Program Definition Embedded_sspf : SSPF.t := 
  @SSPF.mk F _ _ embedded_embed _ _ _ _ _.
Next Obligation.
Proof.
  apply G.(SSPF.mem_nat1), Nt.(PNatTrans.mem_nat1), X0.
Defined.
Next Obligation.
Proof.
  apply Nt.(PNatTrans.mem_nat2), G.(SSPF.mem_nat2), X0.
Defined.
Next Obligation.
  unfold embedded_embed.
  rewrite Nt.(PNatTrans.map_nat).
  apply SSPF.map_nat.
Defined.
Next Obligation.
  rewrite Nt.(PNatTrans.eq_nat).
  apply SSPF.eq_nat.
Qed.
Next Obligation.
  unfold embedded_embed in EQ.
  apply SSPF.inj in EQ.
  apply inj in EQ. auto.
Qed.

End Embedded_SSPF.

(*
Definition U Sh Ext := Comp (Expn Sh) (Coprod Ident (Const Ext)).

Lemma mem_eq1 Sh Ext X (u: Sh -> X + Ext) (x: X)
  : SPUF.u_mem u x -> (U Sh Ext).(PFunctor.mem) u x.
Proof.
  intro. inversion X0. subst. simpl.
  apply (_comp_mem (Expn Sh) (Coprod Ident (Const Ext)) _ (inl x)).
  - simpl. constructor.
  - simpl. rewrite <- EQ. constructor.
Defined.

Lemma mem_eq2 Sh Ext X (u: Sh -> X + Ext) (x: X)
  : (U Sh Ext).(PFunctor.mem) u x -> SPUF.u_mem u x.
Proof.
  intro. inversion X0. subst. simpl in *.
  destruct gx; inversion HG. subst.
  inversion HF. subst.
  econstructor. apply H1.
Defined.
*)
