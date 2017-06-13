Require Import FunctionalExtensionality ProofIrrelevance ClassicalDescription.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Logic.Eqdep_dec.
Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.
Require Import ssp.

Arguments proj1_sig {A P} e.

Section Constant_SSPF.

Variable A : Type.

Definition const_Fn :=
  (PFunctor.mk_data (fun X => A) (fun X Y (f: X -> Y) x => x) (fun _ _ _ => True)).

Definition const_embed X (a: A) (s: unit) : X + A := inr a.

Program Definition Const : SSPF.t := 
  @SSPF.mk const_Fn unit A 
          (PNatTrans.mk _ _ const_embed _ _) _ _.
Next Obligation.
  unfold SPUF.pmap. unfold const_embed.
  split; intros.
  - inversion EQ. 
  - apply I.
Qed.
Next Obligation.
  exists m. eauto.
Qed.
Next Obligation.
  unfold const_embed in EQ.
  apply equal_f with tt in EQ.
  inversion EQ. auto.
Qed.

End Constant_SSPF.

Section Identity_SSPF.

Definition ident_embed X (x: X) (s: unit) : X + unit := inl x.

Program Definition Ident : SSPF.t := 
  @SSPF.mk PFunctor.id_data unit unit
          (PNatTrans.mk _ _ ident_embed _ _) _ _.
Next Obligation.
  unfold SPUF.pmap. unfold ident_embed.
  split; intros.
  - inversion EQ. subst. apply H.
  - apply (H tt). auto.
Qed.
Next Obligation.
  exfalso. specialize (CONST m m). eauto.
Qed.
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

Definition coprod_pmap X (P: X -> Prop) x :=
  match x with
  | inl xl => F.(PFunctor.pmap) P xl
  | inr xr => G.(PFunctor.pmap) P xr
  end.

Definition coprod_Fn :=
  (PFunctor.mk_data (fun X => sum (F X) (G X)) coprod_map coprod_pmap).

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
  @SSPF.mk coprod_Fn _ _
          (PNatTrans.mk _ _ coprod_embed _ _) _ _.
Next Obligation.
  extensionality s. unfold coprod_embed, coprod_map.
  destruct x; destruct s; destruct s; try eauto;
  rewrite PNatTrans.map_nat; simpl; unfold SPUF.map;
  [destruct ((SSPF.emb F) X f0) | destruct ((SSPF.emb G) X f0)]; eauto.
Qed.
Next Obligation.
  unfold SPUF.pmap. split; intros.
  - destruct x; simpl in *;
    destruct s; destruct s; inversion EQ;
    [ apply (PNatTrans.pmap_nat F.(SSPF.emb)) in H|
    apply (PNatTrans.pmap_nat G.(SSPF.emb)) in H];
    simpl in H; unfold SPUF.pmap in H; specialize (H s x0);
    [destruct ((SSPF.emb F) X f) | destruct ((SSPF.emb G) X f)];
    inversion H1;
    apply H; subst; auto.
  - unfold coprod_pmap. destruct x.
    + apply (PNatTrans.pmap_nat F.(SSPF.emb)). simpl; unfold SPUF.pmap; intros.
      specialize (H (inl (inr s))). simpl in H.
      destruct ((SSPF.emb F) X f); inversion EQ. apply H. subst. auto.
    + apply (PNatTrans.pmap_nat G.(SSPF.emb)). simpl; unfold SPUF.pmap; intros.
      specialize (H (inr (inr s))). simpl in H.
      destruct ((SSPF.emb G) X f); inversion EQ. apply H. subst. auto.
Qed.
Next Obligation.
  unfold coprod_embed in CONST.
  destruct m.
  - assert (H : forall (s : SSPF.Sh F) (x : ()), (SSPF.emb F) unit f s <> inl x).
    { intros.
      specialize (CONST (inl (inr s)) tt). simpl in CONST.
      destruct ((SSPF.emb F) unit f).
      - destruct u; exfalso; auto. 
      - intro. inversion H.
    }
    apply SSPF.uni in H; destruct H; unfold coprod_map.
    exists (inl x); f_equal; apply H.
  - assert (H : forall (s : SSPF.Sh G) (x : ()), (SSPF.emb G) unit f s <> inl x).
    { intros.
      specialize (CONST (inr (inr s)) tt). simpl in CONST.
      destruct ((SSPF.emb G) unit f).
      - destruct u; exfalso; auto.
      - intro. inversion H.
    }
    apply SSPF.uni in H; destruct H; unfold coprod_map.
    exists (inr x); f_equal; apply H.
Qed.
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

Definition prod_pmap X (P: X -> Prop) x := 
  match x with (xf, xg) => F.(PFunctor.pmap) P xf /\ G.(PFunctor.pmap) P xg end.

Definition prod_Fn :=
  (PFunctor.mk_data (fun X => prod (F X) (G X)) prod_map prod_pmap).

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
  @SSPF.mk prod_Fn (sum F.(SSPF.Sh) G.(SSPF.Sh)) (sum F.(SSPF.Ext) G.(SSPF.Ext))
          (PNatTrans.mk _ _ prod_embed _ _) _ _.
Next Obligation.  
  extensionality s. unfold prod_map, prod_embed. repeat rewrite PNatTrans.map_nat.
  destruct s; simpl; unfold SPUF.map;
  [destruct ((SSPF.emb F) X f0) | destruct ((SSPF.emb G) X f1)]; eauto.
Qed.
Next Obligation.
  split; unfold prod_pmap; unfold SPUF.pmap; unfold prod_embed; intros.
  - destruct H.
    apply (PNatTrans.pmap_nat F.(SSPF.emb)) in H.
    apply (PNatTrans.pmap_nat G.(SSPF.emb)) in H0. simpl in *. unfold SPUF.pmap in *.
    destruct s.
    + specialize (H s). apply H.
      destruct ((SSPF.emb F) X f); inversion EQ. auto.
    + specialize (H0 s). apply H0.
      destruct ((SSPF.emb G) X f0); inversion EQ. auto.
  - split.
    + apply (PNatTrans.pmap_nat F.(SSPF.emb)). simpl. unfold SPUF.pmap. intros.
      specialize (H (inl s)). apply H.
      destruct ((SSPF.emb F) X f); inversion EQ; auto.
    + apply (PNatTrans.pmap_nat G.(SSPF.emb)). simpl. unfold SPUF.pmap. intros.
      specialize (H (inr s)). apply H.
      destruct ((SSPF.emb G) X f0); inversion EQ; auto.
Qed.
Next Obligation.
  unfold prod_embed in CONST.
  assert (H1 : forall s x, (SSPF.emb F) unit f s <> inl x).
  { intros.
    specialize (CONST (inl s) tt). simpl in CONST.
    destruct ((SSPF.emb F) unit f);
    [exfalso; destruct u; eauto | intro; inversion H].
  }
  assert (H2 : forall s x, (SSPF.emb G) unit f0 s <> inl x). intros.
  { specialize (CONST (inr s) tt). simpl in CONST.
    destruct ((SSPF.emb G) unit f0);
    [exfalso; destruct u; eauto | intro; inversion H].
  }
  apply SSPF.uni in H1. apply SSPF.uni in H2. destruct H1, H2.
  exists (x, x0).
  unfold prod_map. rewrite H. rewrite H0. eauto.
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

Definition exp_pmap X (P: X -> Prop) (x: A -> X) : Prop :=
  forall a x', x a = x' -> P x'.

Definition exp_Fn := (PFunctor.mk_data (fun X => A -> X) exp_map exp_pmap).

Definition exp_embed X (x: A -> X) (s: A) : (X + False) := inl (x s).

Program Definition Expn : SSPF.t := 
  @SSPF.mk exp_Fn _ _
          (PNatTrans.mk _ _ exp_embed _ _) _ _.
Next Obligation.
  split; unfold exp_pmap; unfold SPUF.pmap; unfold exp_embed; intros.
  - inversion EQ. apply (H s (x s)). auto.
  - apply (H a x'). f_equal. auto.
Qed.
Next Obligation.
  unfold exp_embed, exp_map in *.
  exists (fun (a: A) => (CONST a (m a)) eq_refl).
  extensionality s. destruct (m s). auto.
Qed.
Next Obligation.
  unfold exp_embed in EQ.
  extensionality s. apply equal_f with s in EQ.
  inversion EQ. auto.
Qed.

End Exponential_SSPF.

Section Composition_SSPF.

Variable F G: SSPF.t.

Definition comp_map X Y (f: X -> Y) (x: F (G X)) :=
  F.(PFunctor.map) (G.(PFunctor.map) f) x.

Definition comp_pmap X (P: X -> Prop) x := F.(PFunctor.pmap) (G.(PFunctor.pmap) P) x.

Definition comp_Fn := (PFunctor.mk_data (fun X => F (G X)) comp_map comp_pmap).

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

Lemma comp_embed'_pullback m (H: forall s x, ~ comp_embed' m s = inl x) :
  exists m', m = SPUF.map F.(SSPF.Sh) F.(SSPF.Ext)
                          (SPUF.map G.(SSPF.Sh) G.(SSPF.Ext) (False_rect unit)) m'.
Proof.
  unfold comp_embed', SPUF.map in *.
  assert (EX : forall sf,
             exists (xg: sum (G.(SSPF.Sh) -> sum False (G.(SSPF.Ext))) F.(SSPF.Ext)),
               match m sf with
               | inr ef => xg = inr ef
               | inl ug =>
                 exists xg', xg = inl xg' /\ forall sg,
                 (match ug sg with
                 | inr eg => xg' sg = inr eg
                 | inl _ => True end) end).
  { intros.
    destruct (m sf) eqn : EQ.
    - assert (EX : forall sg, exists (xg': False + SSPF.Ext G),
             match s sg with
             | inl _ => True
             | inr eg => xg' = inr eg end).
      { intros.
        specialize (H (inr sg, sf)). simpl in H. rewrite EQ in H.
        destruct (s sg). 
        - exfalso. apply (H u). auto.
        - eauto.
      }
      apply choice in EX. destruct EX. exists (inl x).
      exists x.
      split. auto. apply H0.
    - eauto.
  }
  apply choice in EX. destruct EX.
  exists x.
  extensionality sf. specialize (H0 sf).
  - destruct (m sf) eqn: EQ.
    destruct H0. destruct H0.
    rewrite H0. f_equal.
    extensionality sg. specialize (H1 sg).
    specialize (H (inr sg, sf)). simpl in H.
    rewrite EQ in H. destruct (s sg).
    + exfalso. apply (H u). auto.
    + rewrite H1. auto.
    + rewrite H0. auto.
Qed.  

Definition comp_embed X (x: F (G X)) :=
  comp_embed' (F.(SSPF.emb) _ (F.(PFunctor.map) (G.(SSPF.emb) X) x)).

Program Definition Comp : SSPF.t := 
  @SSPF.mk comp_Fn _ _ (PNatTrans.mk _ _ comp_embed _ _) _ _.
Next Obligation.
  extensionality s. destruct s; destruct s;
  unfold SPUF.map, comp_embed;
  repeat rewrite PNatTrans.map_nat; simpl;
  unfold comp_map, SPUF.map; rewrite PNatTrans.map_nat; simpl;  
  destruct ((SSPF.emb F) (G X) x); eauto.
  rewrite PNatTrans.map_nat. simpl.
  destruct ((SSPF.emb G) X f0); eauto.
Qed.
Next Obligation.
  unfold comp_pmap, comp_embed. rewrite PNatTrans.map_nat. simpl.
  unfold SPUF.map, SPUF.pmap, comp_embed'. split; intros.
  - apply (PNatTrans.pmap_nat F.(SSPF.emb)) in H. simpl in H. unfold SPUF.pmap in H.
    destruct s.
    destruct ((SSPF.emb F) (G X) x) eqn : EQF; inversion EQ;
    dependent destruction s; inversion EQ. 
    apply H in EQF. apply (PNatTrans.pmap_nat G.(SSPF.emb)) in EQF.
    simpl in EQF. unfold SPUF.pmap in EQF.
    destruct ((SSPF.emb G) X f) eqn : EQG; inversion EQ.
    apply EQF in EQG. subst. auto.
  - apply (PNatTrans.pmap_nat F.(SSPF.emb)). simpl. unfold SPUF.pmap. intros.
    apply (PNatTrans.pmap_nat G.(SSPF.emb)). simpl. unfold SPUF.pmap. intros.
    specialize (H (inr s0, s) x1). simpl in H.
    destruct ((SSPF.emb F) (G X) x); inversion EQ. subst.
    destruct ((SSPF.emb G) X x0); inversion EQ0. subst.
    apply H. auto.
Qed.
Next Obligation.
  apply comp_embed'_pullback in CONST.
  destruct CONST.
  apply SSPF.embedded_pullback in H. destruct H.
  apply (SSPF.preserve_pullback F (@SSPF.embedded_pullback _ _ _ _)) in H.
  destruct H. exists x1.
  subst. unfold comp_map.
  repeat f_equal. extensionality s. destruct s.
Qed.
Next Obligation.
  unfold comp_embed in EQ.
  apply comp_embed'_injective in EQ.
  apply SSPF.inj in EQ. apply SSPF.map_injective in EQ.
  apply EQ. apply SSPF.inj.
Qed.

End Composition_SSPF.

Section List_SSPF.

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
  @SSPF.mk (PFunctor.mk_data list List.map List.Forall) (list unit) unit 
          (PNatTrans.mk _ _ list_embed _ _) _ _.
Next Obligation.
  induction x; eauto.
  extensionality s. simpl. rewrite IHx.
  destruct s; eauto.
  destruct s; eauto.
Qed.
Next Obligation.
  unfold SPUF.pmap; induction x; split; intros.
  - inversion EQ.
  - constructor.
  - dependent destruction H.
    destruct IHx, s; inversion EQ.
    destruct s. inversion H4. subst. auto.
    apply (H1 H0 (cons u0 s) _ EQ).
  - constructor.
    apply (H (cons tt nil)). auto.
    apply IHx. intros.
    apply (H (cons tt s)). simpl.
    destruct s. destruct x; inversion EQ.
    apply EQ.
Qed.
Next Obligation.
  destruct m.
  - exists nil. eauto.
  - exfalso. eapply (CONST (cons () nil)); simpl; eauto.
Qed.
Next Obligation.
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
Qed.

End List_SSPF.

Section Dependent_function_SSPF.

Variable A: Type.
Variable B: A -> SSPF.t.

Definition depfun_map X Y (f: X -> Y) (x: forall a : A, B a X) :=
  fun (a: A) => (B a).(PFunctor.map) f (x a).

Definition depfun_pmap X (P: X -> Prop) x := forall a, (B a).(PFunctor.pmap) P (x a).

Definition depfun_Fn :=
  (PFunctor.mk_data (fun X => forall a: A, B a X) depfun_map depfun_pmap).

Definition depfun_embed X (x: forall a : A, B a X) (s: SSPF.dep_sum B (SSPF.Sh)) 
  : (X + (SSPF.dep_sum B (SSPF.Ext))) :=
  match s with
  | SSPF.dep _ _ a sh =>
    match (B a).(SSPF.emb) _ (x a) sh with
    | inl v => inl v
    | inr v => inr (SSPF.dep _ _ a v)
    end
  end.

Program Definition Depend_Fun : SSPF.t := 
  @SSPF.mk depfun_Fn _ _ (PNatTrans.mk _ _ depfun_embed _ _) _ _.
Next Obligation.
  extensionality s.
  unfold depfun_map. destruct s. unfold depfun_embed.
  rewrite PNatTrans.map_nat. simpl. unfold SPUF.map.
  destruct ((SSPF.emb (B a)) X (x a)); auto.
Qed.
Next Obligation.
  unfold depfun_pmap, depfun_embed, SPUF.pmap. split; intros; simpl.
  - destruct s.
    specialize (H a). apply (PNatTrans.pmap_nat (B a).(SSPF.emb)) in H.
    simpl in H. unfold SPUF.pmap in H.
    specialize (H c x0). apply H.
    destruct ((SSPF.emb (B a)) X (x a)); inversion EQ. auto.
  - apply (PNatTrans.pmap_nat (B a).(SSPF.emb)). simpl. unfold SPUF.pmap.
    intros.
    specialize (H (SSPF.dep _ _ _ s) x0). simpl in H. apply H.
    destruct ((SSPF.emb (B a)) X (x a)); inversion EQ. auto.
Qed.
Next Obligation.
  unfold depfun_embed, depfun_map in *.
  assert (forall a, exists x: (B a) False,
               m a = PFunctor.map (B a) (fun _ : False => ()) x).
  { intros.
    apply (B a).(SSPF.uni). intros.
    specialize (CONST (SSPF.dep _ _ _ s) x). simpl in CONST.
    destruct ((SSPF.emb (B a)) _ (m a)).
    destruct x, u; auto. intro. inversion H.
  }
  apply (non_dep_dep_functional_choice choice) in H.
  destruct H. exists x.
  extensionality s. apply H.
Qed.
Next Obligation.
  extensionality s. apply SSPF.inj.
  extensionality sh.
  unfold depfun_embed in EQ.
  apply equal_f with (SSPF.dep _ _ _ sh) in EQ.
  destruct ((SSPF.emb (B s)) X (m s)), ((SSPF.emb (B s)) X (n s));
  inversion EQ; auto.
  apply inj_pair2_eq_dec in H0. subst. auto.
  intros. destruct (excluded_middle_informative (x=y)); auto.
Qed.

End Dependent_function_SSPF.

Section Dependent_sum_SSPF.

Variable A: Type.
Variable B: A -> SSPF.t.

Inductive dep_sum X :=
| dep (a: A) (x': B a X) : dep_sum X.

Definition depsum_map X Y (f: X -> Y) (x: dep_sum X) :=
  match x with
  | dep _ a x' =>
    dep _ a ((B a).(PFunctor.map) f x') end.

Definition depsum_pmap X (P: X -> Prop) x :=
  match x with
  | dep _ a x' => (B a).(PFunctor.pmap) P x' end.

Definition depsum_Fn :=
  (PFunctor.mk_data dep_sum depsum_map depsum_pmap).

Definition depsum_embed X (x: dep_sum X)
           (s: SSPF.dep_sum B (fun x => sum unit x.(SSPF.Sh))):
  sum X (sum bool (SSPF.dep_sum B SSPF.Ext)) :=
  match x with
  | dep _ a x' =>
    match s with
    | SSPF.dep _ _ a' sh =>
      match (excluded_middle_informative (a = a')) with
      | left pf =>
        match sh with
        | inl _ => inr (inl true)
        | inr sh' =>
          match (B a').(SSPF.emb) _ (eq_rect _ (fun y => (B y) X) x' _ pf) sh' with
          | inl a => inl a
          | inr b => inr (inr (SSPF.dep _ _ a' b)) end
        end
      | right _ => inr (inl false)
      end
    end
  end.

Program Definition Depend_Sum : SSPF.t := 
  @SSPF.mk depsum_Fn _ _ (PNatTrans.mk _ _ depsum_embed _ _) _ _.
Next Obligation.
Proof.
  extensionality s. unfold depsum_embed, depsum_map, SPUF.map.
  destruct x; destruct s; destruct c;
  destruct (excluded_middle_informative (a = a0)); auto.
  destruct e. simpl.
  rewrite PNatTrans.map_nat. simpl. unfold SPUF.map.
  destruct ((SSPF.emb (B a)) X x'); auto.
Qed.
Next Obligation.
  unfold SPUF.pmap, depsum_pmap. split; intros.
  destruct s.
  - destruct c; unfold depsum_embed in EQ.
    + destruct x.
      destruct (excluded_middle_informative (a0 = a)); inversion EQ.
    + destruct x.
      apply (PNatTrans.pmap_nat (B a0).(SSPF.emb)) in H.
      simpl in H. unfold SPUF.pmap in H.
      destruct (excluded_middle_informative (a0 = a)); inversion EQ.      
      destruct e.
      apply H with (s := s).
      destruct ((SSPF.emb (B a0)) X x'); inversion EQ. auto.
  - destruct x.
    apply (PNatTrans.pmap_nat (B a).(SSPF.emb)). simpl. unfold SPUF.pmap.
    intros.
    unfold depsum_embed in H.
    specialize (H (SSPF.dep _ _ a (inr s)) x).
    simpl in H.
    destruct (excluded_middle_informative (a = a)).
    + apply H.
      assert ((eq_rect a (fun y : A => (B y) X) x' a e) = x').
      rewrite <- eq_rect_eq. auto.
      rewrite H0 in H. rewrite H0.
      destruct ((SSPF.emb (B a)) X x'); inversion EQ. auto.
    + exfalso. auto.
Qed.
Next Obligation.
  destruct m.
  unfold depsum_map, depsum_embed in *.
  assert (forall (s: SSPF.Sh (B a)) (x : unit), (SSPF.emb (B a)) _ x' s <> inl x).
  { intros.
    specialize (CONST (SSPF.dep _ _ a (inr s)) x). simpl in CONST.
    destruct (excluded_middle_informative (a = a)).
    - assert ((eq_rect a (fun y : A => (B y) unit) x' a e)=x').
      rewrite <- eq_rect_eq. auto.
      rewrite H in CONST.
      destruct ((SSPF.emb (B a)) _ x').
      destruct u, x. exfalso. auto.
      intro. inversion H0.
    - destruct n. auto.
  }
  apply SSPF.uni in H.
  destruct H.
  exists (dep _ a x). subst. auto.
Qed.
Next Obligation.
  destruct m, n.
  unfold depsum_embed in EQ.
  assert (H:= equal_f EQ (SSPF.dep _ _ a (inl tt))).
  simpl in H.
  destruct (excluded_middle_informative (a0 = a)). subst.
  - f_equal. apply SSPF.inj. extensionality s.
    apply equal_f with (x:= (SSPF.dep _ _ a (inr s))) in EQ.
    destruct (excluded_middle_informative (a = a)).
    assert (H1 : (eq_rect a (fun y : A => (B y) X) x' a e) = x').
    rewrite <- eq_rect_eq. auto.
    assert (H2 : (eq_rect a (fun y : A => (B y) X) x'0 a e) = x'0).
    rewrite <- eq_rect_eq. auto.
    rewrite H1 in EQ. rewrite H2 in EQ.
    destruct ((SSPF.emb (B a)) X x'), ((SSPF.emb (B a)) X x'0); inversion EQ; auto.
    apply inj_pair2_eq_dec in H3. subst. auto.
    intros. destruct (excluded_middle_informative (x=y)); auto.
    destruct n. auto.
  - destruct (excluded_middle_informative (a = a)); inversion H.
    destruct n0. auto.
Qed.

End Dependent_sum_SSPF.

Section Option_SSPF.

Definition option_pmap X (P: X -> Prop) (x: option X) :=
  match x with
  | Some x' => P x'
  | None => True
  end.

Definition option_Fn :=
  (PFunctor.mk_data option option_map option_pmap).

Definition option_embed X (x: option X) (s: unit) :=
  match x with
  | Some x' => inl x'
  | None => inr tt
  end.

Program Definition Option_sspf : SSPF.t :=
   @SSPF.mk option_Fn unit unit 
           (PNatTrans.mk _ _ option_embed _ _) _ _.
Next Obligation.
Proof.
  destruct x; auto.
Qed.
Next Obligation.
Proof.
  unfold option_pmap, option_embed, SPUF.pmap. split; intros.
  - destruct x; inversion EQ; subst; auto.
  - destruct x.
    + apply (H tt x). auto.
    + apply I.
Qed.    
Next Obligation.
  destruct m; simpl in CONST.
  - exfalso. apply (CONST tt u). auto.
  - exists None. auto.
Qed.
Next Obligation.
Proof.
  apply equal_f with tt in EQ.
  destruct m, n; inversion EQ; auto.
Qed.

End Option_SSPF.