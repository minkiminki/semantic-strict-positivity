Require Import paco.
Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.

Set Implicit Arguments.

Require Import Functor SPFunctor spec.

Module RCOINDUCTIVE : COINDUCTIVE.

Section FCoFix.
  Variable PF : Type -> Type.
  Context `{SPF : SPFunctor PF}.

  CoInductive ucofix: Type :=
  | Ucofix: UF (@Sh1 _ _ _ SPF) (@Sh2 _ _ _ SPF) ucofix -> ucofix
  .

  CoInductive c_range: forall (u:ucofix), Prop :=
  | c_Range
      (m: PF ucofix)
      (MEM: forall u, mem (emb _ m) u -> c_range u):
      c_range (Ucofix (emb _ m))
  .

  Definition fcofix := sig c_range.

  Definition fcofix_to_ucofix (x:fcofix): ucofix := proj1_sig x.

  Lemma Fcofix_range (x: PF fcofix) : c_range (Ucofix (emb _ (map fcofix_to_ucofix x))).
  Proof.
    constructor. intros.
    rewrite MAP_COMMUTE in H1. inv H1. simplify.
    destruct (emb _ x d) eqn: EQ; simplify; [|inv MEM].
    subst. destruct i. auto.
  Defined. 

  Definition Fcofix (x: PF fcofix) : fcofix :=
    @exist _ _ (Ucofix (NT _ (map fcofix_to_ucofix x))) (Fcofix_range x).

  Lemma fcofix_des0' u (R:c_range u): ex (unique (fun m => u = Ucofix (emb _ m))).
  Proof.
    inv R. exists m. split; auto.
    intros. inversion H1. apply INJECTIVE. auto. 
  Qed.

  Definition fcofix_des0 u (R:c_range u) : PF ucofix :=
    proj1_sig (constructive_definite_description _ (fcofix_des0' R)).

  Definition fcofix_des1 u (R:c_range u) x (MEM: mem (fcofix_des0 R) x): fcofix.
  Proof.
    exists x.
    destruct R. apply MEM0.
    unfold fcofix_des0 in MEM.
    destruct (constructive_definite_description
                 (fun m0 : PF ucofix => Ucofix (NT _ m) = Ucofix (NT _ m0))
                 (fcofix_des0' (c_Range m MEM0))) eqn : EQ.
    unfold proj1_sig in MEM.
    inversion e. apply INJECTIVE in H2. subst.
    apply MEM_COMMUTE in MEM. auto.
  Defined.

  Definition fcofix_des (f:fcofix): PF fcofix :=
    map_dep (fcofix_des0 (proj2_sig f)) (fcofix_des1 (proj2_sig f)).

  Lemma sig_unique : forall X (P: X -> Prop) (x1 x2: X) p1 p2,
    x1 = x2 -> exist P x1 p1 = exist P x2 p2.
  Proof.
    intros. subst.
    replace p1 with p2. auto.
    apply proof_irrelevance.
  Qed.

  Lemma Ucofix_inj u1 u2 (EQ: Ucofix u1 = Ucofix u2) : u1 = u2.
  Proof.
    inversion EQ. auto.
  Qed.

  Lemma Fcofix_inj x1 x2 (EQ: Fcofix x1 = Fcofix x2) : x1 = x2.
  Proof.
    unfold Fcofix in EQ.
    apply eq_sig_fst in EQ. apply Ucofix_inj in EQ.
    apply INJECTIVE.
    extensionality s. apply equal_f with s in EQ.
    repeat rewrite MAP_COMMUTE in EQ.
    simplify.
    destruct (emb _ x1 s);
    destruct (emb _ x2 s); inversion EQ; auto.
    destruct i, i0. simplify. subst.
    f_equal. f_equal. apply proof_irrelevance.
  Qed.

  Lemma c_des_correct1 x: Fcofix (fcofix_des x) = x.
  Proof.
    destruct x. destruct c. unfold Fcofix.
    apply sig_unique.
    f_equal. f_equal. unfold fcofix_des.
    rewrite MAP_DEP.
    - unfold fcofix_des0.
      destruct (constructive_definite_description
     (fun m0 : PF ucofix =>
      ` (exist c_range (Ucofix (NT _ m)) (c_Range m MEM)) = Ucofix (NT _ m0))
     (fcofix_des0' (proj2_sig (exist c_range (Ucofix (NT _ m)) (c_Range m MEM)))))
               eqn : EQ.
      unfold proj1_sig in *. inversion e.
      apply INJECTIVE in H2. auto.
    - auto.
  Qed.

  Lemma c_des_correct2 x: fcofix_des (Fcofix x) = x.
  Proof.
    apply Fcofix_inj.
    apply c_des_correct1.
  Qed.

  Inductive grd_ucofix (A : Type) : Type :=
  | _val : ucofix -> grd_ucofix A
  | _grd : UF (@Sh1 _ _ _ SPF) (@Sh2 _ _ _ SPF) (sum A (grd_ucofix A))
             -> grd_ucofix A.

  CoInductive grd_range (A: Type) : grd_ucofix A -> Prop :=
  | _val_r x : c_range x -> grd_range (_val A x)
  | _grd_r (m: PF (sum A (grd_ucofix A)))
             (MEM: forall a, mem (emb _ m) (inr a) -> grd_range a)
    : grd_range (_grd (emb _ m)).

  Definition grd_fcofix (A: Type) := sig (@grd_range A). 

  Definition val A (x: fcofix) : grd_fcofix A := exist _ _ (_val_r A (proj2_sig x)).

  Definition grd_fcofix_to_ucofix (A: Type) (x: sum A (grd_fcofix A))
    : sum A (grd_ucofix A) :=
    match x with
    | inl a => inl a
    | inr c => inr (proj1_sig c) end.

  Lemma grd_fcofix_range A (x: PF (sum A (grd_fcofix A))) :
                      grd_range (_grd (emb _ (map (@grd_fcofix_to_ucofix A) x))). 
  Proof.
    constructor. intros.
    rewrite MAP_COMMUTE in H1. inv H1. simplify.
    unfold grd_fcofix_to_ucofix in MEM.
    destruct (emb _ x d).
    - destruct i; inversion MEM.
      destruct g. auto.
    - inversion MEM.
  Defined.

  Definition grd A (x: PF (sum A (grd_fcofix A))) : grd_fcofix A :=
    exist _ _ (@grd_fcofix_range A x).

  Lemma grd_fcofix_des0' A u (R: grd_range (@_grd A u))
    : ex (unique (fun m => u = emb _ m)).
  Proof.
    inv R. exists m. split; auto.
    intros. apply INJECTIVE, H1.
  Defined.

  Definition grd_fcofix_des0 A u (R: grd_range (@_grd A u))
    : PF (sum A (grd_ucofix A)) :=
    proj1_sig (constructive_definite_description _ (grd_fcofix_des0' R)).

  Definition grd_fcofix_des1 A u (R: grd_range (@_grd A u)) x
             (MEM: mem (grd_fcofix_des0 R) x): sum A (grd_fcofix A).
  Proof.
    destruct x.
    - apply (inl a).
    - apply inr. exists g.
      inversion R. apply MEM0.
      unfold grd_fcofix_des0 in MEM.
      destruct (constructive_definite_description
                  (fun m : PF (A + grd_ucofix A)%type => u = (emb _ m))
                  (grd_fcofix_des0' R)) eqn : EQ.
      unfold proj1_sig in MEM.
      subst. apply INJECTIVE in H2. subst.
      apply MEM_COMMUTE in MEM. auto.
  Defined.

  Lemma grd_fcofix_des_v' A (u: ucofix) (g: grd_range (_val A u))
    : ex (unique (fun m: fcofix => u = proj1_sig m)).
  Proof.
    inv g.
    exists (exist _ _ H2).
    split; auto. intros.
    destruct x'.
    apply sig_unique. eauto.
  Qed.

  Definition grd_fcofix_des_v A (u: ucofix) (g: grd_range (_val A u)) : fcofix :=
    proj1_sig (constructive_definite_description _ (grd_fcofix_des_v' g)).

  Definition grd_fcofix_des A (f: grd_fcofix A)
    : sum fcofix (PF (sum A (grd_fcofix A))).
    destruct f.
    destruct x.
    - apply (inl (grd_fcofix_des_v g)).
    - apply inr.
      apply (map_dep (grd_fcofix_des0 g) (grd_fcofix_des1 g)).
  Defined.

  Definition val_des_correct A (x: fcofix) : grd_fcofix_des (val A x) = inl x.
  Proof.
    simpl. f_equal.
    destruct x. simpl. unfold grd_fcofix_des_v.
    destruct (constructive_definite_description (fun m : fcofix => x = ` m)
     (grd_fcofix_des_v' (_val_r A c))) eqn : EQ.
    destruct x0. inv e. simplify.
    apply sig_unique. auto.
  Qed.

  Definition grd_inj A x1 x2 (EQ: @grd A x1 = @grd A x2) : x1 = x2.
  Proof.
    unfold grd in EQ.
    apply eq_sig_fst in EQ. inversion EQ.
    apply INJECTIVE.
    extensionality s. apply equal_f with s in H2.
    repeat rewrite MAP_COMMUTE in H2.
    simplify.
    destruct (emb _ x1 s);
    destruct (emb _ x2 s); inversion H0; auto;
    try destruct i, i0; inversion H2; simplify; eauto.
    destruct g, g0. simplify. subst.
    repeat apply f_equal. apply proof_irrelevance.
  Qed.

  Lemma grd_des_correct' A x f (EQ: grd_fcofix_des f = inr x) : @grd A x = f.
  Proof.
    destruct f. inversion g.
    - destruct x0; [inversion EQ| inversion H2].
    - destruct x0; inv H1.
      unfold grd. apply sig_unique.
      f_equal. f_equal. simpl in *.
      inv EQ.
      rewrite MAP_DEP.
      + unfold grd_fcofix_des0.
        destruct (constructive_definite_description
                    (fun m0 : PF (A + grd_ucofix A)%type => (emb _ m) = (emb _ m0))
                    (grd_fcofix_des0' g)) eqn: EQ.
        simpl.
        apply INJECTIVE. auto.
      + intros.
        unfold grd_fcofix_to_ucofix.
        destruct x; simpl; auto.
  Qed.

  Definition grd_des_correct A (f: PF (sum A (grd_fcofix A)))
    : grd_fcofix_des (@grd A f) = inr f.
  Proof.
    assert (grd_fcofix_des (@grd A f) =
            inr (map_dep (grd_fcofix_des0 (@grd_fcofix_range A f))
                                  (grd_fcofix_des1 (@grd_fcofix_range A f)))); auto.
    apply grd_des_correct' in H1.
    apply grd_inj in H1.
    simpl. f_equal. auto.
  Qed.

  Lemma grd_fcofix_match A (x: grd_fcofix A) :
    (exists x', val A x' = x) \/ (exists m, @grd A m = x).
  Proof.
    destruct (grd_fcofix_des x) eqn: EQ.
    - destruct x. destruct x; inversion g; simpl in EQ; inversion EQ. subst.
      left. exists (exist _ _ H2).
      unfold val. simpl. apply sig_unique. auto.
    - apply grd_des_correct' in EQ. eauto.
  Qed.

  CoFixpoint to_ucofix A (f: A -> grd_ucofix A) : sum A (grd_ucofix A) -> ucofix :=
    fun s =>
      match s with
      | inl a =>
        match f a with
        | _val _ u => u
        | _grd u =>
          Ucofix
            (fun s1 : Sh1 =>
               match u s1 with
               | inl x => inl (to_ucofix f x)
               | inr e => inr e
               end)
        end
      | inr (_val _ u) => u
      | inr (_grd u) =>
        Ucofix
          (fun s1 : Sh1 =>
             match u s1 with
             | inl x => inl (to_ucofix f x)
             | inr e => inr e
             end)
      end.
  
  Lemma ucofix_adhoc (x: ucofix) : x = Ucofix (match x with Ucofix u => u end).
  Proof.
    destruct x. auto.
  Defined.

  Definition to_fcofix0 A (f: A -> grd_fcofix A) (s: sum A (grd_fcofix A))
    : ucofix :=
    match s with
    | inl a => to_ucofix (fun x => proj1_sig (f x)) (inl a)
    | inr m => to_ucofix (fun x => proj1_sig (f x)) (inr (proj1_sig m)) end.

  Lemma to_fcofix1 A (f: A -> grd_fcofix A) (s: sum A (grd_fcofix A))
    : c_range (to_fcofix0 f s).
  Proof.
    revert s. cofix.
    intros.
    destruct s; simpl.
    - rewrite ucofix_adhoc. simpl. destruct (f a). simpl.
      destruct g.
      + rewrite <- ucofix_adhoc. apply H1.
      + replace (fun s1 : @Sh1 PF H H0 SPF =>
        match
          @NT PF (UF (@Sh1 PF H H0 SPF) (@Sh2 PF H H0 SPF)) _ _
            (@emb PF H H0 SPF) (sum A (grd_ucofix A)) m s1
          return (Coprod Ident (Const (@Sh2 PF H H0 SPF)) ucofix)
        with
        | inl x =>
            @inl ucofix (Const (@Sh2 PF H H0 SPF) ucofix)
              (@to_ucofix A
                 (fun x0 : A => @proj1_sig (grd_ucofix A) (@grd_range A) (f x0)) x)
        | inr e =>
            @inr (Ident ucofix) (Const (@Sh2 PF H H0 SPF) (sum A (grd_ucofix A))) e
        end) with
            (map (fun x => to_ucofix (fun x0 : A => ` (f x0)) x) (@emb _ _ _ SPF _ m)); auto. 
        rewrite <- MAP_COMMUTE.
        constructor. intros. set H1. rewrite MAP_COMMUTE in m0.
        simpl in m0. inv m0. simplify.
        destruct (match emb _ m d with
           | inl fx => inl (to_ucofix (fun x0 : A => ` (f x0)) fx)
           | inr fx => inr fx
           end) eqn: EQ1;
        destruct (emb _ m d) eqn : EQ2; inversion MEM0;
          inversion EQ1; simplify.
        destruct i.
        * specialize (to_fcofix1 (inl a0)). simpl in to_fcofix1. 
          apply to_fcofix1.
        * assert (grd_range g).
          { apply MEM. apply (Function_mem _ _ d).
            rewrite EQ2. simplify. auto.
          }
          specialize (to_fcofix1 (inr (exist _ _ H3))).
          simpl in to_fcofix1. apply to_fcofix1.
    - rewrite ucofix_adhoc. simpl.
      destruct g. simpl. destruct x.
      + rewrite <- ucofix_adhoc. inversion g. subst. apply H2.
      + inversion g.
        replace (fun s1 : @Sh1 PF H H0 SPF =>
        match
          @NT PF (UF (@Sh1 PF H H0 SPF) (@Sh2 PF H H0 SPF)) _ _ 
            (@emb PF H H0 SPF) (sum A (grd_ucofix A)) m s1
          return (Coprod Ident (Const (@Sh2 PF H H0 SPF)) ucofix)
        with
        | inl x =>
            @inl ucofix (Const (@Sh2 PF H H0 SPF) ucofix)
              (@to_ucofix A
                 (fun x0 : A => @proj1_sig (grd_ucofix A) (@grd_range A) (f x0)) x)
        | inr e =>
            @inr (Ident ucofix) (Const (@Sh2 PF H H0 SPF) (sum A (grd_ucofix A))) e
        end) with
            (map (fun x => to_ucofix (fun x0 : A => ` (f x0)) x) (emb _ m)); auto.
        rewrite <- MAP_COMMUTE.
        constructor. intros.
        set H1. rewrite MAP_COMMUTE in m0.
        simpl in m0. inv m0. simplify.
        destruct (match emb _ m d with
           | inl fx => inl (to_ucofix (fun x0 : A => ` (f x0)) fx)
           | inr fx => inr fx
           end) eqn: EQ1;
        destruct (emb _ m d) eqn : EQ2; inversion EQ1; simplify; inv MEM0.
        destruct i.
        * specialize (to_fcofix1 (inl a)). simpl in to_fcofix1. apply to_fcofix1.
        * assert (grd_range g0).
          { apply MEM.
            econstructor. simplify.
            rewrite EQ2. simplify. auto.
          }
          specialize (to_fcofix1 (inr (exist _ _ H3))).
          simpl in to_fcofix1. apply to_fcofix1.
  Defined.

  Definition to_fcofix A (f: A -> grd_fcofix A) (s: sum A (grd_fcofix A)) : fcofix :=
    exist _ (to_fcofix0 f s) (to_fcofix1 f s).

  Definition fcorec A (f : A -> grd_fcofix A) (a: A) : fcofix := to_fcofix f (inl a).

  Lemma fcorec_red A (f: A -> grd_fcofix A) (a: A) :
    fcofix_des (fcorec f a) =
    match (grd_fcofix_des (f a)) with
    | inl x => fcofix_des x
    | inr m => map (to_fcofix f) m end.
  Proof.
    assert (H1:= grd_fcofix_match (f a)). destruct H1; destruct H1.
    - rewrite <- H1. rewrite val_des_correct.
      f_equal.
      unfold fcorec, to_fcofix.
      unfold to_fcofix0. destruct x. apply sig_unique.
      unfold val in H. simpl in H.
      rewrite (ucofix_adhoc (to_ucofix (fun x0 : A => ` (f x0)) (inl a))). simpl.
      rewrite <- H1. simpl.
      rewrite <- ucofix_adhoc. auto.
    - rewrite <- H1. rewrite grd_des_correct.
      unfold fcorec. unfold to_fcofix at 1.
      apply (map_injective fcofix_to_ucofix).
      { intros. destruct x1, x2. simpl in EQ. inversion EQ. apply sig_unique. auto. }
      unfold fcofix_des.
      rewrite MAP_DEP; auto. simpl. 
      unfold fcofix_des0. simpl.
      destruct (constructive_definite_description
     (fun m : PF ucofix =>
      to_ucofix (fun x0 : A => ` (f x0)) (inl a) = Ucofix (emb _ m))
     (fcofix_des0' (to_fcofix1 f (inl a)))) eqn : EQ. simpl in *.
      rewrite EQ. simpl. clear EQ.
      set e.
      rewrite (ucofix_adhoc (to_ucofix (fun x0 : A => ` (f x0)) (inl a))) in e0.
      simpl in e0. rewrite <- H1 in e0.
      unfold grd in e0. simpl in e0. inversion e0. clear e0.
      rewrite MAP_COMPOSE.
      apply INJECTIVE.
      rewrite <- H3.
      repeat rewrite MAP_COMMUTE.
      extensionality s.
      simplify.
      destruct (emb _ x s) eqn : EQ; auto.
      f_equal.
      unfold to_fcofix0, grd_fcofix_to_ucofix.
      destruct i; auto.
   Qed.
        
  Lemma to_fcofix_correct1 A (f: A -> grd_fcofix A) a :
    to_fcofix f (inl a) = fcorec f a.
  Proof.
    unfold fcorec. auto.
  Qed.

  Lemma to_fcofix_correct2 A (f: A -> grd_fcofix A) x :
    to_fcofix f (inr (val A x)) = x.
  Proof.
    unfold to_fcofix. destruct x. apply sig_unique. simpl.
    rewrite (ucofix_adhoc (to_ucofix (fun x0 : A => ` (f x0)) (inr (_val A x)))).
    simpl. rewrite <- ucofix_adhoc. auto.
  Qed.

  Lemma to_fcofix_correct3 A (f: A -> grd_fcofix A) m :
    to_fcofix f (inr (@grd A m)) = Fcofix (map (to_fcofix f) m).
  Proof.
    unfold to_fcofix, to_fcofix0, Fcofix. apply sig_unique.
    rewrite (ucofix_adhoc (to_ucofix (fun x : A => ` (f x)) (inr (` (@grd A m))))).
    f_equal.
    rewrite Functor.MAP_COMPOSE.
    rewrite MAP_COMMUTE. simpl.
    simplify. extensionality s.
    rewrite MAP_COMMUTE. simplify.
    unfold grd_fcofix_to_ucofix.
    destruct (emb _ m s); auto.
    destruct i; auto.
  Qed.

  Lemma bsm_gen_mon : monotone2 (bsm_gen Fcofix).
  Proof.
    unfold monotone2. intros. inv IN. constructor.
    unfold rel2 in r.
    apply (rel_monotone _ _ _ _ LE R).
  Qed.
  Hint Resolve bsm_gen_mon : paco.

  Inductive u_bsm_gen u_bsm : ucofix -> ucofix -> Prop :=
  | _u_bsm_gen : forall u1 u2 (R: rel u_bsm u1 u2),
      u_bsm_gen u_bsm (Ucofix u1) (Ucofix u2).
  Hint Constructors u_bsm_gen.

  Definition u_bsm u1 u2 := paco2 u_bsm_gen bot2 u1 u2.
  Hint Unfold u_bsm.
  Lemma u_bsm_gen_mon : monotone2 u_bsm_gen.
  Proof.
    unfold monotone2. intros. inv IN. constructor.
    apply (UF_rel_monotone _ LE R).
  Qed.
  Hint Resolve u_bsm_gen_mon : paco.

  Lemma eq_u_bsm : forall u1 u2, u1 = u2 -> u_bsm u1 u2.
  Proof.
    pcofix CIH.
    intros. subst. pfold.
    destruct u2. constructor. simplify.
    intro d. destruct (u d);
    constructor; simplify; auto.
  Qed.

  Definition bsm x1 x2 := paco2 (bsm_gen Fcofix) bot2 x1 x2.

  Axiom u_bsm_eq : forall u1 u2, u_bsm u1 u2 -> u1 = u2.

  Lemma bsm_u_bsm x1 x2 (BSM: bsm x1 x2)
    : u_bsm (fcofix_to_ucofix x1) (fcofix_to_ucofix x2).
  Proof.
    revert x1 x2 BSM. pcofix CIH.
    intros. pfold.
    destruct x1, x2. destruct x, x0.
    constructor. simplify.

    punfold BSM. inv BSM.
    inv c. inv c0. apply REL_COMMUTE in R.
    rewrite MAP_COMMUTE in H2.
    rewrite MAP_COMMUTE in H3.

    rewrite H2. rewrite H3. rewrite H2 in MEM. rewrite H3 in MEM0. clear H2 H3 m m0.

    intro. specialize (R d). simplify.

    destruct (emb _ x1 d);
    destruct (emb _ x2 d); inv R.
    - simplify. constructor. destruct REL; [| inversion H1].
      simplify. right. apply CIH, H1.
    - simplify. subst. constructor. simplify. auto.
  Qed.

  Lemma u_bsm_bsm x1 x2 (BSM: u_bsm (fcofix_to_ucofix x1) (fcofix_to_ucofix x2))
    : bsm x1 x2.
  Proof.
    revert x1 x2 BSM. pcofix CIH.
    intros. pfold.
    rewrite <- (c_des_correct1 x1). rewrite <- (c_des_correct1 x2).
    constructor.

    apply REL_COMMUTE. simplify. intro.

    assert (H1 : forall x y, map fcofix_to_ucofix (emb _ (fcofix_des (exist c_range (Ucofix (emb _ x)) y))) = (emb _ x)).
    { intros.
      rewrite <- MAP_COMMUTE.
      unfold fcofix_des. rewrite MAP_DEP.
      unfold fcofix_des0. simpl.
      destruct (constructive_definite_description
                  (fun m1 : PF ucofix => Ucofix (emb _ x) = Ucofix (emb _ m1))
                  (fcofix_des0' y)) eqn : EQ.
      inversion e. apply INJECTIVE in H2. subst. eauto.
      intros. auto.
    }
    
    punfold BSM. inv BSM. simplify. specialize (R d). inv R.


    - simplify. destruct REL; [|inversion H2].
      destruct x1. destruct x2. simplify. subst.
      inversion c. inversion c0. subst.

      assert (c_range fx1).
      { apply MEM. apply (Function_mem _ _ d). simplify.
        rewrite <- H5. simplify. auto. }
      assert (c_range fx2).
      { apply MEM0. apply (Function_mem _ _ d). simplify.
        rewrite <- H6. simplify. auto. }
      replace (emb _ (fcofix_des (exist c_range (Ucofix (emb _ m)) c)) d) with (@inl _ Sh2 (exist _ _ H3)).
      replace (emb _ (fcofix_des (exist c_range (Ucofix (emb _ m0)) c0)) d) with (@inl _ Sh2 (exist _ _ H4)).
      constructor. simplify.
      right. apply CIH. apply H2.

      specialize (H1 m0 c0). apply equal_f with d in H1. rewrite <- H6 in H1.
      simplify.
      destruct (emb _ (fcofix_des (exist c_range (Ucofix (emb _ m0)) c0)) d);
      inversion H1. subst. destruct i. simpl. f_equal. apply sig_unique. auto.

      specialize (H1 m c). apply equal_f with d in H1. rewrite <- H5 in H1.
      simplify.
      destruct (emb _ (fcofix_des (exist c_range (Ucofix (emb _ m)) c)) d);
      inversion H1. subst. destruct i. simpl. f_equal. apply sig_unique. auto.
      
    - simplify. subst.

      
      destruct x1, x2. inversion c. inversion c0. simplify. subst.
      inv H2. inv H7.

      set (H1 m c). apply equal_f with d in e. rewrite <- H5 in e.
      set (H1 m0 c0). apply equal_f with d in e0. rewrite <- H6 in e0. simplify.
      destruct (emb _ (fcofix_des (exist c_range (Ucofix (emb _ m)) c)) d);
      destruct (emb _ (fcofix_des (exist c_range (Ucofix (emb _ m0)) c0)) d);
      simplify; inversion e; inversion e0.
      constructor. constructor. 
  Qed.

  Lemma bsm_eq x1 x2 : bsm x1 x2 <-> x1 = x2.
  Proof.
    split; intros.
    - apply bsm_u_bsm in H1. apply u_bsm_eq in H1.
      destruct x1, x2. apply sig_unique. auto.
    - apply u_bsm_bsm. apply eq_u_bsm.
      subst. auto.
  Qed.

  Definition fcorec_p A (f: A -> PF A) : A -> fcofix :=
    fcorec (fun a: A => @grd A (map inl (f a))).

  Lemma fcorec_p_red A (f: A -> PF A) a :
    fcofix_des (fcorec_p f a) = map (fcorec_p f) (f a).
  Proof.
    unfold fcorec_p. rewrite fcorec_red. rewrite grd_des_correct.
    simplify. apply Functor.MAP_COMPOSE. 
  Qed.

  Global Opaque Fcofix fcofix_des val grd grd_fcofix_des to_fcofix fcorec fcorec_p fcorec_red fcorec_p_red.

End FCoFix.

End RCOINDUCTIVE.

Section coinductive.

  Variable PF : Type -> Type.
  Context `{SPF : SPFunctor PF}.

  Definition fcofix : Type := @RCOINDUCTIVE.fcofix _ _ _ _. (* coinductive type *)

  Definition Fcofix : PF fcofix -> fcofix := @RCOINDUCTIVE.Fcofix _ _ _ _. (* constructor *)

  Definition fcofix_des : fcofix ->  PF fcofix := @RCOINDUCTIVE.fcofix_des _ _ _ _. (* destructor *)

  Definition Fcofix_inj : forall x1 x2 (EQ: Fcofix x1 = Fcofix x2), x1 = x2 := @RCOINDUCTIVE.Fcofix_inj _ _ _ _.
  (* constructors are injective *)

  Definition c_des_correct1 : forall x, Fcofix (fcofix_des x) = x := @RCOINDUCTIVE.c_des_correct1 _ _ _ _.

  Definition c_des_correct2 : forall x, fcofix_des (Fcofix x) = x := @RCOINDUCTIVE.c_des_correct2 _ _ _ _.
  (* these say that destructors are the inverse of constructors *)


(* for corecursive functions *)
(* we use mendler style corecursion *)

  Definition grd_fcofix : Type -> Type := @RCOINDUCTIVE.grd_fcofix _ _ _ _.

  Definition val : forall (A : Type), fcofix -> grd_fcofix A := @RCOINDUCTIVE.val _ _ _ _.

  Definition grd : forall (A : Type), PF (sum A (grd_fcofix A)) -> grd_fcofix A := @RCOINDUCTIVE.grd _ _ _ _.
  (* constructors for grd_fcofix *)

  Definition grd_fcofix_des : forall (A: Type),
      grd_fcofix A -> fcofix + (PF (sum A (grd_fcofix A))) := @RCOINDUCTIVE.grd_fcofix_des _ _ _ _.
  (* destructors for grd_fcofix *)

  Definition val_des_correct : forall A (x: fcofix),
      grd_fcofix_des (val A x) = inl x := @RCOINDUCTIVE.val_des_correct _ _ _ _.

  Definition grd_des_correct : forall A (f: PF (sum A (grd_fcofix A))),
      grd_fcofix_des (@grd A f) = inr f := @RCOINDUCTIVE.grd_des_correct _ _ _ _.
  (* destructros are the inverse of constructors *)

  Definition to_fcofix : forall A, (A -> grd_fcofix A) ->
                                 (sum A (grd_fcofix A)) -> fcofix := @RCOINDUCTIVE.to_fcofix _ _ _ _.
  (* users don't need to know this function *)

  Definition fcorec : forall A, (A -> grd_fcofix A) -> (A -> fcofix) := @RCOINDUCTIVE.fcorec _ _ _ _.
  (* corecursive function!!! *)

  Definition fcorec_p : forall A (f: A -> PF A), A -> fcofix := @RCOINDUCTIVE.fcorec_p _ _ _ _.
  (* primitive corecursion *)


(* reduction rules for corecursive functions *)

  Definition fcorec_red : forall A (f: A -> grd_fcofix A) (a: A),
      fcofix_des (fcorec f a) = match (grd_fcofix_des (f a)) with
                                | inl x => fcofix_des x
                                | inr m => map (to_fcofix f) m end := @RCOINDUCTIVE.fcorec_red _ _ _ _.
        
  Definition to_fcofix_correct1 : forall A (f: A -> grd_fcofix A) a,
    to_fcofix f (inl a) = fcorec f a := @RCOINDUCTIVE.to_fcofix_correct1 _ _ _ _.

  Definition to_fcofix_correct2 : forall A (f: A -> grd_fcofix A) x,
    to_fcofix f (inr (val A x)) = x := @RCOINDUCTIVE.to_fcofix_correct2 _ _ _ _.

  Definition to_fcofix_correct3 : forall A (f: A -> grd_fcofix A) m,
    to_fcofix f (inr (@grd A m)) = Fcofix (map (to_fcofix f) m) := @RCOINDUCTIVE.to_fcofix_correct3 _ _ _ _.

  Definition fcorec_p_red : forall A (f: A -> PF A) a,
    fcofix_des (fcorec_p f a) = map (fcorec_p f) (f a) := @RCOINDUCTIVE.fcorec_p_red _ _ _ _.

(* bisimilarity *)

  Definition bsm_gen_mon : monotone2 (bsm_gen Fcofix) := @RCOINDUCTIVE.bsm_gen_mon _ _ _ _.

  Definition bsm (x1 x2 : fcofix) : Prop := paco2 (bsm_gen Fcofix) bot2 x1 x2.

  Definition bsm_eq : forall x1 x2, bsm x1 x2 <-> x1 = x2  := @RCOINDUCTIVE.bsm_eq _ _ _ _.
  (* bisimilarity axiom.
     its proof relies on the bisimilarity axiom of universal functors *)

(* tactics for reduction *)

End coinductive.


Global Opaque fcofix Fcofix fcofix_des Fcofix_inj c_des_correct1 c_des_correct2 grd_fcofix val grd grd_fcofix_des val_des_correct grd_des_correct to_fcofix fcorec fcorec_p fcorec_red fcorec_p_red to_fcofix_correct1 to_fcofix_correct2 to_fcofix_correct3 bsm_gen_mon bsm_eq.


Ltac csimpl := repeat (autounfold;
                       repeat rewrite c_des_correct2;
                       repeat rewrite val_des_correct;
                       repeat rewrite grd_des_correct;
                       repeat rewrite fcorec_red;
                       repeat rewrite fcorec_p_red;
                       repeat rewrite to_fcofix_correct1;
                       repeat rewrite to_fcofix_correct2;
                       repeat rewrite to_fcofix_correct3;
                       unfold id;
                       simpl).

Ltac csimpl_in H := repeat (autounfold in H;
                            repeat rewrite c_des_correct2 in H;
                            repeat rewrite val_des_correct in H;
                            repeat rewrite grd_des_correct in H;
                            repeat rewrite fcorec_red in H;
                            repeat rewrite fcorec_p_red in H;
                            repeat rewrite to_fcofix_correct1 in H;
                            repeat rewrite to_fcofix_correct2 in H;
                            repeat rewrite to_fcofix_correct3 in H;
                            unfold id in H;
                            simpl in H).

Arguments fcofix PF {H} {H0} {SPF}.
Arguments Fcofix PF {H} {H0} {SPF}.
Arguments fcofix_des {PF} {H} {H0} {SPF}.