Require Import paco.
Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor.


Section FCoFix.
  Variable PF: SPFunctorType.

  CoInductive ucofix: Type :=
  | Ucofix: UF PF.(SPFunctor.Sh1) PF.(SPFunctor.Sh2) ucofix -> ucofix
  .

  CoInductive c_range: forall (u:ucofix), Prop :=
  | c_Range
      (m: PF ucofix)
      (MEM: forall u, fmem (femb m) u -> c_range u):
      c_range (Ucofix (femb m))
  .

  Definition fcofix := sig c_range.

  Definition fcofix_to_ucofix (x:fcofix): ucofix := proj1_sig x.

  Lemma Fcofix_range (x: PF fcofix) : c_range (Ucofix (femb (fmap fcofix_to_ucofix x))).
  Proof.
    constructor. intros.
    rewrite SPFunctorFacts.NATURAL_MAP in H. inv H. simplify.
    destruct (SPFunctor.embedding PF fcofix x) eqn: EQ; [|inv MEM].
    subst. destruct f. auto.
  Defined. 

  Definition Fcofix (x: PF fcofix) : fcofix :=
    @exist _ _ (Ucofix (femb (fmap fcofix_to_ucofix x))) (Fcofix_range x).

  Lemma fcofix_des0' u (R:c_range u): ex (unique (fun m => u = Ucofix (femb m))).
  Proof.
    inv R. exists m. split; auto.
    intros. inversion H. apply (SPFunctorFacts.INJECTIVE _ _ _ H1).
  Qed.

  Definition fcofix_des0 u (R:c_range u) : PF ucofix :=
    proj1_sig (constructive_definite_description _ (fcofix_des0' R)).

  Definition fcofix_des1 u (R:c_range u) x (MEM: fmem (fcofix_des0 R) x): fcofix.
  Proof.
    exists x.
    destruct R. apply MEM0.
    unfold fcofix_des0 in MEM.
    destruct (constructive_definite_description
                 (fun m0 : PF ucofix => Ucofix femb (m) = Ucofix femb (m0))
                 (fcofix_des0' (c_Range m MEM0))) eqn : EQ.
    unfold proj1_sig in MEM.
    inversion e. apply SPFunctorFacts.INJECTIVE in H0. subst.
    apply SPFunctorFacts.NATURAL_MEM in MEM. auto.
  Defined.

  Definition fcofix_des (f:fcofix): PF fcofix :=
    fmap_dep (fcofix_des0 (proj2_sig f)) (fcofix_des1 (proj2_sig f)).

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
    apply SPFunctorFacts.INJECTIVE.
    extensionality s. apply equal_f with s in EQ.
    repeat rewrite SPFunctorFacts.NATURAL_MAP in EQ.
    simplify.
    destruct (SPFunctor.embedding PF fcofix x1 s);
    destruct (SPFunctor.embedding PF fcofix x2 s); inversion EQ; auto.
    destruct f, f0. simpl in H0. subst.
    f_equal. f_equal. apply proof_irrelevance.
  Qed.

  Lemma c_des_correct1 x: Fcofix (fcofix_des x) = x.
  Proof.
    destruct x. destruct c. unfold Fcofix.
    apply sig_unique.
    f_equal. f_equal. unfold fcofix_des.
    rewrite SFunctor.MAP_DEP.
    - unfold fcofix_des0.
      destruct (constructive_definite_description
     (fun m0 : PF ucofix =>
      ` (exist c_range (Ucofix femb (m)) (c_Range m MEM)) = Ucofix femb (m0))
     (fcofix_des0' (proj2_sig (exist c_range (Ucofix femb (m)) (c_Range m MEM)))))
               eqn : EQ.
      unfold proj1_sig in *. inversion e.
      apply SPFunctorFacts.INJECTIVE in H0. auto.
    - auto.
  Qed.

  Lemma c_des_correct2 x: fcofix_des (Fcofix x) = x.
  Proof.
    apply Fcofix_inj.
    apply c_des_correct1.
  Qed.

  Inductive grd_ucofix (A : Type) : Type :=
  | _val : ucofix -> grd_ucofix A
  | _grd : UF PF.(SPFunctor.Sh1) PF.(SPFunctor.Sh2) (sum A (grd_ucofix A))
             -> grd_ucofix A.

  CoInductive grd_range (A: Type) : grd_ucofix A -> Prop :=
  | _val_r x : c_range x -> grd_range (_val A x)
  | _grd_r (m: PF (sum A (grd_ucofix A)))
             (MEM: forall a, fmem (femb m) (inr a) -> grd_range a)
    : grd_range (_grd (femb m)).

  Definition grd_fcofix (A: Type) := sig (@grd_range A). 

  Definition val A (x: fcofix) : grd_fcofix A := exist _ _ (_val_r A (proj2_sig x)).

  Definition grd_fcofix_to_ucofix (A: Type) (x: sum A (grd_fcofix A))
    : sum A (grd_ucofix A) :=
    match x with
    | inl a => inl a
    | inr c => inr (proj1_sig c) end.

  Lemma grd_fcofix_range A (x: PF (sum A (grd_fcofix A))) :
                      grd_range (_grd (femb (fmap (@grd_fcofix_to_ucofix A) x))). 
  Proof.
    constructor. intros.
    rewrite SPFunctorFacts.NATURAL_MAP in H. inv H. simplify.
    unfold grd_fcofix_to_ucofix in MEM.
    destruct (SPFunctor.embedding PF (A + grd_fcofix A) x d).
    - destruct s; inversion MEM.
      destruct g. auto.
    - inversion MEM.
  Defined.

  Definition grd A (x: PF (sum A (grd_fcofix A))) : grd_fcofix A :=
    exist _ _ (grd_fcofix_range A x).

  Lemma grd_fcofix_des0' A u (R: grd_range (@_grd A u))
    : ex (unique (fun m => u = femb m)).
  Proof.
    inv R. exists m. split; auto.
    intros. apply SPFunctorFacts.INJECTIVE, H.
  Defined.

  Definition grd_fcofix_des0 A u (R: grd_range (@_grd A u))
    : PF (sum A (grd_ucofix A)) :=
    proj1_sig (constructive_definite_description _ (grd_fcofix_des0' R)).

  Definition grd_fcofix_des1 A u (R: grd_range (@_grd A u)) x
             (MEM: fmem (grd_fcofix_des0 R) x): sum A (grd_fcofix A).
  Proof.
    destruct x.
    - apply (inl a).
    - apply inr. exists g.
      inversion R. apply MEM0.
      unfold grd_fcofix_des0 in MEM.
      destruct (constructive_definite_description
                  (fun m : PF (A + grd_ucofix A)%type => u = femb (m))
                  (grd_fcofix_des0' R)) eqn : EQ.
      unfold proj1_sig in MEM.
      subst. apply SPFunctorFacts.INJECTIVE in H0. subst.
      apply SPFunctorFacts.NATURAL_MEM in MEM. auto.
  Defined.

  Lemma grd_fcofix_des_v' A (u: ucofix) (g: grd_range (_val A u))
    : ex (unique (fun m: fcofix => u = proj1_sig m)).
  Proof.
    inv g.
    exists (exist _ _ H0).
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
      apply (fmap_dep (grd_fcofix_des0 g) (grd_fcofix_des1 g)).
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

  Definition grd_inj A x1 x2 (EQ: grd A x1 = grd A x2) : x1 = x2.
  Proof.
    unfold grd in EQ.
    apply eq_sig_fst in EQ. inversion EQ.
    apply SPFunctorFacts.INJECTIVE.
    extensionality s. apply equal_f with s in H0.
    repeat rewrite SPFunctorFacts.NATURAL_MAP in H0.
    simplify.
    destruct (SPFunctor.embedding PF (A + grd_fcofix A) x1 s);
    destruct (SPFunctor.embedding PF (A + grd_fcofix A) x2 s); inversion H0; auto.
    destruct s0, s1; inversion H1; eauto.
    destruct g, g0. simpl in *. subst.
    repeat apply f_equal. apply proof_irrelevance.
  Qed.

  Lemma grd_des_correct' A x f (EQ: grd_fcofix_des f = inr x) : grd A x = f.
  Proof.
    destruct f. inversion g.
    - destruct x0; [inversion EQ| inversion H0].
    - destruct x0; inv H.
      unfold grd. apply sig_unique.
      f_equal. f_equal. simpl in *.
      inv EQ.
      rewrite SFunctor.MAP_DEP.
      + unfold grd_fcofix_des0.
        destruct (constructive_definite_description
                    (fun m0 : PF (A + grd_ucofix A)%type => femb (m) = femb (m0))
                    (grd_fcofix_des0' g)) eqn: EQ.
        simpl.
        apply SPFunctorFacts.INJECTIVE. auto.
      + intros.
        unfold grd_fcofix_to_ucofix.
        destruct x; simpl; auto.
  Qed.

  Definition grd_des_correct A (f: PF (sum A (grd_fcofix A)))
    : grd_fcofix_des (grd A f) = inr f.
  Proof.
    assert (grd_fcofix_des (grd A f) =
            inr (SFunctor.map_dep PF (grd_fcofix_des0 (grd_fcofix_range A f))
                                  (grd_fcofix_des1 (grd_fcofix_range A f)))); auto.
    apply grd_des_correct' in H.
    apply grd_inj in H.
    simpl. f_equal. auto.
  Qed.

  Lemma grd_fcofix_match A (x: grd_fcofix A) :
    (exists x', val A x' = x) \/ (exists m, grd A m = x).
  Proof.
    destruct (grd_fcofix_des x) eqn: EQ.
    - destruct x. destruct x; inversion g; simpl in EQ; inversion EQ. subst.
      left. exists (exist _ _ H0).
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
            (fun s1 : SPFunctor.Sh1 PF =>
               match u s1 with
               | inl x => inl (to_ucofix f x)
               | inr e => inr e
               end)
        end
      | inr (_val _ u) => u
      | inr (_grd u) =>
        Ucofix
          (fun s1 : SPFunctor.Sh1 PF =>
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
      + rewrite <- ucofix_adhoc. apply H.
      + replace (fun s1 : SPFunctor.Sh1 PF =>
                   match femb (m) s1 with
                   | inl x => inl (to_ucofix (fun x0 : A => ` (f x0)) x)
                   | inr e => inr e
                   end) with
            (fmap (fun x => to_ucofix (fun x0 : A => ` (f x0)) x) (femb m)); auto.
        rewrite <- SPFunctorFacts.NATURAL_MAP.
        constructor. intros. set H. rewrite SPFunctorFacts.NATURAL_MAP in m0.
        simpl in m0. inv m0. simplify.
        destruct (match SPFunctor.embedding PF (A + grd_ucofix A) m d with
           | inl fx => inl (to_ucofix (fun x0 : A => ` (f x0)) fx)
           | inr fx => inr fx
           end) eqn: EQ1; destruct MEM0.
        destruct (SPFunctor.embedding PF _ m d) eqn : EQ2; inversion EQ1.
        
        destruct s.
        * specialize (to_fcofix1 (inl a0)). simpl in to_fcofix1. apply to_fcofix1.
        * assert (grd_range g).
          { apply MEM.
            econstructor. simplify.
            rewrite EQ2. auto.
          }
          specialize (to_fcofix1 (inr (exist _ _ H0))).
          simpl in to_fcofix1. apply to_fcofix1.
    - rewrite ucofix_adhoc. simpl.
      destruct g. simpl. destruct x.
      + rewrite <- ucofix_adhoc. inversion g. subst. apply H0.
      + inversion g.
        replace (fun s1 : SPFunctor.Sh1 PF =>
        match femb (m) s1 with
        | inl x => inl (to_ucofix (fun x0 : A => ` (f x0)) x)
        | inr e => inr e
        end) with
            (fmap (fun x => to_ucofix (fun x0 : A => ` (f x0)) x) (femb m)); auto.
        rewrite <- SPFunctorFacts.NATURAL_MAP.
        constructor. intros.
        set H. rewrite SPFunctorFacts.NATURAL_MAP in m0.
        simpl in m0. inv m0. simplify.
        destruct (match SPFunctor.embedding PF (A + grd_ucofix A) m d with
           | inl fx => inl (to_ucofix (fun x0 : A => ` (f x0)) fx)
           | inr fx => inr fx
           end) eqn: EQ1; destruct MEM0.
        destruct (SPFunctor.embedding PF _ m d) eqn : EQ2; inversion EQ1.
        
        destruct s.
        * specialize (to_fcofix1 (inl a)). simpl in to_fcofix1. apply to_fcofix1.
        * assert (grd_range g0).
          { apply MEM.
            econstructor. simplify.
            rewrite EQ2. auto.
          }
          specialize (to_fcofix1 (inr (exist _ _ H0))).
          simpl in to_fcofix1. apply to_fcofix1.
  Defined.

  Definition to_fcofix A (f: A -> grd_fcofix A) (s: sum A (grd_fcofix A)) : fcofix :=
    exist _ (to_fcofix0 f s) (to_fcofix1 f s).

  Definition fcorec A (f : A -> grd_fcofix A) (a: A) : fcofix := to_fcofix f (inl a).

  Lemma fcorec_red A (f: A -> grd_fcofix A) (a: A) :
    fcofix_des (fcorec f a) =
    match (grd_fcofix_des (f a)) with
    | inl x => fcofix_des x
    | inr m => fmap (to_fcofix f) m end.
  Proof.
    assert (H:= grd_fcofix_match (f a)). destruct H; destruct H.
    - rewrite <- H. rewrite val_des_correct.
      f_equal.
      unfold fcorec, to_fcofix.
      unfold to_fcofix0. destruct x. apply sig_unique.
      unfold val in H. simpl in H.
      rewrite (ucofix_adhoc (to_ucofix (fun x0 : A => ` (f x0)) (inl a))). simpl.
      rewrite <- H. simpl.
      rewrite <- ucofix_adhoc. auto.
    - rewrite <- H. rewrite grd_des_correct.
      unfold fcorec. unfold to_fcofix at 1.
      apply SPFunctorFacts.map_injective with (f := fcofix_to_ucofix) .
      { intros. destruct x1, x2. simpl in EQ. inversion EQ. apply sig_unique. auto. }
      unfold fcofix_des.
      rewrite SFunctor.MAP_DEP; auto. simpl. 
      unfold fcofix_des0. simpl.
      destruct (constructive_definite_description
     (fun m : PF ucofix =>
      to_ucofix (fun x0 : A => ` (f x0)) (inl a) = Ucofix femb (m))
     (fcofix_des0' (to_fcofix1 f (inl a)))) eqn : EQ. simpl in *.
      rewrite EQ. simpl. clear EQ.
      set e.
      rewrite (ucofix_adhoc (to_ucofix (fun x0 : A => ` (f x0)) (inl a))) in e0.
      simpl in e0. rewrite <- H in e0.
      unfold grd in e0. simpl in e0. inversion e0. clear e0.
      rewrite Functor.MAP_COMPOSE.
      apply SPFunctorFacts.INJECTIVE.
      rewrite <- H1.
      repeat rewrite SPFunctorFacts.NATURAL_MAP.
      extensionality s.
      simplify.
      destruct (SPFunctor.embedding PF (A + grd_fcofix A) x s) eqn : EQ; auto.
      f_equal.
      unfold to_fcofix0, grd_fcofix_to_ucofix.
      destruct s0; auto.
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
    to_fcofix f (inr (grd A m)) = Fcofix (fmap (to_fcofix f) m).
  Proof.
    unfold to_fcofix, to_fcofix0, Fcofix. apply sig_unique.
    rewrite (ucofix_adhoc (to_ucofix (fun x : A => ` (f x)) (inr (` (grd A m))))).
    f_equal.
    rewrite Functor.MAP_COMPOSE.
    rewrite SPFunctorFacts.NATURAL_MAP. simpl.
    simplify. extensionality s.
    rewrite SPFunctor._NATURAL_MAP. simplify.
    unfold grd_fcofix_to_ucofix.
    destruct (SPFunctor.embedding PF (A + grd_fcofix A) m s); auto.
    destruct s0; auto.
  Qed.


  Definition bsm_fold_ (bsm : fcofix -> fcofix -> Prop) (x1 x2 : PF fcofix) :=
    frel bsm (femb x1) (femb x2).

  CoInductive bsm : fcofix -> fcofix -> Prop :=
  | bsm_fold : forall (x1 x2 : PF fcofix), frel bsm (femb x1) (femb x2) ->
                                             bsm (Fcofix x1) (Fcofix x2).

  CoInductive u_bsm : ucofix -> ucofix -> Prop :=
  | u_bsm_fold : forall u1 u2, frel u_bsm u1 u2 -> u_bsm (Ucofix u1) (Ucofix u2).

  Lemma eq_u_bsm : forall u1 u2, u1 = u2 -> u_bsm u1 u2.
  Proof.
    cofix.
    intros. subst.
    destruct u2. constructor.
    simplify. intros.
    destruct (u d); constructor.
    - apply eq_u_bsm. auto.
    - constructor.
  Defined.

  Axiom u_bsm_eq : forall u1 u2, u_bsm u1 u2 -> u1 = u2.

  Lemma u_bsm_equiv x1 x2
    : bsm x1 x2 <-> u_bsm (fcofix_to_ucofix x1) (fcofix_to_ucofix x2).
  Proof.
    split; revert x2; revert x1.
    - cofix.
      intros.
      destruct x1, x2. inversion c. inversion c0. inv H.
      constructor. simplify.
      intros. inversion H2. inversion H3. clear H2 H3.
      rewrite H0. rewrite H1.
      destruct (SPFunctor.embedding PF ucofix m d) eqn : EQ1;
      destruct (SPFunctor.embedding PF ucofix m0 d) eqn : EQ2;
      rewrite <- H0 in EQ1; rewrite <- H1 in EQ2.
      + constructor. simpl.
        
        

  Inductive u_bsm_gen1 u_bsm1 : ucofix -> ucofix -> Prop :=
  | _u_bsm_gen1 : forall u1 u2 (R : frel u_bsm1 u1 u2 : Prop),
      u_bsm_gen1 u_bsm1 (Ucofix u1) (Ucofix u2).

  CoInductive u_bsm1 : ucofix -> ucofix -> Prop :=
  | u_bsm_fold1 : forall u1 u2, u_bsm_gen1 u_bsm1 u1 u2 -> u_bsm1 u1 u2.

  Definition bsm1 (x1: fcofix) (x2:  fcofix) : Prop :=
    match x1, x2 with
    | (exist _ u1 _), (exist _ u2 _) => u_bsm1 u1 u2 end.




  Lemma bsm1_unfold x1 x2: bsm1 x1 x2 -> frel bsm1 (fcofix_des x1) (fcofix_des x2).
  Proof.
    intros. destruct x1, x2. inversion c. inversion c0. subst.
    simpl in H. destruct H. inversion H. subst.
    apply SPFunctorFacts.NATURAL_REL.
    

    constructor.


    assert (ssH := femb (fcofix_des (exist c_range (Ucofix u0) c))).

    replace (femb (fcofix_des (exist c_range (Ucofix u0) c))) with u0.
    simpl.
    

    

unfold bsm1 in H.
    


Inductive seq_gen seq : stream → stream → Prop :=
  | _seq_gen : ∀ n s1 s2 (R : seq s1 s2 : Prop), seq_gen seq (cons n s1) (cons n s2).
Hint Constructors seq_gen.

CoInductive seq : stream → stream → Prop :=
  | seq_fold : ∀ s1 s2, seq_gen seq s1 s2 → seq s1 s2.



Opaque Fcofix fcofix_des val grd grd_fcofix_des to_fcofix fcorec.

  Definition fcorec_p A (f: A -> PF A) : A -> fcofix :=
    fcorec (fun a: A => grd A (fmap inl (f a))).

  Lemma fcorec_p_red A (f: A -> PF A) a :
    fcofix_des (fcorec_p f a) = fmap (fcorec_p f) (f a).
  Proof.
    unfold fcorec_p. rewrite fcorec_red. rewrite grd_des_correct.
    simplify. apply Functor.MAP_COMPOSE. 
  Qed.

End FCoFix.


Opaque Fcofix fcofix_des val grd grd_fcofix_des to_fcofix fcorec fcorec_p_red.

Ltac csimpl := repeat (repeat rewrite c_des_correct1;
                       repeat rewrite c_des_correct2;
                       repeat rewrite val_des_correct;
                       repeat rewrite grd_des_correct;
                       repeat rewrite fcorec_red;
                       repeat rewrite fcorec_p_red;
                       repeat rewrite to_fcofix_correct1;
                       repeat rewrite to_fcofix_correct2;
                       repeat rewrite to_fcofix_correct3;
                       simpl).

Ltac csimpl_in H := repeat (repeat rewrite c_des_correct1 in H;
                            repeat rewrite c_des_correct2 in H;
                            repeat rewrite val_des_correct in H;
                            repeat rewrite grd_des_correct in H;
                            repeat rewrite fcorec_red in H;
                            repeat rewrite fcorec_p_red in H;
                            repeat rewrite to_fcofix_correct1 in H;
                            repeat rewrite to_fcofix_correct2 in H;
                            repeat rewrite to_fcofix_correct3 in H;
                            simpl in H).