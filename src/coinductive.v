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

(*
  Lemma range_injective x:
    exists! x', Ufix (femb x') = ffix_to_ufix x.
  Proof.
    destruct x. destruct r.
    econstructor. econstructor.
    econstructor. econstructor; eauto.
    intros. inv H. eapply SPFunctor.INJECTIVE; eauto.
  Qed.
*)


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

(*
  Inductive u_bsm_gen u_bsm : ucofix -> ucofix -> Prop :=
  | _u_bsm_gen : forall (u1 u2: UF PF.(SPFunctor.Sh1) PF.(SPFunctor.Sh2) ucofix),
      frel u_bsm u1 u2 -> u_bsm_gen u_bsm (Ucofix u1) (Ucofix u2).
  Hint Constructors u_bsm_gen.
  CoInductive u_bsm : ucofix -> ucofix -> Prop :=
  | u_bsm_fold : forall u1 u2, u_bsm_gen u_bsm u1 u2 -> u_bsm u1 u2.
  Definition BSM : Mcofixpoint -> Mcofixpoint -> Prop.
  Admitted.
  Lemma BSM_Equivalence : equiv _ BSM.
  Admitted.
  Lemma destruct_correct1 x : BSM (Mcofix_mk (Mcofix_destruct x)) x.
  Admitted.
  Lemma destruct_correct2 m : M.(PFunctor.eq) BSM (Mcofix_destruct (Mcofix_mk m)) m.
  Admitted.
  Lemma BSM_1 (m1 m2 : M Mcofixpoint)
    : M.(PFunctor.eq) BSM m1 m2 <-> BSM (Mcofix_mk m1) (Mcofix_mk m2).
  Admitted.
  Lemma BSM_2 (x1 x2 : Mcofixpoint)
    : M.(PFunctor.eq) BSM (Mcofix_destruct x1) (Mcofix_destruct x2) <-> BSM x1 x2.
  Admitted.
  (*
Axiom BSM_eq : forall (x1 x2 : Mcofixpoint), BSM x1 x2 <-> x1 = x2.
   *)
  Lemma des_correct1 x : (Mcofix_mk (Mcofix_destruct x)) = x.
  Admitted.
  Lemma des_correct2 m : (Mcofix_destruct (Mcofix_mk m)) = m.
  Admitted.
*)

  Inductive grd_ucofix (A : Type) : Type :=
  | _val : fcofix -> grd_ucofix A
  | _grd : UF PF.(SPFunctor.Sh1) PF.(SPFunctor.Sh2) (sum A (grd_ucofix A))
             -> grd_ucofix A.

  Inductive grd_range (A: Type) : grd_ucofix A -> Prop :=
  | _val_r x : grd_range (_val A x)
  | _grd_r (m: PF (sum A (grd_ucofix A)))
             (MEM: forall a, fmem (femb m) (inr a) -> grd_range a)
    : grd_range (_grd (femb m)).

  Definition grd_fcofix (A: Type) := sig (@grd_range A). 

  Definition val A (x: fcofix) : grd_fcofix A := exist _ _ (_val_r A x).

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

  Definition grd_fcofix_des A (f: grd_fcofix A)
    : sum fcofix (PF (sum A (grd_fcofix A))).
    destruct f.
    destruct x.
    - apply (inl f).
    - apply inr.
      apply (fmap_dep (grd_fcofix_des0 g) (grd_fcofix_des1 g)).
  Defined.

  Definition val_des_correct A (x: fcofix) : grd_fcofix_des (val A x) = inl x.
  Proof.
    auto.
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
    - destruct x0; [inversion EQ| inversion H].
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

  Definition to_ucofix A (f: A -> grd_ucofix A)
             (s: sum A (grd_ucofix A)) : ucofix.
    revert s. cofix.
    intro.
    destruct s.
    - specialize (f a). 
      destruct f.
      destruct x.
      + destruct f. apply x.
      + apply (Ucofix (fmap to_coinductive u)).

        Guarded.

    specialize (f  term+)
    constructor. unfold UF.
    intros.
    
    

  Definition to_coinductive A (f: A -> grd_fcofix A)
             (s: sum A (grd_fcofix A)) : fcofix.
  Admitted.

  Definition MCoFix A (f: A -> A_or_coinductive A) (a: A) : Mcofixpoint.
  Admitted.

  Lemma MCofix_correct A (f: A -> A_or_coinductive A) (a: A) :
    Mcofix_destruct (MCoFix f a) =
    match (A_or_coinductive_inv (f a)) with
    | inl x => Mcofix_destruct x
    | inr m => M.(PFunctor.map) (to_coinductive f) m end.
  Admitted.

  Lemma to_coinductive_correct1 A (f: A -> A_or_coinductive A) a :
    to_coinductive f (inl a) = MCoFix f a.
  Admitted.

  Lemma to_coinductive_correct2 A (f: A -> A_or_coinductive A) x :
    to_coinductive f (inr (val_A A x)) = x.
  Admitted.

  Lemma to_coinductive_correct3 A (f: A -> A_or_coinductive A) m :
    to_coinductive f (inr (grd_A A m)) = Mcofix_mk (M.(PFunctor.map) (to_coinductive f) m).
  Admitted.
  



  Lemma range_unique x : forall (p1 p2: range x), p1 = p2.
  Proof.
    revert x.
    apply (Fix ufix_ord_wf (fun x => forall p1 p2 : range x, p1 = p2)). intros.
    dependent destruction p1. dependent destruction p2.
    apply SPFunctorFacts.INJECTIVE in x0. subst.
    assert (MEM = MEM0).
    extensionality s. extensionality r.
    apply (H s (Ufix_ord r)).
    subst. auto.
  Qed.

  Lemma range_unique2 : forall (x1 x2: ufix) p1 p2,
    x1 = x2 -> existT range x1 p1 = existT range x2 p2.
  Proof.
    intros. subst.
    replace p1 with p2. auto.
    apply range_unique.
  Qed.

  Lemma Ufix_inj u1 u2 (EQ: Ufix u1 = Ufix u2) : u1 = u2.
  Proof.
    inversion EQ. auto.
  Qed.

  Lemma Ffix_inj x1 x2 (EQ: Ffix x1 = Ffix x2) : x1 = x2.
  Proof.
    unfold Ffix in EQ.
    apply eq_sigT_fst in EQ. apply Ufix_inj in EQ.
    apply SPFunctorFacts.INJECTIVE.
    extensionality s. apply equal_f with s in EQ.
    repeat rewrite SPFunctorFacts.NATURAL_MAP in EQ.
    simplify.
    destruct (SPFunctor.embedding PF ffix x1 s);
    destruct (SPFunctor.embedding PF ffix x2 s); inversion EQ; auto.
    destruct f, f0. simpl in H0. subst.
    f_equal. f_equal. apply range_unique.
  Qed.

  Lemma des_correct1 x: Ffix (ffix_des x) = x.
  Proof.
    destruct x. destruct r. unfold Ffix. simpl.
    apply range_unique2.
    f_equal. f_equal. apply SFunctor.MAP_DEP.
    intros. auto.
  Qed.

  Lemma des_correct2 x: ffix_des (Ffix x) = x.
  Proof.
    apply Ffix_inj.
    apply des_correct1.
  Qed.

  Definition ffix_ord_c := clos_trans_n1 ffix ffix_ord.

  Lemma ffix_ord_c_wf : well_founded ffix_ord_c.
  Proof.
    unfold well_founded. intro. apply (ffix_ord_induction a).
    intros.
    constructor. intros.
    destruct H0.
    - apply H, H0.
    - specialize (H y H0).
      destruct H. eauto.
  Qed.

  Lemma ord_transtive x y z (Rxy: ffix_ord_c x y) (Ryz: ffix_ord_c y z) :
    ffix_ord_c x z.
  Proof.
  revert Ryz. revert Rxy.
  apply (ffix_ord_induction z).
  intros.
  destruct Ryz.
  - apply (tn1_trans _ _ _ _ _ H0 Rxy).
  - specialize (H _ H0 Rxy Ryz).
    apply (tn1_trans _ _ _ _ _ H0 H).
  Defined.

  Inductive less_ones y : Type :=
  | w_ord x (ORD: ffix_ord_c x y) : less_ones y.

  Definition v_get y (x: less_ones y) : ffix :=
    match x with
    | @w_ord _ x' _ => x' end.

  Lemma ffix_str_induction x
        (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord_c x y -> P x) -> P y) :
    P x.
  Proof.
    apply (Fix ffix_ord_c_wf). apply STEP.
  Qed.

  Definition frec_d (P: ffix -> Type)
      (FIX: forall m (FN: forall y, ffix_ord_c y m -> P y), P m) : forall x, P x :=
    Fix ffix_ord_c_wf _ FIX.

  Definition frec T
      (FIX: forall m (FN: forall y, ffix_ord_c y m -> T), T) x : T :=
    Fix ffix_ord_c_wf _ FIX x.

  Lemma Fix_F_eq A (R : A -> A -> Prop) (P : A -> Type) (F : forall x: A, (forall y:A, R y x -> P y) -> P x) :
    forall (x : A) (r: Acc R x),
    @F x (fun (y : A) (p : R y x) => @Fix_F A R P F y (@Acc_inv A R x r y p)) = Fix_F P F r.
  Proof.
    intros. destruct r. simpl. auto.
  Qed.

  Lemma Fix_correct A (R : A -> A -> Prop) (P : A -> Type) (F : forall x: A, (forall y:A, R y x -> P y) -> P x) (W : well_founded R) :
    forall x, F x (fun y _ => (Fix W P F y)) = Fix W P F x.
  Proof.
    intros. unfold Fix.
    rewrite <- (Fix_F_eq _ _ (W x)).
    f_equal. extensionality s1. extensionality s2.
    f_equal. apply proof_irrelevance.
  Qed.

  Lemma frec_red T
        (FIX: forall m (FN: forall y, ffix_ord_c y m -> T), T) x :
    frec FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec FIX y).
  Proof.
    unfold frec. 
    rewrite <- Fix_correct. auto.
  Qed.

  Lemma frec_d_red (P: ffix -> Type)
      (FIX: forall m (FN: forall y, ffix_ord_c y m -> P y), P m) x :
    frec_d P FIX (Ffix x) 
    = FIX (Ffix x) (fun y _ => frec_d P FIX y).
  Proof.
    unfold frec_d. 
    rewrite <- Fix_correct. auto.
  Qed.

  Definition mem_to_ord m x : fmem m x -> ffix_ord x (Ffix m).
  Proof.
    intros. destruct x.
    constructor. constructor. rewrite SPFunctorFacts.NATURAL_MAP. simplify.
    apply SPFunctorFacts.NATURAL_MEM1 in X.
    inv X. simplify. destruct (SPFunctor.embedding PF _ m d) eqn : EQ; [| inv MEM].
    apply (Function_mem _ _ _ d). simplify.
    rewrite EQ. rewrite MEM. auto.
  Defined.


  Definition ord_to_mem m x (ORD: ffix_ord x (Ffix m))
    : inhabited (fmem m x).
  Proof.
    inv ORD. inv ORD0. inv IN. rewrite SPFunctorFacts.NATURAL_MAP in MEM.  simplify.
    constructor. apply SPFunctorFacts.NATURAL_MEM2.
    apply (Function_mem _ _ _ d). simplify.
    destruct (SPFunctor.embedding PF ffix m d); inversion MEM.
    subst. destruct f. f_equal.
    apply range_unique.
  Qed.

  Lemma ffix_mem_induction x (P: ffix -> Prop)
        (STEP: forall m (IND: forall y, fmem m y -> P y), P (Ffix m)):
    P x.
  Proof.
    assert (H : forall m (IND: forall y, ffix_ord y m -> P y), P m). intros.
    rewrite <- (des_correct1 m) in *. apply STEP.
    intros. apply IND.
    apply (mem_to_ord _ _ X).
    apply (ffix_ord_induction x _ H).
  Qed.

  Definition ffix_des_ord' u (R: range u): forall x (MEM: fmem (ffix_des0 R) x),
      less_ones (existT _ _ R).
    intros.
    destruct R. apply SPFunctorFacts.NATURAL_MEM1 in MEM.
    apply (w_ord (tn1_step _ _ _ _ (Ffix_ord (MEM0 _ MEM) (Range m MEM0)
                                             (Ufix_ord MEM)))).
  Defined.

  Definition ffix_des_ord (x: ffix) : PF (less_ones x) :=
    match x with
    | existT _ _ p => fmap_dep _ (ffix_des_ord' p) end.

  Definition destruct_order m : forall x, fmem m x -> ffix_ord_c x (Ffix m).
    intros. destruct x. unfold Ffix.
    repeat constructor.
    apply SPFunctorFacts.NATURAL_MEM1 in X. rewrite SPFunctorFacts.NATURAL_MAP.
    inv X. simplify.
    apply (Function_mem _ _ _ d). simplify.
    destruct (SPFunctor.embedding PF ffix m d); inversion MEM.
    subst. auto.
  Defined.

  Lemma des_ord_correct m 
    : ffix_des_ord (Ffix m) 
      = fmap_dep m (fun x r => w_ord (destruct_order m x r)).
  Proof.
    apply SPFunctorFacts.map_injective with (f := (fun x => projT1 (v_get x))).
    - intros. destruct x1, x2. destruct x, x0.
      simpl in EQ. subst.
      assert (EQ := range_unique r r0). subst.
      f_equal. apply proof_irrelevance.
    - simplify. rewrite SFunctor.MAP_DEP; [| intros; auto].
      replace (Functor.map (SFunctor.base PF) (fun x : less_ones (Ffix m) => projT1 (v_get x))
    (SFunctor.map_dep (SFunctor.ext PF) m
       (fun (x : ffix) (r : SFunctor.mem (SFunctor.ext PF) m x) =>
        w_ord (destruct_order m x r)))) with
          (Functor.map (SFunctor.base PF) (@projT1 _ _) (Functor.map (SFunctor.base PF) (@v_get _)
                                               (SFunctor.map_dep (SFunctor.ext PF) m (fun x r =>
                                                                    w_ord (destruct_order m x r))))); [| apply Functor.MAP_COMPOSE].
      f_equal.
      rewrite SFunctor.MAP_DEP; auto.
  Qed.

  Definition frec_p T (f: PF T -> T) : ffix -> T :=
    frec (fun (m: ffix) g =>
            let g' (m': less_ones m) : T :=
                match m' with
                | @w_ord _ m'' r => g m'' r end in
            f (fmap g' (ffix_des_ord m))).

  Lemma frec_p_red T (f: PF T -> T) m :
    frec_p f (Ffix m) = f (fmap (frec_p f) m).
  Proof.
    unfold frec_p. rewrite frec_red.
    f_equal. rewrite des_ord_correct.
    remember (frec
              (fun (m0 : ffix) (g : forall y : ffix, ffix_ord_c y m0 -> T) =>
               f
                 (fmap (fun m'0 : less_ones m0 =>
                        match m'0 with
                        | @w_ord _ m''0 r0 => g m''0 r0
                        end) (ffix_des_ord m0)))) as g.
    replace (fun m' : less_ones (Ffix m) => match m' with
                                       | @w_ord _ m'' _ => g m''
                                       end) with (fun m' => g (@v_get (Ffix m) m'));
      [| extensionality s; destruct s; auto].
    simplify.
    replace (Functor.map (SFunctor.base PF) (fun m' : less_ones (Ffix m) => g (v_get m'))
    (SFunctor.map_dep (SFunctor.ext PF) m
       (fun (x : ffix) (r : SFunctor.mem (SFunctor.ext PF) m x) =>
        w_ord (destruct_order m x r)))) with
        (Functor.map (SFunctor.base PF) g (Functor.map (SFunctor.base PF) (@v_get _)
                                                       (SFunctor.map_dep (SFunctor.ext PF) m
       (fun (x : ffix) (r : SFunctor.mem (SFunctor.ext PF) m x) =>
        w_ord (destruct_order m x r))))); [| apply Functor.MAP_COMPOSE].
    f_equal. apply SFunctor.MAP_DEP. auto.
  Qed.

End FFix.
