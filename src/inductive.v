Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor.

Section FFix.
  Variable PF: SPFunctorType.

  Inductive ufix: Type :=
  | Ufix: UF PF.(SPFunctor.Sh1) PF.(SPFunctor.Sh2) ufix -> ufix
  .

  Inductive range: forall (u:ufix), Prop :=
  | Range
      (m: PF ufix)
      (MEM: forall u, fmem (femb m) u -> range u):
      range (Ufix (femb m))
  .

  Definition ffix := sig range.

  Definition ffix_to_ufix (x:ffix): ufix := proj1_sig x.

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


  Lemma Ffix_range (x: PF ffix) : range (Ufix (femb (fmap ffix_to_ufix x))).
  Proof.
    constructor. intros.
    rewrite SPFunctorFacts.NATURAL_MAP in H. inv H. simplify.
    destruct (SPFunctor.embedding PF ffix x) eqn: EQ; [|inv MEM].
    subst. destruct f. auto.
  Defined. 

  Definition Ffix (x: PF ffix) : ffix :=
    @exist _ _ (Ufix (femb (fmap ffix_to_ufix x))) (Ffix_range x).

  Lemma ffix_des0' u (R:range u): ex (unique (fun m => u = Ufix (femb m))).
  Proof.
    inv R. exists m. split; auto.
    intros. inversion H. apply (SPFunctorFacts.INJECTIVE _ _ _ H1).
  Qed.

  Definition ffix_des0 u (R:range u) : PF ufix :=
    proj1_sig (constructive_definite_description _ (ffix_des0' R)).

  Lemma ffix_des0_correct m f: ffix_des0 (Range m f) = m.
  Proof.
    unfold ffix_des0.
    destruct (constructive_definite_description
                 (fun m0 : PF ufix => Ufix femb (m) = Ufix femb (m0))
                 (ffix_des0' (Range m f))) eqn : EQ.
    inversion e. apply SPFunctorFacts.INJECTIVE in H0. eauto.
  Defined.

  Definition ffix_des1 u (R:range u) x (MEM: fmem (ffix_des0 R) x): ffix.
  Proof.
    exists x.
    destruct R. apply MEM0. rewrite ffix_des0_correct in MEM.
    apply SPFunctorFacts.NATURAL_MEM in MEM. auto.
  Defined.

  Definition ffix_des (f:ffix): PF ffix :=
    fmap_dep (ffix_des0 (proj2_sig f)) (ffix_des1 (proj2_sig f)).

  Inductive ufix_ord: forall (x y:ufix), Prop :=
  | Ufix_ord x u (IN: fmem u x): ufix_ord x (Ufix u)
  .

  Lemma ufix_ord_wf: well_founded ufix_ord.
  Proof.
    unfold well_founded. fix 1. intro. destruct a.
    constructor. intros.
    inv H. inversion IN. simplify.
    destruct (u d); [| inv MEM].
    specialize (ufix_ord_wf u0).
    rewrite MEM in ufix_ord_wf.
    apply ufix_ord_wf.
  Defined.

  Inductive ffix_ord: forall (x y:ffix), Prop :=
  | Ffix_ord x y PX PY (ORD: ufix_ord x y): ffix_ord (@exist _ _ x PX) (@exist _ _ y PY)
  .

  Lemma ffix_ord_ufix_ord x y (ORD: ffix_ord x y):
    ufix_ord (ffix_to_ufix x) (ffix_to_ufix y).
  Proof.
    inv ORD. auto.
  Qed.

  Lemma acc_preserve X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
        (H: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2))
        (WF: well_founded Ry) y
    : forall x, y = f x /\ Acc Ry y -> Acc Rx x.
  Proof.
    apply (@Fix Y Ry WF (fun a =>  forall x : X, a = f x /\ Acc Ry a -> Acc Rx x)).
    intros. destruct H1. subst.
    constructor. intros. eauto.
  Qed.

  Lemma sub_wellorder X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
        (H: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2)) (WF: well_founded Ry) 
    : well_founded Rx.
  Proof.
    unfold well_founded. intros. apply (@acc_preserve _ _ f Rx _ H WF (f a)). auto.
  Qed.

  Lemma ffix_ord_wf: well_founded ffix_ord.
  Proof.
    apply (sub_wellorder _ _ ffix_ord_ufix_ord ufix_ord_wf).
  Qed.

  Lemma ffix_ord_induction x
        (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord x y -> P x) -> P y) :
    P x.
  Proof.
    apply (Fix ffix_ord_wf). apply STEP.
  Qed.

  Lemma range_unique2 : forall (x1 x2: ufix) p1 p2,
    x1 = x2 -> exist range x1 p1 = exist range x2 p2.
  Proof.
    intros. subst.
    replace p1 with p2. auto.
    apply proof_irrelevance.
  Qed.

  Lemma Ufix_inj u1 u2 (EQ: Ufix u1 = Ufix u2) : u1 = u2.
  Proof.
    inversion EQ. auto.
  Qed.

  Lemma Ffix_inj x1 x2 (EQ: Ffix x1 = Ffix x2) : x1 = x2.
  Proof.
    unfold Ffix in EQ.
    apply eq_sig_fst in EQ. apply Ufix_inj in EQ.
    apply SPFunctorFacts.INJECTIVE.
    extensionality s. apply equal_f with s in EQ.
    repeat rewrite SPFunctorFacts.NATURAL_MAP in EQ.
    simplify.
    destruct (SPFunctor.embedding PF ffix x1 s);
    destruct (SPFunctor.embedding PF ffix x2 s); inversion EQ; auto.
    destruct f, f0. simpl in H0. subst.
    f_equal. f_equal. apply proof_irrelevance.
  Qed.

  Lemma des_correct1 x: Ffix (ffix_des x) = x.
  Proof.
    destruct x. destruct r. unfold Ffix.
    apply range_unique2.
    f_equal. f_equal. unfold ffix_des.
    rewrite SFunctor.MAP_DEP.
    - unfold ffix_des0.
      destruct (constructive_definite_description
     (fun m0 : PF ufix =>
      ` (exist range (Ufix femb (m)) (Range m MEM)) = Ufix femb (m0))
     (ffix_des0' (proj2_sig (exist range (Ufix femb (m)) (Range m MEM)))))
               eqn : EQ.
      unfold proj1_sig in *. inversion e.
      apply SPFunctorFacts.INJECTIVE in H0. auto.
    - auto.
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

  Definition ord_correct m x : fmem m x <-> ffix_ord x (Ffix m).
  Proof.
    split; intros.
    - destruct x.
      constructor. constructor. rewrite SPFunctorFacts.NATURAL_MAP. simplify.
      apply SPFunctorFacts.NATURAL_MEM in H.
      inv H. simplify. destruct (SPFunctor.embedding PF _ m d) eqn : EQ; [| inv MEM].
      apply (Function_mem _ _ _ d). simplify.
      rewrite EQ. rewrite MEM. auto.
    - inv H. inv ORD. inv IN. rewrite SPFunctorFacts.NATURAL_MAP in MEM. simplify.
      apply SPFunctorFacts.NATURAL_MEM.
      apply (Function_mem _ _ _ d). simplify.
      destruct (SPFunctor.embedding PF ffix m d); inversion MEM.
      subst. destruct f. f_equal.
      apply proof_irrelevance.
  Defined.

Check inl.

  Lemma ffix_mem_induction x (P: ffix -> Prop)
        (STEP: forall m (IND: forall y, fmem m y -> P y), P (Ffix m)):
    P x.
  Proof.
    assert (H : forall m (IND: forall y, ffix_ord y m -> P y), P m). intros.
    rewrite <- (des_correct1 m) in *. apply STEP.
    intros. apply IND.
    apply ord_correct, H.
    apply (ffix_ord_induction x _ H).
  Qed.

  Definition ffix_des_ord' u (R: range u): forall x (MEM: fmem (ffix_des0 R) x),
      less_ones (exist _ _ R).
    intros.
    apply (@w_ord _ (ffix_des1 R x MEM)).
    destruct R. apply tn1_step. constructor. constructor.
    apply SPFunctorFacts.NATURAL_MEM.
    rewrite ffix_des0_correct in MEM. auto.
  Defined.

  Definition ffix_des_ord (x: ffix) : PF (less_ones x) :=
    match x with
    | exist _ _ p => fmap_dep _ (ffix_des_ord' p) end.

  Definition order_part m : forall x, fmem m x -> ffix_ord_c x (Ffix m).
    intros. destruct x. unfold Ffix.
    repeat constructor.
    apply SPFunctorFacts.NATURAL_MEM in H. rewrite SPFunctorFacts.NATURAL_MAP.
    inv H. simplify.
    apply (Function_mem _ _ _ d). simplify.
    destruct (SPFunctor.embedding PF ffix m d); inversion MEM.
    subst. auto.
  Defined.

  Lemma des_ord_correct m 
    : ffix_des_ord (Ffix m) 
      = fmap_dep m (fun x r => w_ord (order_part m x r)).
  Proof.
    apply SPFunctorFacts.map_injective with (f := (fun x => proj1_sig (v_get x))).
    - intros. destruct x1, x2. destruct x, x0.
      simpl in EQ. subst.
      assert (EQ := proof_irrelevance _ r r0). subst.
      f_equal. apply proof_irrelevance.
    - simplify. rewrite SFunctor.MAP_DEP; [| intros; auto].
      unfold Ffix_range. rewrite (ffix_des0_correct (fmap (ffix_to_ufix) m) _). 
      replace (Functor.map (SFunctor.base PF) (fun x : less_ones (Ffix m) => proj1_sig (v_get x))
    (SFunctor.map_dep (SFunctor.ext PF) m
       (fun (x : ffix) (r : SFunctor.mem (SFunctor.ext PF) m x) =>
        w_ord (order_part m x r)))) with
          (Functor.map (SFunctor.base PF) (@proj1_sig _ _) (Functor.map (SFunctor.base PF) (@v_get _)
                                               (SFunctor.map_dep (SFunctor.ext PF) m (fun x r =>
                                                                    w_ord (order_part m x r))))); [| apply Functor.MAP_COMPOSE].
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
        w_ord (order_part m x r)))) with
        (Functor.map (SFunctor.base PF) g (Functor.map (SFunctor.base PF) (@v_get _)
                                                       (SFunctor.map_dep (SFunctor.ext PF) m
       (fun (x : ffix) (r : SFunctor.mem (SFunctor.ext PF) m x) =>
        w_ord (order_part m x r))))); [| apply Functor.MAP_COMPOSE].
    f_equal. apply SFunctor.MAP_DEP. auto.
  Qed.

End FFix.

Arguments w_ord {PF y} x ORD.

Opaque ffix Ffix ffix_des ffix_des_ord frec frec_p frec_d order_part.

Ltac msimpl := repeat (autounfold;
                       repeat rewrite frec_red;
                       repeat rewrite frec_d_red;
                       repeat rewrite frec_p_red;
                       repeat rewrite des_ord_correct;
                       repeat rewrite des_correct1;
                       repeat rewrite des_correct2;
                       simpl).

Ltac msimpl_in H := repeat (autounfold;
                            repeat rewrite frec_red in H;
                            repeat rewrite frec_p_red in H;
                            repeat rewrite frec_d_red in H;
                            repeat rewrite des_ord_correct in H;
                            repeat rewrite des_correct1 in H;
                            repeat rewrite des_correct2 in H;
                            simpl in H).

(* Instances *)

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


