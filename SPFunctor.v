Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Require Import Functor.

Set Implicit Arguments.
Set Automatic Coercions Import.


(* Classical *)

Theorem dependent_unique_choice :
  forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
    (forall x:A, exists! y : B x, R x y) ->
    { f : forall x:A, B x | forall x:A, R x (f x) }.
Proof.
  intros A B R H.
  assert (Hexuni:forall x, exists! y, R x y).
  intro x. apply H.
  econstructor. instantiate (1 := (fun x => proj1_sig (constructive_definite_description (R x) (Hexuni x)))).
  intro x.
  apply (proj2_sig (constructive_definite_description (R x) (Hexuni x))).
Defined.

Theorem unique_choice :
  forall (A B:Type) (R:A -> B -> Prop),
    (forall x:A,  exists! y : B, R x y) ->
    { f : A -> B | forall x:A, R x (f x) }.
Proof.
  intros A B.
  apply dependent_unique_choice with (B:=fun _:A => B).
Defined.


(* Categories *)

Section UniversalFunctor.
  Variable (Sh1 Sh2: Type).

  Definition UF T := Sh1 -> T + Sh2.

  Definition UF_functorMixin: Functor.mixin_of UF :=
    function_functorMixin Sh1 (coproduct_functorType id_functorType (const_functorType Sh2)).
  Definition UF_sFunctorMixin: SFunctor.mixin_of UF UF_functorMixin.(Functor.map) :=
    function_sFunctorMixin Sh1 (coproduct_sFunctorType id_sFunctorType (const_sFunctorType Sh2)).

  Canonical Structure UF_FunctorType := FunctorType UF_functorMixin.
  Canonical Structure UF_SFunctorType := SFunctorType UF_FunctorType UF_sFunctorMixin.
  Hint Unfold UF_FunctorType.
  Hint Unfold UF_SFunctorType.

  Lemma UF_map_injective X Y (u1 u2: UF X) (f: X -> Y)
        (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
        (EQ: fmap f u1 = fmap f u2):
    u1 = u2.
  Proof.
    extensionality s. apply equal_f with (x:=s) in EQ. simplify. 
    destruct (u1 s), (u2 s); inv EQ; auto.
    apply INJ in H0. subst; auto.
  Qed.

  Lemma UF_map_pointwise X Y (u: UF X) (f g: X -> Y)
        (ALL: forall x, fmem u x -> f x = g x):
    fmap f u = fmap g u.
  Proof.
    extensionality s. simplify.
    destruct (u s) eqn : EQ; auto.
    specialize (ALL x). f_equal. apply ALL.
    econstructor. simplify. rewrite EQ. auto.
  Qed.

End UniversalFunctor.


Module SPFunctor.
  Program Record mixin_of (F: Type -> Type)
          (F_map:forall T1 T2 (f: forall (x1:T1), T2) (fx1:F T1), F T2)
          (F_mem:forall X, F X -> X -> Type)
          (F_rel:forall X Y (rel: X -> Y -> Prop) (fx:F X) (fy:F Y), Prop)
  : Type := Mixin {
    Sh1: Type;
    Sh2: Type;
    embedding: forall T (x: F T), UF Sh1 Sh2 T;

    _INJECTIVE: forall T x1 x2 (EQ: @embedding T x1 = @embedding T x2), x1 = x2;
    _NATURAL_MAP:
      forall T1 T2 (f: T1 -> T2) fx1,
        embedding (F_map _ _ f fx1) = fmap f (embedding fx1);
    _NATURAL_MEM1: forall X fx x, F_mem X fx x -> fmem (embedding fx) x;
    _NATURAL_MEM2: forall X fx x, fmem (embedding fx) x -> F_mem X fx x;
    _NATURAL_REL:
      forall T1 T2 (r: T1 -> T2 -> Prop) fx1 fx2,
        frel r (embedding fx1) (embedding fx2) <-> (F_rel _ _ r fx1 fx2);
  }.

  Record class_of (F: Type -> Type): Type := Class {
    base :> SFunctor.class_of F;
    ext :> mixin_of F base.(SFunctor.base).(Functor.map)
                      base.(SFunctor.ext).(SFunctor.mem) base.(SFunctor.ext).(SFunctor.rel);
  }.

  Structure type: Type := Pack {
    sort :> Type -> Type;
    class :> class_of sort;
    _: Type -> Type;
  }.

  Definition unpack K (k: forall T (c: class_of T), K T c) cF :=
    match cF return K _ (class cF) with
    | Pack c _ => k _ c
    end.

  Definition pack :=
    let k T c m := Pack (Class c m) T in
    SFunctor.unpack _ k.

  Coercion sFunctorType cF := SFunctor.Pack (class cF) cF.
  Coercion functorType cF := Functor.Pack (class cF).(base).(SFunctor.base) cF.

End SPFunctor.

Notation SPFunctorType := SPFunctor.type.
Notation spFunctorType := SPFunctor.pack.
Canonical Structure SPFunctor.sFunctorType.
Canonical Structure SPFunctor.functorType.
Definition functor_embedding F := SPFunctor.embedding (SPFunctor.class F).
Notation "'femb' fx" := (@functor_embedding _ _ fx) (at level 0).
Hint Unfold functor_embedding.

Module SPFunctorFacts.

  Lemma INJECTIVE (PF: SPFunctorType) T (x1 x2: PF T) (EQ: femb x1 = femb x2) :
    x1 = x2.
  Proof.
    apply PF.(SPFunctor._INJECTIVE). apply EQ.
  Qed.

  Lemma NATURAL_MAP (PF: SPFunctorType) T1 T2 (f: T1 -> T2) (fx: PF T1) :
    femb (fmap f fx) = fmap f (femb fx).
  Proof.
    apply SPFunctor._NATURAL_MAP.
  Qed.

  Lemma NATURAL_MEM1 (PF: SPFunctorType) X (fx: PF X) (x: X) :
    fmem fx x -> fmem (femb fx) x.
  Proof.
    apply SPFunctor._NATURAL_MEM1.
  Qed.

  Lemma NATURAL_MEM2 (PF: SPFunctorType) X (fx: PF X) (x: X) :
    fmem (femb fx) x -> fmem fx x.
  Proof.
    apply SPFunctor._NATURAL_MEM2.
  Qed.

  Lemma NATURAL_REL (PF: SPFunctorType) T1 T2 (r: T1 -> T2 -> Prop)
        (fx1: PF T1) (fx2: PF T2) : 
    frel r fx1 fx2 <-> frel r (femb fx1) (femb fx2).
  Proof.
    split; intros.
    - apply SPFunctor._NATURAL_REL. apply H.
    - apply SPFunctor._NATURAL_REL in H. apply H.
  Qed.

  Lemma map_injective (PF: SPFunctorType) X Y (u1 u2: PF X) (f: X -> Y)
         (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
         (EQ: fmap f u1 = fmap f u2):
     u1 = u2.
  Proof.
    apply (SPFunctorFacts.INJECTIVE PF). apply (UF_map_injective INJ).
    repeat rewrite <- SPFunctorFacts.NATURAL_MAP.
    rewrite EQ. auto.
  Qed.

  Lemma map_pointwise (PF: SPFunctorType) X Y (f g: X -> Y) (m: PF X)
        (ALL: forall x, fmem m x -> f x = g x):
    fmap f m = fmap g m.
  Proof.
    apply SPFunctorFacts.INJECTIVE. 
    repeat rewrite SPFunctorFacts.NATURAL_MAP.
    apply UF_map_pointwise.
    intros. apply ALL, NATURAL_MEM2, X0.
  Qed.

End SPFunctorFacts.

(* Fixpoint *)

Section FFix.
  Variable PF: SPFunctorType.

  Inductive ufix: Type :=
  | Ufix: UF PF.(SPFunctor.Sh1) PF.(SPFunctor.Sh2) ufix -> ufix
  .

  Inductive range: forall (u:ufix), Type :=
  | Range
      (m: PF ufix)
      (MEM: forall u, fmem (femb m) u -> range u):
      range (Ufix (femb m))
  .

  Definition ffix := sigT range.

  Definition ffix_to_ufix (x:ffix): ufix := projT1 x.

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
    rewrite SPFunctorFacts.NATURAL_MAP in X. inv X. simplify.
    destruct (SPFunctor.embedding PF ffix x) eqn: EQ; [|inv MEM].
    subst. destruct f. auto.
  Defined. 

  Definition Ffix (x: PF ffix) : ffix :=
    @existT _ _ (Ufix (femb (fmap ffix_to_ufix x))) (Ffix_range x).



  Definition ffix_des0 u (R:range u): PF ufix :=
    match R with
    | Range m _ => m
    end.

  Definition ffix_des1 u (R:range u) x (MEM: fmem (ffix_des0 R) x): ffix.
  Proof.
    econstructor. destruct R. simplify.
    eapply SPFunctorFacts.NATURAL_MEM1 in MEM. simplify.
    apply MEM0. apply MEM.
  Defined.

  Program Definition ffix_des (f:ffix): PF ffix :=
    fmap_dep _ (ffix_des1 (projT2 f)).

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
  | Ffix_ord x y PX PY (ORD: ufix_ord x y): ffix_ord (@existT _ _ x PX) (@existT _ _ y PY)
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

Arguments w_ord {PF y} x ORD.

Opaque ffix Ffix ffix_des ffix_des_ord frec frec_p frec_d destruct_order.

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
    _ _ _ _ _.
Next Obligation.
  eapply fapp in EQ; [|apply ()]. inv EQ. auto.
Qed.
Next Obligation.
  econstructor; [apply ()|].
  econstructor.
Qed.
Next Obligation.
  inv X0. inv MEM. auto.
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
    _ _ _ _ _.
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
  econstructor; [apply ()|].
  econstructor.
Qed.
Next Obligation.
  inv X0. destruct fx; simplify; inv MEM; auto.
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


Module opt_nat.

Definition nat := ffix option_SPFunctorType.
Definition O := Ffix option_SPFunctorType None.
Definition S x := Ffix option_SPFunctorType (Some x).

Definition to_nat := frec (fun (n: nat) f =>
match ffix_des_ord n with
| None => 0
| Some (w_ord n' pf) => (f n' pf) + 1 end).

Lemma sssss : to_nat (S (S (S O))) = 3.
Proof.
  unfold S. unfold to_nat. unfold O.
  msimpl. auto.
Qed.

End opt_nat.