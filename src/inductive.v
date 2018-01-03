Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.

Require Import Functor SPFunctor spec.

Module RINDUCTIVE : INDUCTIVE.

Section FFix.
  Variable PF : Type -> Type.
  Context `{SPF : SPFunctor PF}.

  Inductive ufix: Type :=
  | Ufix: UF (@Sh1 _ _ _ SPF) (@Sh2 _ _ _ SPF) ufix -> ufix
  .

  Inductive range: forall (u:ufix), Prop :=
  | Range
      (m: PF ufix)
      (MEM: forall u, mem (emb _ m) u -> range u):
      range (Ufix (emb _ m))
  .

  Definition ffix := sig range.

  Definition ffix_to_ufix (x:ffix): ufix := proj1_sig x.

  Lemma Ffix_range (x: PF ffix) : range (Ufix (emb _ (map ffix_to_ufix x))).
  Proof.
    constructor. intros.
    rewrite MAP_COMMUTE in H1. inv H1. simplify.
    destruct (emb _ x d) eqn : EQ; [| inv MEM]; simplify.
    subst. destruct i. auto.
  Defined. 

  Definition Ffix (x: PF ffix) : ffix :=
    @exist _ _ (Ufix (emb _ (map ffix_to_ufix x))) (Ffix_range x).

  Lemma ffix_des0' u (R:range u): ex (unique (fun m => u = Ufix (emb _ m))).
  Proof.
    inv R. exists m. split; auto.
    intros. inversion H1. apply INJECTIVE. auto.
  Qed.

  Definition ffix_des0 u (R:range u) : PF ufix :=
    proj1_sig (constructive_definite_description _ (ffix_des0' R)).

  Lemma ffix_des0_correct m f: ffix_des0 (Range m f) = m.
  Proof.
    unfold ffix_des0.
    destruct (constructive_definite_description
                 (fun m0 : PF ufix => Ufix (emb _ m) = Ufix (emb _ m0))
                 (ffix_des0' (Range m f))) eqn : EQ.
    inversion e. apply INJECTIVE in H2. eauto.
  Defined.

  Definition ffix_des1 u (R:range u) x (MEM: mem (ffix_des0 R) x): ffix.
  Proof.
    exists x.
    destruct R. apply MEM0. rewrite ffix_des0_correct in MEM.
    apply MEM_COMMUTE in MEM. auto.
  Defined.

  Definition ffix_des (f:ffix): PF ffix :=
    map_dep (ffix_des0 (proj2_sig f)) (ffix_des1 (proj2_sig f)).

  Inductive ufix_ord: forall (x y:ufix), Prop :=
  | Ufix_ord x u (IN: mem u x): ufix_ord x (Ufix u)
  .

  Lemma ufix_ord_wf: well_founded ufix_ord.
  Proof.
    unfold well_founded. fix 1. intro. destruct a.
    constructor. intros.
    inv H1. inversion IN. simplify.
    destruct (u d); [| inv MEM].
    specialize (ufix_ord_wf i).
    rewrite MEM in ufix_ord_wf.
    apply ufix_ord_wf.
  Qed.

  Inductive ffix_ord': forall (x y:ffix), Prop :=
  | Ffix_ord x y PX PY (ORD: ufix_ord x y): ffix_ord' (@exist _ _ x PX) (@exist _ _ y PY)
  .

  Definition ffix_ord := ffix_ord'.

  Lemma ffix_ord_ufix_ord x y (ORD: ffix_ord x y):
    ufix_ord (ffix_to_ufix x) (ffix_to_ufix y).
  Proof.
    inv ORD. auto.
  Qed.

  Lemma acc_preserve X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
        (SUB: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2))
        (WF: well_founded Ry) y
    : forall x, y = f x /\ Acc Ry y -> Acc Rx x.
  Proof.
    apply (@Fix Y Ry WF (fun a =>  forall x : X, a = f x /\ Acc Ry a -> Acc Rx x)).
    intros. destruct H2. subst.
    constructor. intros. eauto.
  Qed.

  Lemma sub_wellorder X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
        (SUB: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2)) (WF: well_founded Ry) 
    : well_founded Rx.
  Proof.
    unfold well_founded. intros. apply (@acc_preserve _ _ f Rx _ SUB WF (f a)). auto.
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
    apply INJECTIVE.
    extensionality s. apply equal_f with s in EQ.
    repeat rewrite MAP_COMMUTE in EQ.
    simplify.
    destruct (emb _ x1 s);
    destruct (emb _ x2 s); inversion EQ; auto.
    destruct i, i0. simplify. subst.
    f_equal. f_equal. apply proof_irrelevance.
  Qed.

  Lemma des_correct1 x: Ffix (ffix_des x) = x.
  Proof.
    destruct x. destruct r. unfold Ffix.
    apply range_unique2.
    f_equal. f_equal. unfold ffix_des.
    rewrite MAP_DEP; auto.
    unfold ffix_des0.
    destruct (constructive_definite_description
                (fun m0 : PF ufix =>
                   ` (exist range (Ufix (emb _ m)) (Range m MEM)) = Ufix (emb _ m0))
                (ffix_des0' (proj2_sig (exist range (Ufix (emb _ m)) (Range m MEM)))))
             eqn : EQ.
    unfold proj1_sig in *. inversion e.
    apply INJECTIVE in H2. auto.
  Qed.

  Lemma des_correct2 x: ffix_des (Ffix x) = x.
  Proof.
    apply Ffix_inj.
    apply des_correct1.
  Qed.

  Definition ffix_ord_c := clos_trans_n1 ffix_ord.

  Lemma ffix_ord_c_wf : well_founded ffix_ord_c.
  Proof.
    unfold well_founded. intro. apply (ffix_ord_induction a).
    intros.
    constructor. intros.
    destruct H2.
    - apply H1, H2.
    - specialize (H1 y H2).
      destruct H1. eauto.
  Qed.

  Lemma ord_transtive x y z (Rxy: ffix_ord_c x y) (Ryz: ffix_ord_c y z) :
    ffix_ord_c x z.
  Proof.
  revert Ryz. revert Rxy.
  apply (ffix_ord_induction z).
  intros.
  destruct Ryz.
  - apply (tn1_trans _ _ _ _ _ H2 Rxy).
  - specialize (H1 _ H2 Rxy Ryz).
    apply (tn1_trans _ _ _ _ _ H2 H1).
  Qed.

  Definition v_get y (x: @less_ones _ ffix_ord_c y) : ffix :=
    match x with
    | @w_ord _ _ _ x' _ => x' end.

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

  Definition ord_correct m x : mem m x <-> ffix_ord x (Ffix m).
  Proof.
    split; intros.
    - destruct x.
      constructor. constructor. rewrite MAP_COMMUTE. simplify.
      apply MEM_COMMUTE in H1.
      inv H1. simplify. destruct (emb _ m d) eqn : EQ; [| inv MEM].
      apply (Function_mem _ _ d). simplify.
      rewrite EQ. rewrite MEM. simplify. auto.
    - inv H1. inv ORD. inv IN. rewrite MAP_COMMUTE in MEM. simplify.
      apply MEM_COMMUTE.
      apply (Function_mem _ _ d). simplify.
      destruct (emb _ m d); inversion MEM.
      subst. destruct i. simplify. f_equal.
      apply proof_irrelevance.
  Qed.

  Lemma ffix_mem_induction x (P: ffix -> Prop)
        (STEP: forall m (IND: forall y, mem m y -> P y), P (Ffix m)):
    P x.
  Proof.
    assert (H1 : forall m (IND: forall y, ffix_ord y m -> P y), P m). intros.
    rewrite <- (des_correct1 m) in *. apply STEP.
    intros. apply IND.
    apply ord_correct, H1.
    apply (ffix_ord_induction x _ H1).
  Qed.

  Definition ffix_des_ord' u (R: range u): forall x (MEM: mem (ffix_des0 R) x),
      @less_ones _ ffix_ord_c (exist _ _ R).
  Proof.
    intros.
    apply (@w_ord _ _ _ (ffix_des1 R x MEM)).
    destruct R. apply tn1_step. constructor. constructor.
    rewrite <- MEM_COMMUTE.
    rewrite ffix_des0_correct in MEM. auto.
  Defined.

  Definition ffix_des_ord (x: ffix) : PF (less_ones x) :=
    match x with
    | exist _ _ p => map_dep _ (ffix_des_ord' p) end.

  Definition order_part m : forall x, mem m x -> ffix_ord_c x (Ffix m).
    intros. destruct x. unfold Ffix.
    repeat constructor.
    rewrite MEM_COMMUTE in H1. rewrite MAP_COMMUTE.
    inv H1. simplify.
    apply (Function_mem _ _ d). simplify.
    destruct (emb _ m d); inversion MEM. simplify. auto.
  Qed.

  Lemma des_ord_correct m 
    : ffix_des_ord (Ffix m) 
      = map_dep m (fun x r => w_ord _ (order_part m x r)).
  Proof.
    apply (map_injective (fun x => proj1_sig (v_get x))).
    - intros. destruct x1, x2. destruct x, x0.
      simpl in EQ. subst.
      assert (EQ := proof_irrelevance _ r r0). subst.
      f_equal. apply proof_irrelevance.
    - simplify. rewrite MAP_DEP; [| intros; auto].
      unfold Ffix_range. rewrite (ffix_des0_correct (map (ffix_to_ufix) m) _).
      replace (map (fun x : _ => ` (v_get x))
                   (map_dep m
                            (fun (x : ffix) (r : mem m x) =>
                               w_ord x (order_part m x r)))) with
          (map (@proj1_sig _ _) (map (@v_get _) (map_dep m
                                                         (fun (x : ffix) (r : mem m x) =>
                                                            w_ord x (order_part m x r))))); [| apply MAP_COMPOSE].
      f_equal. rewrite MAP_DEP; auto.
  Qed.

  Definition frec_p T (f: PF T -> T) : ffix -> T :=
    frec (fun (m: ffix) g =>
            let g' (m': @less_ones _ ffix_ord_c m) : T :=
                match m' with
                | @w_ord _ _ _ m'' r => g m'' r end in
            f (map g' (ffix_des_ord m))).

  Lemma frec_p_red T (f: PF T -> T) m :
    frec_p f (Ffix m) = f (map (frec_p f) m).
  Proof.
    unfold frec_p. rewrite frec_red.
    f_equal. rewrite des_ord_correct.
    remember (frec
           (fun (m0 : ffix) (g : forall y : ffix, ffix_ord_c y m0 -> T) =>
            f
              (map
                 (fun m'0 : @less_ones _ ffix_ord_c m0 =>
                  match m'0 with
                  | w_ord m''0 r0 => g m''0 r0
                  end) (ffix_des_ord m0)))) as g.
    replace (fun m' : @less_ones _ ffix_ord_c (Ffix m) =>
     match m' with
     | w_ord m'' _ => g m''
     end) with (fun m' => g (@v_get (Ffix m) m'));
      [| extensionality s; destruct s; auto].
    replace (map (fun m' : less_ones (Ffix m) => g (v_get m'))
    (map_dep m
       (fun (x : ffix) (r : mem m x) =>
        w_ord x (order_part m x r)))) with
        (map g (map (@v_get _ ) (map_dep m
       (fun (x : ffix) (r : mem m x) =>
        w_ord x (order_part m x r))))); [| apply Functor.MAP_COMPOSE].
    f_equal. apply MAP_DEP. auto.
  Qed.


End FFix.

End RINDUCTIVE.

Section inductive.

  Variable PF : Type -> Type.
  Context `{H : FunctorData PF}.
  Context `{H0 : @SFunctorData PF _}.
  Context `{SPF : @SPFunctor PF _ _}.

  Definition ffix : Type := @RINDUCTIVE.ffix PF _ _ _. (* inductive type *)

  Definition Ffix : PF ffix -> ffix := @RINDUCTIVE.Ffix PF _ _ _. (* constructor *)

  Definition ffix_des : ffix -> PF ffix := @RINDUCTIVE.ffix_des PF _ _ _. (* destructor *)

  Definition Ffix_inj : forall x1 x2 (EQ: Ffix x1 = Ffix x2), x1 = x2 := @RINDUCTIVE.Ffix_inj PF _ _ _.
  (* constructors are injective *)

  Definition des_correct1 : forall x, Ffix (ffix_des x) = x := @RINDUCTIVE.des_correct1 PF _ _ _.

  Definition des_correct2 : forall x, ffix_des (Ffix x) = x := @RINDUCTIVE.des_correct2 PF _ _ _.
  (* these say that destructors are the inverse of constructors *)


(* order and induction principle *)

  Definition ffix_ord : ffix -> ffix -> Prop := @RINDUCTIVE.ffix_ord PF _ _ _. (* order on ffix *)

  Definition ffix_ord_c := @clos_trans_n1 ffix ffix_ord. (* closure of ffix_ord *)

  Definition ord_correct : forall m x, mem m x <-> ffix_ord x (Ffix m) := @RINDUCTIVE.ord_correct PF _ _ _.
  (* membership relations in SPFunctor became order on ffix *)

  Definition ord_transitive : forall x y z (Rxy: ffix_ord_c x y) (Ryz: ffix_ord_c y z),
      ffix_ord_c x z := @RINDUCTIVE.ord_transtive PF _ _ _.

  Definition ffix_ord_wf: well_founded ffix_ord := @RINDUCTIVE.ffix_ord_wf PF _ _ _.

  Definition ffix_ord_c_wf : well_founded ffix_ord_c := @RINDUCTIVE.ffix_ord_c_wf PF _ _ _.
  (* well order *)

  Definition ffix_des_ord : forall (x: ffix), PF (less_ones x) := @RINDUCTIVE.ffix_des_ord PF _ _ _.
  (* destruct with order *)

  Definition order_part : forall m x, mem m x -> ffix_ord_c x (Ffix m) := @RINDUCTIVE.order_part PF _ _ _.
  (* users don't need to know this *)

  Definition des_ord_correct : forall (m : PF ffix),
      ffix_des_ord (Ffix m) = map_dep m (fun x r => w_ord _ (order_part m x r)) := @RINDUCTIVE.des_ord_correct PF _ _ _.

(* induction principles with different forms *)

  Definition ffix_ord_induction : forall x (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord x y -> P x) -> P y),
    P x := @RINDUCTIVE.ffix_ord_induction PF _ _ _.

  Definition ffix_str_induction : forall x (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord_c x y -> P x) -> P y),
    P x := @RINDUCTIVE.ffix_str_induction PF _ _ _.
    (* strong induction *)

  Definition ffix_mem_induction : forall x (P: ffix -> Prop)
        (STEP: forall m (IND: forall y, mem m y -> P y), P (Ffix m)),
    P x := @RINDUCTIVE.ffix_mem_induction PF _ _ _.


(* recursive function *)

  Definition frec : forall T (FIX: forall m (FN: forall y, ffix_ord_c y m -> T), T),
      ffix -> T := @RINDUCTIVE.frec PF _ _ _.

  Definition frec_d: forall (P: ffix -> Type)
                          (FIX: forall m (FN: forall y, ffix_ord_c y m -> P y), P m),
      forall x : ffix, P x := @RINDUCTIVE.frec_d PF _ _ _.
  (* dependent functions *)

  Definition frec_p : forall T (f: PF T -> T),
      ffix -> T := @RINDUCTIVE.frec_p PF _ _ _.
  (* primitive recursion : simple but not general *)


(* reduction rules for recursive functions *)

  Definition frec_red : forall T
      (FIX: forall m (FN: forall y, ffix_ord_c y m -> T), T) x,
    frec FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec FIX y) := @RINDUCTIVE.frec_red PF _ _ _.

  Definition frec_d_red : forall (P: ffix -> Type)
      (FIX: forall m (FN: forall y, ffix_ord_c y m -> P y), P m) x,
    frec_d P FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec_d P FIX y) := @RINDUCTIVE.frec_d_red PF _ _ _.

  Definition frec_p_red : forall T (f: PF T -> T) m,
    frec_p f (Ffix m) = f (map (frec_p f) m) := @RINDUCTIVE.frec_p_red PF _ _ _.

End inductive.

Global Opaque ffix Ffix ffix_des Ffix_inj des_correct1 des_correct2 ffix_ord ord_correct ord_transitive ffix_ord_wf ffix_ord_c_wf ffix_des_ord order_part des_ord_correct order_part des_ord_correct ffix_ord_induction ffix_str_induction ffix_mem_induction frec frec_d frec_p frec_red frec_d_red frec_p_red.

Ltac msimpl := repeat (autounfold;
                       repeat rewrite frec_red;
                       repeat rewrite frec_d_red;
                       repeat rewrite frec_p_red;
                       repeat rewrite des_ord_correct;
                       repeat rewrite des_correct2;
                       repeat unfold id;
                       simpl).

Ltac msimpl_in H := repeat (autounfold in H;
                            repeat rewrite frec_red in H;
                            repeat rewrite frec_p_red in H;
                            repeat rewrite frec_d_red in H;
                            repeat rewrite des_ord_correct in H;
                            repeat rewrite des_correct2 in H;
                            repeat unfold id in H;
                            simpl in H).

Arguments ffix PF {H} {H0} {SPF}.
Arguments Ffix PF {H} {H0} {SPF}.
Arguments ffix_des {PF} {H} {H0} {SPF}.
