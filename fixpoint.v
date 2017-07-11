Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.
Require Import ssp combinator.

Arguments proj1_sig {A P} e.
Arguments projT1 {A P} x.

Section SSPF_Fixpoint.

Variable M: SSPF.t.

Inductive Mfixpoint_ : Type :=
| Mfix_mk_ : SPUF.U M.(SSPF.Sh) M.(SSPF.Ext) Mfixpoint_ -> Mfixpoint_.

Inductive PMfixpoint : Mfixpoint_ -> Type :=
| PMfix_mk (m: M Mfixpoint_)
           (OnTL: forall x, SPUF.u_mem (M.(SSPF.emb) _ m) x -> PMfixpoint x)
  : PMfixpoint (Mfix_mk_ (M.(SSPF.emb) _ m)).

Definition Mfixpoint : Type := sigT PMfixpoint.

Definition Mfix_mk_prop (m : M Mfixpoint)
  : PMfixpoint (Mfix_mk_ (M.(SSPF.emb) _ (M.(PFunctor.map) projT1 m))).
Proof.
  constructor. intros.
  inversion X. subst.
  rewrite SSPF.map_nat in EQ. unfold SPUF.map in EQ.
  destruct ((SSPF.emb M) Mfixpoint m); inversion EQ.
  destruct m0. simpl. auto.
Defined.

Definition Mfix_mk (m: M Mfixpoint) : Mfixpoint := existT _ _ (Mfix_mk_prop m).

Definition Mfix_destruct' (x: Mfixpoint_) (p: PMfixpoint x) : M Mfixpoint_ :=
  match p with
  | PMfix_mk m OnTL => m end.

Definition Mfix_destruct_all (x: Mfixpoint_) (p: PMfixpoint x)
           : forall y, M.(PFunctor.mem) (Mfix_destruct' p) y -> Mfixpoint.
  intros. econstructor.
  destruct p.
  apply SSPF.mem_nat1 in X. simpl in X.
  apply OnTL in X. apply X.
Defined.

Definition Mfix_destruct (x: Mfixpoint) : M Mfixpoint :=
  match x with
  | existT _ _ p => M.(PFunctor.uni) _ (Mfix_destruct_all p) end.

Inductive order_Mfix_' : Mfixpoint_ -> Mfixpoint_ -> Type :=
| _order_Mfix_' x u : SPUF.u_mem u x -> order_Mfix_' x (Mfix_mk_ u).

Inductive order_Mfix_ : Mfixpoint_ -> Mfixpoint_ -> Prop :=
| _order_Mfix_ a b : order_Mfix_' a b -> order_Mfix_ a b.

Lemma wf_order_Mfix_ : well_founded order_Mfix_.
Proof.
  unfold well_founded. fix 1. intro. destruct a.
  constructor. intros.
  inversion H. inversion X. inversion X0.
  destruct (u s).
  - specialize (wf_order_Mfix_ m). inversion EQ. subst.
    apply wf_order_Mfix_.
  - inversion EQ.
Defined.

Lemma Mfix__ind x (P: Mfixpoint_ -> Prop)
    (STEP: forall m (IND: forall y, order_Mfix_ y m -> P y), P m):
  P x.
Proof.
  apply (Fix wf_order_Mfix_ _ STEP).
Defined.

(* test *)

Lemma PMfixpoint_unique x : forall (p1 : PMfixpoint x) (p2 : PMfixpoint x), p1 = p2.
Proof.
  apply (Mfix__ind x). clear x.
  dependent destruction p1.
  dependent destruction p2.
  apply SSPF.inj in x0. subst.
  assert (OnTL = OnTL0).
  extensionality s. extensionality r.
  specialize (IND s (_order_Mfix_ (_order_Mfix_' r))).
  apply IND.
  subst. auto.
Qed.

Lemma mfix_mk'_unique : forall (x1 x2: Mfixpoint_) p1 p2,
    existT PMfixpoint x1 p1 = existT PMfixpoint x2 p2 -> x1 = x2.
Proof.
  intros.
  inversion H. auto.
Qed.

Lemma mfix_mk'_unique2 : forall (x1 x2: Mfixpoint_) p1 p2,
    x1 = x2 -> existT PMfixpoint x1 p1 = existT PMfixpoint x2 p2.
Proof.
  intros.
  subst.
  replace p1 with p2. auto.
  apply PMfixpoint_unique.
Qed.

Lemma mfix_mk_inj m1 m2 (EQ: Mfix_mk m1 = Mfix_mk m2) : m1 = m2.
Proof.
  apply mfix_mk'_unique in EQ. inversion EQ.
  apply SSPF.inj. extensionality s.
  apply equal_f with s in H0.
  repeat rewrite SSPF.map_nat in H0. unfold SPUF.map in H0.
  destruct (SSPF.emb M _ m1), (SSPF.emb M _ m2); inversion H0.
  - destruct m, m0. simpl in H1. subst.
    repeat f_equal. apply PMfixpoint_unique.
  - auto.
Qed.

Lemma destruct_correct1 x : Mfix_mk (Mfix_destruct x) = x.
Proof.
  destruct x. destruct p. unfold Mfix_mk. simpl.
  apply mfix_mk'_unique2.
  f_equal. f_equal.
  apply M.(PFunctor.uni_correct). auto.
Qed.

Lemma destruct_correct2 m : Mfix_destruct (Mfix_mk m) = m.
Proof.
  apply mfix_mk_inj.
  apply destruct_correct1.
Qed.

Inductive order_Mfix : Mfixpoint -> Mfixpoint -> Prop:=
| _order_Mfix m1 p1 m2 p2 : order_Mfix_ m1 m2 ->
                            order_Mfix (existT _ m1 p1) (existT _ m2 p2).

Lemma order_Mfix_preserve m1 m2 (ORD: order_Mfix m1 m2) :
  order_Mfix_ (projT1 m1) (projT1 m2).
Proof.
  inversion ORD. auto.
Defined.

Lemma acc_preserve X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
      (H: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2)) (WF: well_founded Ry )y :
  forall x, y = f x /\ Acc Ry y -> Acc Rx x.
Proof.
  apply (@Fix Y Ry WF (fun a =>  forall x : X, a = f x /\ Acc Ry a -> Acc Rx x)).
  intros. destruct H1.
  constructor. intros.
  subst. specialize (H0 (f y0)).
  specialize (H y0 x0). apply H in H3.
  apply H0.
  apply H3.
  auto.
Defined.

Lemma sub_wellorder X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
      (H: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2)) (WF: well_founded Ry) 
  : well_founded Rx.
Proof.
  unfold well_founded. intros. apply (@acc_preserve _ _ f Rx _ H WF (f a)).
  auto.
Defined.

Lemma wf_order_Mfix : well_founded order_Mfix.
Proof.
  apply (sub_wellorder projT1 _ order_Mfix_preserve wf_order_Mfix_).
Defined.

Lemma Mfixpoint_ind' x (P: Mfixpoint -> Prop)
    (STEP: forall m (IND: forall y, order_Mfix y m -> P y), P m):
  P x.
Proof.
  apply (Fix wf_order_Mfix _ STEP).
Defined.

Inductive s_order_Mfix : Mfixpoint -> Mfixpoint -> Prop :=
| base_order x y (RE: order_Mfix x y) : s_order_Mfix x y
| step_order x y z (Rxy: s_order_Mfix x y) (Ryz: order_Mfix y z) : s_order_Mfix x z.

Lemma wf_s_order_Mfix : well_founded s_order_Mfix.
Proof.
  unfold well_founded. intro. apply (Mfixpoint_ind' a).
  intros.
  constructor. intros.
  destruct H.
  - apply IND, RE.
  - specialize (IND y Ryz).
    destruct IND. eauto.
Defined.

Lemma link_order x y z (Rxy: s_order_Mfix x y) (Ryz: s_order_Mfix y z) :
  s_order_Mfix x z.
Proof.
  revert Ryz. revert Rxy.
  apply (Mfixpoint_ind' z).
  intros.
  destruct Ryz.
  - apply (step_order Rxy RE).
  - specialize (IND _ Ryz0 Rxy Ryz).
    apply (step_order IND Ryz0).
Defined.

Inductive Mfix_with_order y : Type :=
| morder x (OR: s_order_Mfix x y) : Mfix_with_order y.

Definition Mfix_v_get y (x: Mfix_with_order y) : Mfixpoint :=
  match x with
  | @morder _ x' _ => x' end.

Lemma Mfixpoint_s_ind x (P: Mfixpoint -> Prop)
    (STEP: forall m (IND: forall y, s_order_Mfix y m -> P y), P m):
  P x.
Proof.
  apply (Fix wf_s_order_Mfix _ STEP).
Qed.

Definition Mfixpoint_fn_depend (P: Mfixpoint -> Type)
    (FIX: forall m (FN: forall y, s_order_Mfix y m -> P y), P m) : forall x, P x :=
  Fix wf_s_order_Mfix _ FIX.

Definition Mfixpoint_fn T
    (FIX: forall m (FN: forall y, s_order_Mfix y m -> T), T) x : T :=
  Fix wf_s_order_Mfix _ FIX x.

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

Lemma Mfixpoint_fn_correct T
      (FIX: forall m (FN: forall y, s_order_Mfix y m -> T), T) x :
  Mfixpoint_fn FIX (Mfix_mk x) = FIX (Mfix_mk x) (fun y _ => Mfixpoint_fn FIX y).
Proof.
  unfold Mfixpoint_fn. 
  rewrite <- Fix_correct. auto.
Qed.

Lemma Mfixpoint_fn_correct2 T
      (FIX: forall m (FN: forall y, s_order_Mfix y m -> T), T) x :
  Mfixpoint_fn FIX x = FIX x (fun y _ => Mfixpoint_fn FIX y).
Proof.
  unfold Mfixpoint_fn. 
  rewrite <- Fix_correct. auto.
Qed.

Lemma Mfixpoint_fn_d_correct (P: Mfixpoint -> Type)
    (FIX: forall m (FN: forall y, s_order_Mfix y m -> P y), P m) x :
  Mfixpoint_fn_depend P FIX (Mfix_mk x) 
  = FIX (Mfix_mk x) (fun y _ => Mfixpoint_fn_depend P FIX y).
Proof.
  unfold Mfixpoint_fn_depend. 
  rewrite <- Fix_correct. auto.
Qed.

Lemma Mfixpoint_fn_d_correct2 (P: Mfixpoint -> Type)
    (FIX: forall m (FN: forall y, s_order_Mfix y m -> P y), P m) x :
  Mfixpoint_fn_depend P FIX x = FIX x (fun y _ => Mfixpoint_fn_depend P FIX y).
Proof.
  unfold Mfixpoint_fn_depend. 
  rewrite <- Fix_correct. auto.
Qed.

Definition Mfix_destruct_all_ord (x: Mfixpoint_) (p: PMfixpoint x)
           : forall y, M.(PFunctor.mem) (Mfix_destruct' p) y -> Mfix_with_order (existT _ _ p).
  intros.
  destruct p.
  set X. apply SSPF.mem_nat1 in m0.
  set m0.
  apply OnTL in u.
  apply _order_Mfix_' in m0.
  apply _order_Mfix_ in m0.
  set (_order_Mfix u (PMfix_mk m OnTL) m0). 
  apply base_order in o.
  apply morder in o.
  apply o.
Defined.

Definition Mfix_destruct_ord (x: Mfixpoint) : M (Mfix_with_order x) :=
match x with
| existT _ _ p => M.(PFunctor.uni) _ (Mfix_destruct_all_ord p) end.

Definition order_correct1 m x : PFunctor.mem M m x -> order_Mfix x (Mfix_mk m).
Proof.
  intros. destruct x.
  constructor. constructor. constructor.
  apply SSPF.mem_nat1 in X.
  inversion X. subst.
  apply (SPUF._u_mem _ s).
  rewrite SSPF.map_nat. unfold SPUF.map. simpl in *.
  destruct (SSPF.emb M Mfixpoint m); inversion EQ. auto.
Defined.

Definition order_correct2 m x (ORD: order_Mfix x (Mfix_mk m))
  : inhabited (PFunctor.mem M m x).
Proof.
  inversion ORD. inversion H1. inversion X. inversion X0. subst.
  constructor. apply SSPF.mem_nat2.
  apply (SPUF._u_mem _ s).
  rewrite SSPF.map_nat in EQ. unfold SPUF.map in EQ.
  destruct (SSPF.emb M Mfixpoint m); inversion EQ.
  destruct m0. simpl in H0. subst.
  f_equal. f_equal. apply PMfixpoint_unique.
Qed.

Lemma Mfixpoint_indr x (P: Mfixpoint -> Prop)
    (STEP: forall m (IND: forall y, M.(PFunctor.mem) m y -> P y), P (Mfix_mk m)):
  P x.
Proof.
  assert (H : forall m (IND: forall y, order_Mfix y m -> P y), P m). intros.
  rewrite <- (destruct_correct1 m) in *. apply STEP.
  intros. apply IND.
  apply (order_correct1 _ _ X).
  apply (Mfixpoint_ind' x _ H).
Qed.

Definition destruct_order m : forall x, M.(PFunctor.mem) m x -> s_order_Mfix x (Mfix_mk m).
  intros. destruct x. unfold Mfix_mk.
  repeat constructor.
  apply SSPF.mem_nat1 in X.
  inversion X. subst.
  apply (SPUF._u_mem _ s).
  rewrite SSPF.map_nat. unfold SPUF.map.
  destruct (SSPF.emb M Mfixpoint m); inversion EQ.
  auto.
Defined.

Lemma destruct_ord_correct m 
  : Mfix_destruct_ord (Mfix_mk m) 
    = M.(PFunctor.uni) m (fun x r => morder (destruct_order m x r)).
Proof.
  apply SSPF.map_injective with (f := (fun x => projT1 (Mfix_v_get x))).
  - intros. destruct x1, x2. destruct x, x0.
    simpl in EQ. subst.
    assert (EQ := PMfixpoint_unique p p0). subst.
    f_equal. apply proof_irrelevance.
  - simpl. rewrite PFunctor.uni_correct.
    replace (PFunctor.map M (fun x  => projT1 (Mfix_v_get x))
    (PFunctor.uni M m (fun x r => morder (destruct_order m x r)))) with
        (PFunctor.map M projT1 (PFunctor.map M (@Mfix_v_get _)
                                             (PFunctor.uni M m (fun x r =>
                                                morder (destruct_order m x r))))).
    f_equal. rewrite PFunctor.uni_correct. auto.
    { intros. auto. }
    apply M.(PFunctor.map_comp).
    { intros. auto. }
Qed.

Definition prim_rec T (f: M T -> T) := Mfixpoint_fn (fun (m: Mfixpoint) g =>
  let g' (m': Mfix_with_order m) : T :=
    match m' with
    | @morder _ m'' r => g m'' r end in
  f (M.(PFunctor.map) g' (Mfix_destruct_ord m))).

Lemma prim_rec_correct T (f: M T -> T) m :
  prim_rec f (Mfix_mk m) = f (M.(PFunctor.map) (prim_rec f) m).
Proof.
  unfold prim_rec. rewrite Mfixpoint_fn_correct.
  f_equal. rewrite destruct_ord_correct.
  remember (Mfixpoint_fn
           (fun (m0 : Mfixpoint) (g : forall y : Mfixpoint, s_order_Mfix y m0 -> T)
            =>
            f
              (PFunctor.map M
                 (fun m'0 : Mfix_with_order m0 =>
                  match m'0 with
                  | @morder _ m''0 r0 => g m''0 r0
                  end) (Mfix_destruct_ord m0)))) as g.
  replace (fun m' : Mfix_with_order (Mfix_mk m) =>
     match m' with
     | @morder _ m'' _ => g m''
     end) with (fun m' => g (@Mfix_v_get (Mfix_mk m) m')).
  rewrite <- M.(PFunctor.map_comp).
  f_equal. apply PFunctor.uni_correct.
  intros. auto.
  { extensionality s.
    destruct s eqn : EQ.
    auto.
  }
Qed.

End SSPF_Fixpoint.


Section Deep_Recursion.

Variable M : SSPF.t.

Definition vfx T := Mfixpoint (Prod M (Const T)).

Definition mfix_fnd T (tfix: M (vfx T) -> T) (x: Mfixpoint M) :=
  let tfix' (mvfx : M (vfx T)) : vfx T :=
      Mfix_mk (Prod M (Const T)) (mvfx, tfix mvfx) in
  match Mfix_destruct (prim_rec tfix' x) with
  | (_, t) => t end.

End Deep_Recursion.

Opaque Mfixpoint Mfix_destruct Mfix_mk Mfix_destruct_ord Mfixpoint_fn
       Mfixpoint_fn_depend prim_rec destruct_order.

Ltac msimpl := repeat (repeat rewrite Mfixpoint_fn_correct;
                       repeat rewrite Mfixpoint_fn_d_correct;
                       repeat rewrite prim_rec_correct;
                       repeat rewrite destruct_ord_correct;
                       repeat rewrite Mfixpoint_fn_d_correct;
                       repeat rewrite destruct_correct1;
                       repeat rewrite destruct_correct2;
                       simpl).

Ltac msimpl_in H := repeat (repeat rewrite Mfixpoint_fn_correct in H;
                       repeat rewrite Mfixpoint_fn_d_correct in H;
                       repeat rewrite prim_rec_correct in H;
                       repeat rewrite destruct_ord_correct in H;
                       repeat rewrite Mfixpoint_fn_d_correct in H;
                       repeat rewrite destruct_correct1 in H;
                       repeat rewrite destruct_correct2 in H;
                       simpl in H).

Section Mlist.

Variable M : SSPF.t.
Variable X : Type.

Definition F := Coprod (Const unit) (Prod (Const (M X)) M).

Definition Mlist := Mfixpoint F.

Definition Mnil := Mfix_mk F (inl tt).
Definition Mcons (hd : M X) (tl : M Mlist) := Mfix_mk F (inr (hd, tl)).

Lemma Mcons_inj h1 t1 h2 t2
    (EQ: Mcons h1 t1 = Mcons h2 t2):
  h1 = h2 /\ t1 = t2.
Proof.
  assert (H := @mfix_mk_inj F _ _ EQ).
  inversion H. eauto.
Qed.

Lemma Mcons_inj2 hd tl (EQ: Mcons hd tl = Mnil):
  False.
Proof.
  assert (H := @mfix_mk_inj F _ _ EQ).
  inversion H.
Qed.

Lemma Mlist_ind l (P: Mlist -> Prop)
    (BASE: P Mnil)
    (STEP: forall hd tl 
             (IND: forall x, M.(PFunctor.mem) tl x -> P x), 
           P (Mcons hd tl)):
  P l.
Proof.
  apply (@Mfixpoint_indr F l P).
  intros. destruct m.
  - destruct f. exact BASE.
  - destruct f. apply STEP.
    intros. apply IND. apply (inr X0).
Qed.

Definition mfix T (tnil: T) (tcons: M X -> M T -> T) (l: Mlist) : T :=
  @prim_rec F T (fun m => 
                   match m with
                   | inl tt => tnil
                   | inr (mx, mt) => tcons mx mt end) l.

Lemma mfix_correct_cons T (tnil: T) (tcons: M X -> M T -> T) hd tl : 
  mfix tnil tcons (Mcons hd tl) = tcons hd (PFunctor.map M (mfix tnil tcons) tl).
Proof.
  unfold mfix, Mcons.
  msimpl. auto.
Qed.

Lemma mfix_correct_nil T (tnil: T) (tcons: M X -> M T -> T) :
  mfix tnil tcons Mnil = tnil.
Proof.
  unfold mfix, Mnil.
  msimpl. auto.
Qed.

End Mlist.