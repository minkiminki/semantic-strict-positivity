Require Import FunctionalExtensionality ProofIrrelevance ClassicalDescription.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Logic.Eqdep_dec.
Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.
Require Import ssp combinator.

Arguments proj1_sig {A P} e.

Section SSPF_Fixpoint.

Variable M: SSPF.t.

Inductive Mfixpoint_ : Type :=
| Mfix_mk_ : SPUF.U M.(SSPF.Sh) M.(SSPF.Ext) Mfixpoint_ -> Mfixpoint_.

Inductive PMfixpoint : Mfixpoint_ -> Prop :=
| PMfix_mk m (OnHD: ex (unique (SSPF.on_image M m))) (OnTL: SPUF.pmap PMfixpoint m)
  : PMfixpoint (Mfix_mk_ m).
Hint Constructors PMfixpoint.

Definition Mfixpoint := sig PMfixpoint.

Definition Mfix_mk (m : M Mfixpoint) : Mfixpoint :=
  exist _ (Mfix_mk_ (SPUF.map _ _ proj1_sig (M.(SSPF.emb) _ m)))
        (PMfix_mk (SSPF.sig_on_image _ _ m) (SSPF.sig_all _ _)).

Inductive order_Mfix_ : Mfixpoint_ -> Mfixpoint_ -> Prop:=
| _order_Mfix_ x u : SPUF.u_rel x u -> order_Mfix_ x (Mfix_mk_ u).

Lemma wf_order_Mfix_ : well_founded order_Mfix_.
Proof.
  unfold well_founded. fix 1. intro. destruct a.
  constructor. intros.
  inversion H. inversion H2.
  destruct (u s).
  - specialize (wf_order_Mfix_ m). inversion EQ.
    rewrite H6 in wf_order_Mfix_.
    apply wf_order_Mfix_.
  - inversion EQ.
Qed.

Inductive order_Mfix : Mfixpoint -> Mfixpoint -> Prop:=
| _order_Mfix x m : M.(PFunctor.rel) x m -> order_Mfix x (Mfix_mk m).

Lemma order_Mfix_preserve m1 m2 (ORD: order_Mfix m1 m2) :
  order_Mfix_ (proj1_sig m1) (proj1_sig m2).
Proof.
  inversion ORD.
  apply (PNatTrans.rel_nat M.(SSPF.emb)) in H. simpl in H.
  inversion H. subst.
  unfold Mfix_mk. simpl.
  constructor.
  apply SPUF.u_rel_map. auto.
Qed.

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
Qed.

Lemma sub_wellorder X Y (f: X -> Y) (Rx : X -> X -> Prop) (Ry : Y -> Y -> Prop)
      (H: forall x1 x2 (RE: Rx x1 x2), Ry (f x1) (f x2)) (WF: well_founded Ry) 
  : well_founded Rx.
Proof.
  unfold well_founded. intros. apply (@acc_preserve _ _ f Rx _ H WF (f a)).
  auto.
Qed.

Lemma wf_order_Mfix : well_founded order_Mfix.
Proof.
  apply (sub_wellorder proj1_sig _ order_Mfix_preserve wf_order_Mfix_).
Qed.

Inductive Mfix_with_order y : Type :=
| morder x (OR: order_Mfix x y) : Mfix_with_order y.

Lemma Mfixpoint_ind' x (P: Mfixpoint -> Prop)
    (STEP: forall m (IND: forall y, order_Mfix y m -> P y), P m):
  P x.
Proof.
  apply (Fix wf_order_Mfix _ STEP).
Qed.

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
Qed.

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
Qed.

Inductive Mfix_with_s_order y : Type :=
| msorder x (OR: s_order_Mfix x y) : Mfix_with_s_order y.

Definition Mfix_get y (x: Mfix_with_order y) : Mfixpoint :=
match x with
| @morder _ x' _ => x' end.

Definition Mfix_s_get y (x: Mfix_with_s_order y) : Mfixpoint :=
match x with
| @msorder _ x' _ => x' end.

Definition Mfixpoint_destruct (x: Mfixpoint) : M Mfixpoint.
Admitted.

Lemma destruct_correct1 (x: Mfixpoint) : Mfix_mk (Mfixpoint_destruct x) = x.
Admitted.

Lemma destruct_correct2 (m: M Mfixpoint) : Mfixpoint_destruct (Mfix_mk m) = m.
Admitted.

Definition ordered_destruct (x: Mfixpoint) : M (Mfix_with_order x).
Admitted.

Definition s_ordered_destruct (x: Mfixpoint) : M (Mfix_with_s_order x).
Admitted.

Lemma Mfix_with_order_correct x : M.(PFunctor.map) (@Mfix_get x) (ordered_destruct x) = Mfixpoint_destruct x.
Admitted.

Lemma Mfix_with_s_order_correct x : M.(PFunctor.map) (@Mfix_s_get x) (s_ordered_destruct x) = Mfixpoint_destruct x.
Admitted.

Lemma Mfixpoint_ind x (P: Mfixpoint -> Prop)
    (STEP: forall m (IND: forall y, M.(PFunctor.rel) y m -> P y), P (Mfix_mk m)):
  P x.
Proof.
  assert (H : forall m (IND: forall y, order_Mfix y m -> P y), P m). intros.
  rewrite <- (destruct_correct1 m) in *. apply STEP.
  intros. apply IND. constructor. apply H.
  apply (Mfixpoint_ind' x _ H).
Qed.

Definition Mfixpoint_fn_depend (P: Mfixpoint -> Type)
    (FIX: forall m (FN: forall y, order_Mfix y m -> P y), P m) : forall x, P x :=
  Fix wf_order_Mfix _ FIX.

Definition Mfixpoint_fn T
    (FIX: forall m (FN: forall y, order_Mfix y m -> T), T) x : T :=
  Fix wf_order_Mfix _ FIX x.

Lemma Mfixpoint_s_ind x (P: Mfixpoint -> Prop)
    (STEP: forall m (IND: forall y, s_order_Mfix y m -> P y), P m):
  P x.
Proof.
  apply (Fix wf_s_order_Mfix _ STEP).
Qed.

Definition Mfixpoint_s_fn_depend (P: Mfixpoint -> Type)
    (FIX: forall m (FN: forall y, s_order_Mfix y m -> P y), P m) : forall x, P x :=
  Fix wf_s_order_Mfix _ FIX.

Definition Mfixpoint_s_fn T
    (FIX: forall m (FN: forall y, s_order_Mfix y m -> T), T) x : T :=
  Fix wf_s_order_Mfix _ FIX x.

Lemma Mfixpoint_s_fn_correct T
      (FIX: forall m (FN: forall y, s_order_Mfix y m -> T), T) x :
  Mfixpoint_s_fn FIX x = FIX x (fun y _ => Mfixpoint_s_fn FIX y).
Admitted.

Lemma Mfix_mk_inj (m1 m2: M Mfixpoint) (EQ: Mfix_mk m1 = Mfix_mk m2): m1 = m2.
Proof.
  unfold Mfix_mk in EQ. dependent destruction EQ.
  apply SPUF.map_injective in x.
  - apply M.(SSPF.inj) in x. auto.
  - intros. destruct x1, x2. simpl in EQ; subst.
    rewrite (proof_irrelevance _ p p0). auto.
Qed.

Lemma order_correct a b : order_Mfix a (Mfix_mk b) <-> M.(PFunctor.rel) a b.
Proof.
  split; intros.
  - remember (Mfix_mk b). inversion H.
    subst. apply Mfix_mk_inj in H2. subst. apply H0.
  - constructor. apply H.
Qed.

(* TODO fn_correct *)

End SSPF_Fixpoint.
