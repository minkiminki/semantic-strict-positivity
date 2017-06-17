Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.

Arguments proj1_sig {A P} e.

(*
  Functor
 *)

Module PFunctor.

Structure t_data := mk_data
{ Fn :> Type -> Type
; rel : forall X, X -> Fn X -> Type
; map : forall X Y (a : Fn X) (f: forall (x:X), rel x a -> Y), Fn Y
}.

End PFunctor.

(*
  Strictly Positive Universal Functors

  - A functor (fun X => Sh -> X + nat) for a given shape "Sh"
 *)

Module SPUF.

Definition U (Sh: Type) (Ext: Type) (X: Type) := Sh -> (X + Ext).

Inductive u_rel Sh Ext X : X -> U Sh Ext X -> Type :=
| _u_rel u s x (EQ: u s = inl x) : u_rel x u.

Definition map Sh Ext X Y (u: U Sh Ext X) (f: forall (x:X), u_rel x u -> Y) (s : Sh) : Y + Ext.
  destruct (u s) eqn : H.
  - apply _u_rel in H. apply (inl (f _ H)).
  - apply (inr e).
Defined.

End SPUF.

(*
   Semantically Strictly Positive Functors

   - A functor that can be embeded into some universal functor.
*)

Module SSPF.

Structure t := mk
{ Fn :> PFunctor.t_data
; Sh : Type
; Ext : Type
; emb: forall (X: Type) (x : Fn X), (SPUF.U Sh Ext X)

; rel_nat1: forall X x fx,
    Fn.(PFunctor.rel) x fx -> SPUF.u_rel x (emb X fx)
; rel_nat2: forall X x fx,
    SPUF.u_rel x (emb X fx) -> Fn.(PFunctor.rel) x fx

(* Maybe needed for proof
; rel_nat_c1: forall X x fx (r: SPUF.u_rel x (emb X fx)), @rel_nat1 X x fx (@rel_nat2 X x fx r) = r

; rel_nat_c2: forall X x fx (r: Fn.(PFunctor.rel) x fx), @rel_nat2 X x fx (@rel_nat1 X x fx r) = r
*)

; map_nat: forall X Y (fx: Fn X) s (f: forall (x: X), Fn.(PFunctor.rel) x fx -> Y),
    emb Y (Fn.(PFunctor.map) fx f) s = @SPUF.map Sh Ext _ _ (emb X fx)
                                                (fun x r => f x (rel_nat2 r)) s
(* Maybe needed for proof
; inj: forall (X: Type) (m n: Fn X)
         (EQ: emb _ m = emb _ n),
       m = n
*)
}.

End SSPF.


Section SSPF_Fixpoint.

Variable M: SSPF.t.

Inductive Mfixpoint_ : Type :=
| Mfix_mk_ : SPUF.U M.(SSPF.Sh) M.(SSPF.Ext) Mfixpoint_ -> Mfixpoint_.

Inductive PMfixpoint : Mfixpoint_ -> Type :=
| PMfix_mk (m: M Mfixpoint_) (OnTL: forall x, SPUF.u_rel x (M.(SSPF.emb) _ m) -> PMfixpoint x) : PMfixpoint (Mfix_mk_ (M.(SSPF.emb) _ m)).


(* ver 1
Inductive PMfixpoint : Mfixpoint_ -> Type :=
| PMfix_mk (m: M Mfixpoint_) (OnTL: forall x, M.(PFunctor.rel) x m -> PMfixpoint x)
           : PMfixpoint (Mfix_mk_ (M.(SSPF.emb) _ m)).
*)

Inductive Mfixpoint : Type :=
| Mfix_mk' (m: Mfixpoint_) (H: PMfixpoint m) : Mfixpoint.

Definition Mfix_get (m : Mfixpoint) : Mfixpoint_ :=
  match m with
  | @Mfix_mk' m' _ => m' end.

Program Definition Mfix_mk (m : M Mfixpoint) : Mfixpoint :=
  @Mfix_mk' (Mfix_mk_ (M.(SSPF.emb) _ (M.(PFunctor.map) m (fun x _ => Mfix_get x)))) _.
Next Obligation.
  constructor. intros.
  inversion X. subst.
  rewrite SSPF.map_nat in EQ.
  unfold SPUF.map in EQ.
  destruct (SSPF.emb M Mfixpoint m s); inversion EQ.
  destruct m0.
  simpl.
  apply H.
Defined.

Definition Mfix_destruct (x : Mfixpoint) : M Mfixpoint.
  destruct x.
  destruct m.
  inversion H. rewrite <- H1 in *.
  apply (@PFunctor.map M Mfixpoint_ Mfixpoint m 
                       (fun x r => Mfix_mk' (OnTL x (@SSPF.rel_nat1 M _ _ _ r)))).
Defined.

Inductive order_Mfix_ : Mfixpoint_ -> Mfixpoint_ -> Prop:=
| _order_Mfix_ x u : SPUF.u_rel x u -> order_Mfix_ x (Mfix_mk_ u).

Lemma wf_order_Mfix_ : well_founded order_Mfix_.
Proof.
  unfold well_founded. fix 1. intro. destruct a.
  constructor. intros.
  inversion H. inversion X.
  destruct (u s).
  - specialize (wf_order_Mfix_ m). inversion EQ.
    rewrite H5 in wf_order_Mfix_.
    apply wf_order_Mfix_.
  - inversion EQ.
Defined.

Inductive order_Mfix : Mfixpoint -> Mfixpoint -> Prop:=
| _order_Mfix m1 p1 m2 p2 : order_Mfix_ m1 m2 -> order_Mfix (@Mfix_mk' m1 p1) (@Mfix_mk' m2 p2).

Lemma order_Mfix_preserve m1 m2 (ORD: order_Mfix m1 m2) :
  order_Mfix_ (Mfix_get m1) (Mfix_get m2).
Proof.
  inversion ORD. auto.
Defined.


(* ver 1 
Inductive order_Mfix : Mfixpoint -> Mfixpoint -> Prop:=
| _order_Mfix x m : M.(PFunctor.rel) x m -> order_Mfix x (Mfix_mk m).

Lemma order_Mfix_preserve m1 m2 (ORD: order_Mfix m1 m2) :
  order_Mfix_ (Mfix_get m1) (Mfix_get m2).
Proof.
  inversion ORD.
  apply SSPF.rel_nat1 in X. simpl in *.
  constructor. inversion X. subst. apply (SPUF._u_rel _ s).
  rewrite SSPF.map_nat. simpl.
  unfold SPUF.map. rewrite EQ. auto.
Defined.

*)

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
  apply (sub_wellorder Mfix_get _ order_Mfix_preserve wf_order_Mfix_).
Defined.

Inductive Mfix_with_order y : Type :=
| morder x (OR: order_Mfix x y) : Mfix_with_order y.

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

Inductive Mfix_with_s_order y : Type :=
| msorder x (OR: s_order_Mfix x y) : Mfix_with_s_order y.

Definition Mfix_v_get y (x: Mfix_with_order y) : Mfixpoint :=
match x with
| @morder _ x' _ => x' end.

Definition Mfix_s_v_get y (x: Mfix_with_s_order y) : Mfixpoint :=
match x with
| @msorder _ x' _ => x' end.

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

Lemma Mfixpoint_s_fn_correct T
      (FIX: forall m (FN: forall y, s_order_Mfix y m -> T), T) x :
  Mfixpoint_s_fn FIX x = FIX x (fun y _ => Mfixpoint_s_fn FIX y).
Proof.
  unfold Mfixpoint_s_fn. 
  rewrite <- Fix_correct. auto.
Qed.

Lemma Mfixpoint_fn_correct T
      (FIX: forall m (FN: forall y, order_Mfix y m -> T), T) x :
  Mfixpoint_fn FIX x = FIX x (fun y _ => Mfixpoint_fn FIX y).
Proof.
  unfold Mfixpoint_fn. 
  rewrite <- Fix_correct. auto.
Qed.

Lemma Mfixpoint_fn_d_correct (P: Mfixpoint -> Type)
    (FIX: forall m (FN: forall y, order_Mfix y m -> P y), P m) x :
  Mfixpoint_fn_depend P FIX x = FIX x (fun y _ => Mfixpoint_fn_depend P FIX y).
Proof.
  unfold Mfixpoint_fn_depend. 
  rewrite <- Fix_correct. auto.
Qed.

Lemma Mfixpoint_s_fn_d_correct (P: Mfixpoint -> Type)
    (FIX: forall m (FN: forall y, s_order_Mfix y m -> P y), P m) x :
  Mfixpoint_s_fn_depend P FIX x = FIX x (fun y _ => Mfixpoint_s_fn_depend P FIX y).
Proof.
  unfold Mfixpoint_s_fn_depend. 
  rewrite <- Fix_correct. auto.
Qed.

Definition ordered_destruct (x: Mfixpoint) : M (Mfix_with_order x).
  destruct x. destruct H.

  apply (@PFunctor.map M Mfixpoint_ (Mfix_with_order (Mfix_mk' (PMfix_mk m OnTL))) m 
                       (fun (x : Mfixpoint_) (r: M.(PFunctor.rel) x m) => @morder _ 
 (Mfix_mk' (OnTL x (@SSPF.rel_nat1 M _ _ _ r))) (_order_Mfix (OnTL x (@SSPF.rel_nat1 M _ _ _ r)) (PMfix_mk m OnTL) (_order_Mfix_ (M.(SSPF.rel_nat1) _ _ r))))).
Defined.


Definition s_ordered_destruct (x: Mfixpoint) : M (Mfix_with_s_order x).
  destruct x. destruct H.

  apply (@PFunctor.map M Mfixpoint_ (Mfix_with_s_order (Mfix_mk' (PMfix_mk m OnTL))) m 
                       (fun (x : Mfixpoint_) (r: M.(PFunctor.rel) x m) => @msorder _ 
 (Mfix_mk' (OnTL x (@SSPF.rel_nat1 M _ _ _ r))) (base_order (_order_Mfix (OnTL x (@SSPF.rel_nat1 M _ _ _ r)) (PMfix_mk m OnTL) (_order_Mfix_ (M.(SSPF.rel_nat1) _ _ r)))))).
Defined.


(* TODO part

1. uniqueness of PMfixpoint

2. forall x : Mfixpoint, exists m : M Mfixpoint, x = Mfix_mk m

Lemma Mfixpoint_indr x (P: Mfixpoint -> Prop)
    (STEP: forall m (IND: forall y, M.(PFunctor.rel) y m -> P y), P (Mfix_mk m)):
  P x.
Proof.
  assert (H : forall m (IND: forall y, order_Mfix y m -> P y), P m). intros.
  rewrite <- (destruct_correct1 m) in *. apply STEP.
  intros. apply IND. constructor. apply X.
  apply (Mfixpoint_ind' x _ H).
Qed.

Lemma Mfix_mk_inj (m1 m2: M Mfixpoint) (EQ: Mfix_mk m1 = Mfix_mk m2): m1 = m2.
Proof.
  unfold Mfix_mk in EQ.
  inversion EQ. simpl in *.
  apply inj_pair2_eq_dec in H2. subst. auto.
 subst.
  assert (Mfix_mk_obligation_1 m1 = Mfix_mk_obligation_1 m2).
  destruct Mfix_mk'.
  inversion EQ. subst.

Lemma mfix_destruct_correct1 x : Mfix_mk (mfix_destruct x) = x.
Proof.
Qed.

Lemma mfix_destruct_correct2 mx : mfix_destruct (Mfix_mk mx) = mx.
Proof.

Lemma Mfix_with_order_correct x : M.(PFunctor.map) (@Mfix_get x) (ordered_destruct x) = Mfixpoint_destruct x.
Admitted.

Lemma Mfix_with_s_order_correct x : M.(PFunctor.map) (@Mfix_s_get x) (s_ordered_destruct x) = Mfixpoint_destruct x.
Admitted.

Qed.

*)
End SSPF_Fixpoint.

Section Option_SSPF.

Inductive option_rel X : X -> option X -> Type :=
| _option_rel x : option_rel x (Some x).

Definition opt_map X Y (a : option X) (f: forall (x:X), option_rel x a -> Y) : option Y.
  destruct a eqn: EQ.
  - apply (Some (f x (_option_rel x))).
  - apply None.
Defined.

Definition option_Fn :=
  (PFunctor.mk_data option option_rel opt_map).

Definition option_embed X (x: option X) (s: unit) :=
  match x with
  | Some x' => inl x'
  | None => inr tt
  end.

Program Definition Option_sspf : SSPF.t :=
   @SSPF.mk option_Fn unit unit option_embed _ _ _.
Next Obligation.
  unfold option_embed.
  destruct X0.
  apply (SPUF._u_rel _ tt). auto.
Defined.
Next Obligation.
  unfold option_embed in X0.
  destruct fx.
  - inversion X0. inversion EQ.
    apply _option_rel.
  - inversion X0. inversion EQ.
Defined.  
Next Obligation.
  unfold option_embed, SPUF.map. unfold opt_map.
  destruct fx; auto.
Defined.

End Option_SSPF.

Section opt_nat.

Definition nat := Mfixpoint Option_sspf.
Definition O := Mfix_mk Option_sspf None.
Definition S x := Mfix_mk Option_sspf (Some x).

Arguments morder {M y} x OR.
Arguments msorder {M y} x OR.

Definition to_nat_gen (n: nat) (f: forall m, order_Mfix m n-> Datatypes.nat) :=
match ordered_destruct n with
| None => 0
| Some (morder n' pf) => (f n' pf) + 1 end.

Definition to_nat : nat -> Datatypes.nat := Mfixpoint_fn to_nat_gen. 

Definition fibonacci_gen (n: nat) (f: forall m, s_order_Mfix m n-> Datatypes.nat) :=
match s_ordered_destruct n with
| None => 1
| Some (msorder n' pf1) =>
  match s_ordered_destruct n' with
  | None => 1
  | Some (msorder n'' pf2) => (f n' pf1) + (f n'' (link_order pf2 pf1)) end end.

Definition fibonacci : nat -> Datatypes.nat := Mfixpoint_s_fn fibonacci_gen. 


(*
Eval compute in (fibonacci (S (S (S (S (S O)))))).
 = 8
Eval compute in (to_nat (S (S (S (S O))))). 
 = 4
*)

