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
        (PMfix_mk (SSPF.sig_on_image _ _ m) (SSPF.sig_all _ _ m)).

Lemma Mfix_mk_inj (m1 m2: M Mfixpoint) (EQ: Mfix_mk m1 = Mfix_mk m2): m1 = m2.
Proof.
  unfold Mfix_mk in EQ. dependent destruction EQ.
  apply SPUF.map_injective in x.
  - apply M.(SSPF.inj) in x. auto.
  - intros. destruct x1, x2. simpl in EQ; subst.
    rewrite (proof_irrelevance _ p p0). auto.
Qed.

Lemma Mfixpoint__ind' x (P: Mfixpoint_ -> Prop)
    (STEP: forall u (IND: SPUF.pmap P u), P (Mfix_mk_ u)):
  P x.
Proof.
  revert x. fix 1. intros. destruct x.
  apply STEP. red; intros.
  destruct (u s).
  - specialize (Mfixpoint__ind' m). inversion EQ. 
    subst. apply Mfixpoint__ind'.
  - inversion EQ.
Qed.

Lemma Mfixpoint_ind x (P: Mfixpoint -> Prop)
    (STEP: forall m (IND: @PFunctor.pmap M Mfixpoint P m), P (Mfix_mk m)):
  P x.
Proof.
  destruct x as [x pf]. revert pf. apply (Mfixpoint__ind' x); intros.
  dependent destruction pf.
  destruct OnHD as [y [OnHD UNQ]]. red in OnHD. subst.
  destruct (SSPF.allP_project _ y OnTL) as [y']; subst.
  match goal with [|- context[exist _ _ ?pf]] => generalize pf end.
  rewrite PNatTrans.map_nat; intros.
  erewrite (proof_irrelevance _ _). 
  eapply STEP. apply (PNatTrans.pmap_nat M.(SSPF.emb)).
  eapply SSPF.sig_all2; eauto.
Qed.

Definition default_Mfixpoint_ (d: M False) : Mfixpoint_ :=
  Mfix_mk_ (SPUF.map _ _ (False_rect _) (M.(SSPF.emb) _ d)).

Program Definition default_Mfixpoint (d: M False): Mfixpoint :=
  exist _ (default_Mfixpoint_ d) _. 
Next Obligation.
Proof.
  constructor.
  - exists (M.(PFunctor.map) (False_rect _) d).
    split.
    + unfold SSPF.on_image.
      extensionality s. rewrite PNatTrans.map_nat. simpl.
      destruct ((SSPF.emb M) False d); eauto.
    + intros.
      unfold SSPF.on_image in H. unfold SPUF.map in H.
      apply SSPF.inj.
      rewrite PNatTrans.map_nat. simpl. unfold SPUF.map. apply H.
  - unfold SPUF.pmap. intros.
    unfold SPUF.map in EQ.
    destruct ((SSPF.emb M) False d).
    inversion f. inversion EQ.
Qed.

Definition Mfixpoint_back d (x: Mfixpoint_) : Mfixpoint :=
  match excluded_middle_informative (PMfixpoint x) with
  | left pf => exist _ _ pf
  | _ => default_Mfixpoint d
  end.

Lemma Mfixpoint_back_unique d (x: Mfixpoint) : Mfixpoint_back d (proj1_sig x) = x.
Proof.
  destruct x. unfold Mfixpoint_back.
  destruct (excluded_middle_informative (PMfixpoint (` (exist PMfixpoint x p)))).
  rewrite (proof_irrelevance _ p p0). eauto.
  exfalso. eauto.
Qed.

Fixpoint mfix_fn_' d T (tfix_: M Mfixpoint_ -> M T -> T) (x: Mfixpoint_) : T :=
  match x with
  | Mfix_mk_ x' =>
    tfix_ (SSPF.back _ (M.(PFunctor.map) (False_rect _) d) x') 
          (SSPF.back _ (M.(PFunctor.map) (False_rect _) d)
                     (SPUF.map M.(SSPF.Sh) M.(SSPF.Ext) (mfix_fn_' d tfix_) x'))
  end.

Definition mfix_fn' d T (tfix: M Mfixpoint -> M T -> T) (x: Mfixpoint) : T :=
  let tfix_ x' mv := tfix (M.(PFunctor.map) (Mfixpoint_back d) x') mv in
  (mfix_fn_' d tfix_) (proj1_sig x).

Lemma mfix_fn'_correct d T (tfix: M Mfixpoint -> M T -> T) x' : 
  mfix_fn' d tfix (Mfix_mk x') = tfix x' (M.(PFunctor.map) (mfix_fn' d tfix) x').
Proof.
  unfold mfix_fn'. simpl. f_equal.
  - repeat (setoid_rewrite <- (PNatTrans.map_nat (SSPF.emb M))).
    rewrite SSPF.back_unique. 
    rewrite (PFunctor.map_comp M).
    rewrite <- (PFunctor.map_id M).
    f_equal. extensionality s. rewrite Mfixpoint_back_unique. eauto.
  - rewrite <- (PFunctor.map_comp M).
    repeat setoid_rewrite <- (PNatTrans.map_nat (SSPF.emb M)).
    rewrite SSPF.back_unique. 
    rewrite (PFunctor.map_comp M). auto.
Qed.

Theorem mfix_fn_unique' T (tfix: M Mfixpoint -> M T -> T)
        (mfix'1 mfix'2: Mfixpoint -> T)
        (TFIX1: forall x, mfix'1 (Mfix_mk x) = tfix x (M.(PFunctor.map) mfix'1 x))
        (TFIX2: forall x, mfix'2 (Mfix_mk x) = tfix x (M.(PFunctor.map) mfix'2 x)) :
  mfix'1 = mfix'2.
Proof.
  extensionality s.
  apply (Mfixpoint_ind s).
  intros. rewrite TFIX1. rewrite TFIX2. f_equal.
  apply (SSPF.map_pointwise _ _ _ _ IND).
Qed.
 
Definition Mfixpoint_Empty (EMPTY : M False -> False) (x: Mfixpoint) : False.
Proof.
  intros.
  apply (Mfixpoint_ind x (fun y: Mfixpoint => False)). intros.
  apply EMPTY. apply (PNatTrans.pmap_nat M.(SSPF.emb)) in IND.
  simpl in IND. unfold SPUF.pmap in IND.
  assert (forall s x, (SSPF.emb M) unit (PFunctor.map M (fun x => tt) m) s <> inl x).
  { intros.
    rewrite PNatTrans.map_nat. simpl. unfold SPUF.map.
    specialize (IND s).
    destruct ((SSPF.emb M) Mfixpoint m).
    exfalso. eauto.
    intro. inversion H.
  }
  apply SSPF.uni in H.
  exfalso. destruct H. auto.
Qed.

Theorem mfix_fn_exists T (tfix: M Mfixpoint -> M T -> T) :
  (ex (unique (fun f => forall x, f (Mfix_mk x) = tfix x (M.(PFunctor.map) f x)))).
Proof.
  destruct (excluded_middle_informative (exists d: M False, True)).
  - destruct e as [d _].
    assert (H: forall x, (mfix_fn' d tfix) (Mfix_mk x)
                         = tfix x (PFunctor.map M (mfix_fn' d tfix) x)).
    apply mfix_fn'_correct.
    exists (mfix_fn' d tfix). split.
    apply H. intros. apply (mfix_fn_unique' _ _ _ H H0).
  - assert (F: M False -> False).
    intro. exfalso. eauto.
    exists (fun x => False_rect T (Mfixpoint_Empty F x)).
    split.
    + intros. destruct (Mfixpoint_Empty F (Mfix_mk x)).
    + intros. extensionality s.
      destruct (Mfixpoint_Empty F s).
Qed.

Definition mfix_fn T (tfix: M Mfixpoint -> M T -> T) :=
  proj1_sig (constructive_definite_description _ (mfix_fn_exists tfix)).

Lemma mfix_fn_correct T (tfix: M Mfixpoint -> M T -> T) x' : 
  mfix_fn tfix (Mfix_mk x') = tfix x' (M.(PFunctor.map) (mfix_fn tfix) x').
Proof.
  unfold mfix_fn.
  destruct (constructive_definite_description
      (fun f : Mfixpoint -> T =>
       forall x : M Mfixpoint, f (Mfix_mk x) = tfix x (PFunctor.map M f x))
      (mfix_fn_exists tfix)).
  auto.
Qed.

Lemma mfix_fn_unique T (tfix: M Mfixpoint -> M T -> T) (mfix': Mfixpoint -> T)
    (TFIX: forall x',
           mfix' (Mfix_mk x') = tfix x' (M.(PFunctor.map) mfix' x')):
  mfix' = mfix_fn tfix.
Proof.
  apply (mfix_fn_unique' tfix); auto.
  apply mfix_fn_correct.
Qed.

Definition mfix_destruct := mfix_fn (fun mmx _ => mmx).

Lemma mfix_destruct_correct1 x : Mfix_mk (mfix_destruct x) = x.
Proof.
  apply (Mfixpoint_ind x). intros. unfold mfix_destruct.
  rewrite mfix_fn_correct. auto.
Qed.

Lemma mfix_destruct_correct2 mx : mfix_destruct (Mfix_mk mx) = mx.
Proof.
  apply Mfix_mk_inj.
  apply mfix_destruct_correct1.
Qed.

Opaque Mfixpoint Mfix_mk mfix_fn.

End SSPF_Fixpoint.


Ltac msimpl := repeat (try simpl; try rewrite mfix_fn_correct;
                       try rewrite mfix_destruct_correct1;
                       try rewrite mfix_destruct_correct2; try eauto).


Section Deep_Recursion.

Variable M : SSPF.t.

Definition mfix_fns T (tfix: M T -> T) := mfix_fn (fun x => tfix).

Definition mfix_fn2 T (tfix: M (Mfixpoint M) -> M T -> T) (x: Mfixpoint M) :=
  snd (mfix_fns 
         (fun mxt => (Mfix_mk M (PFunctor.map M fst mxt),
                      tfix (PFunctor.map M fst mxt) (PFunctor.map M snd mxt))) x).

Lemma mfix_fn_equivalent' T (tfix: M (Mfixpoint M) -> M T -> T) x : 
  mfix_fns 
    (fun mxt => (Mfix_mk M (PFunctor.map M fst mxt),
                      tfix (PFunctor.map M fst mxt) (PFunctor.map M snd mxt))) x = 
  (x, mfix_fn tfix x).
Proof.
  apply (Mfixpoint_ind x).
  intros. apply SSPF.map_pointwise in IND.
  unfold mfix_fns. msimpl.
  assert (EQ1 := f_equal (PFunctor.map M fst) IND).
  rewrite (PFunctor.map_comp M fst (fun x => (x, mfix_fn tfix x))) in EQ1.
  rewrite (PFunctor.map_id M) in EQ1.
  f_equal; f_equal; try apply EQ1.
  apply (f_equal (PFunctor.map M snd)) in IND.
  rewrite (PFunctor.map_comp M snd (fun x => (x, mfix_fn tfix x))) in IND.
  rewrite (eta_expansion (mfix_fn tfix)).
  apply IND.
Qed.

Lemma mfix_fn_equivalent T (tfix: M (Mfixpoint M) -> M T -> T) : 
  mfix_fn2 tfix = mfix_fn tfix.
Proof.
  unfold mfix_fn2.
  extensionality s.
  rewrite (mfix_fn_equivalent' tfix s).
  auto.
Qed.

Definition vfx T := Mfixpoint (Prod M (Const T)).

Definition mfix_fnd T (tfix: M (Mfixpoint M) -> M (vfx T) -> T) (x: Mfixpoint M) :=
  let tfix' (mfx : M (Mfixpoint M)) (mvfx : M (vfx T)) : vfx T :=
      Mfix_mk (Prod M (Const T)) (mvfx, tfix mfx mvfx) in
  match mfix_destruct (mfix_fn tfix' x) with
  | (_, t) => t end.

End Deep_Recursion.

(* Example:

   We want to define the list [Mlist M X] parameterized over 
   a strictly postive functors [M] and a base type [X].

   Inductive Mlist (M: Type -> Type) (X: Type) : Type :=
   | Mnil : Mlist M X
   | Mcons (hd: M X) (tl: M (Mlist M X)) : Mlist M X
   .
*)

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
  assert (H := @Mfix_mk_inj F _ _ EQ).
  inversion H. eauto.
Qed.

Lemma Mcons_inj2 hd tl (EQ: Mcons hd tl = Mnil):
  False.
Proof.
  assert (H := @Mfix_mk_inj F _ _ EQ).
  inversion H.
Qed.

Lemma Mlist_ind l (P: Mlist -> Prop)
    (BASE: P Mnil)
    (STEP: forall hd tl 
             (IND: @PFunctor.pmap M Mlist P tl), 
           P (Mcons hd tl)):
  P l.
Proof.
  apply (@Mfixpoint_ind F l P).
  intros. destruct m.
  destruct f. exact BASE.
  destruct f. apply STEP.
  simpl in IND. apply IND.
Qed.

Definition mfix T (tnil: T) (tcons: M X -> M Mlist -> M T -> T) (l: Mlist) : T :=
  let tfix (l': F Mlist) (x: F T) :=
      match l' with
      | inl _ => tnil
      | inr (hd, tl) =>
        match x with 
        | inl _ => tnil
        | inr (_, xr) => tcons hd tl xr
        end
      end in
  mfix_fn tfix l.

Lemma mfix_correct_cons T (tnil: T) (tcons: M X -> M Mlist -> M T -> T) hd tl : 
  mfix tnil tcons (Mcons hd tl) = tcons hd tl (PFunctor.map M (mfix tnil tcons) tl).
Proof.
  apply mfix_fn_correct.
Qed.

Lemma mfix_correct_nil T (tnil: T) (tcons: M X -> M Mlist -> M T -> T) :
  mfix tnil tcons Mnil = tnil.
Proof.
  apply mfix_fn_correct.
Qed.

Lemma mfix_unique T (tnil: T) (tcons: M X -> M Mlist -> M T -> T) mfix'
    (NIL: mfix' Mnil = tnil)
    (CONS: forall hd tl,
           mfix'(Mcons hd tl) = tcons hd tl (M.(PFunctor.map) mfix' tl)):
  mfix' = mfix tnil tcons.
Proof.
  apply mfix_fn_unique. intros.
  simpl. unfold coprod_map. simpl. unfold prod_map. simpl.
  destruct x'.
  destruct f. apply NIL.
  destruct f. apply CONS.
Qed.

Definition len (lenM: M nat -> nat) := @mfix nat 0 (fun _ _ x => 1 + lenM x).

Opaque Mcons Mnil Mlist mfix.

End Mlist.
