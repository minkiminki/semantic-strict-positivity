Require Import FunctionalExtensionality ProofIrrelevance ClassicalDescription.
Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.
Require Import ssp combinator fixpoint.

Module Monad.

Structure t := mk
{ Fn :> SSPF.t
; ret : PNatTrans.t PFunctor.id_functor Fn
; join : PNatTrans.t (PFunctor.functor_comp Fn Fn) Fn
; monad_law_1 : forall X (x : Fn (Fn (Fn X))), 
  (join X) (join (Fn X) x) = (join X) (Fn.(PFunctor.map) (join X) x)
; monad_law_2 : forall X (x : Fn X),
  (join X) (Fn.(PFunctor.map) (ret X) x) = x
; monad_law_3 : forall X (x : Fn X), (join X) (ret (Fn X) x) = x
}.
(*
Definition ret_type Fn := NatTrans.t id_data Fn.
Definition join_type Fn := NatTrans.t (functor_comp_data Fn Fn) Fn.
*)
Definition bind {M: t} {X Y} (f: X -> M Y) (x: M X) :=
  (join M) Y (M.(PFunctor.map) f x).

Lemma bind_law_1 : forall (M: t) X Y (f: X -> M Y) x, bind f ((ret M) X x) = f x.
Proof.
  intros. unfold bind.
  setoid_rewrite <- PNatTrans.map_nat. rewrite M.(monad_law_3). eauto.
Qed.

Lemma bind_law_2 : forall (M: t) X x, bind ((ret M) X) x = x.
Proof.
  intros. apply M.(monad_law_2).
Qed.

Lemma bind_law_3 : forall (M: t) X Y Z (f : X -> M Y) (g : Y -> M Z) x,
    (bind g) ((bind f) x) = bind (fun x0 => bind g (f x0)) x.
Proof.
  intros. unfold bind.
  rewrite <- PNatTrans.map_nat. rewrite M.(monad_law_1).
  repeat (setoid_rewrite (PFunctor.map_comp M)).
  eauto.
Qed.

Lemma bind_lemma_1 : forall (M: t) X x, PNatTrans.Nt (join M) X x = bind id x. 
Proof.
  intros. unfold bind.
  setoid_rewrite (PFunctor.map_id M). eauto.
Qed.

Lemma bind_lemma_2 : forall (M: t) X Y (f: X -> Y) x,
    PFunctor.map M f x = bind (fun y => (ret M) _ (f y)) x.
Proof.
  intros. unfold bind.
  setoid_rewrite <- ((PFunctor.map_comp M) _ _ _ ((ret M) Y)).
  rewrite M.(monad_law_2). eauto.
Qed.

End Monad.

Module Mlist_Append.

Definition app' {M: Monad.t} {X} (mys : M (Mlist M X))
 :=
  mfix mys (fun xsh xst mv => (Monad.ret M) _ (Mcons _ _ xsh ((Monad.join M) _ mv))).

Definition app {M: Monad.t} {X} (mxs mys : M (Mlist M X)) :=
  Monad.bind (app' mys) mxs.

Lemma app'_bind {M: Monad.t} {X} (mys : M (Mlist M X)) hd tl :
  app' mys (Mcons _ _ hd tl) =
  (Monad.ret M) _ (Mcons _ _ hd (Monad.bind (app' mys) tl)).
Proof.
  unfold app'. apply mfix_correct_cons.
Qed.

Theorem app'_assoc : forall {M: Monad.t} {X} (mys mzs : M (Mlist M X)) xs,
    app (app' mys xs) mzs = app' (app mys mzs) xs.
Proof.
  intros. apply (Mlist_ind xs).
  - unfold app'. repeat rewrite mfix_correct_nil. auto.
  - intros. unfold app. rewrite app'_bind. rewrite app'_bind.
    rewrite Monad.bind_law_1. rewrite app'_bind.
    f_equal. f_equal.
    rewrite Monad.bind_law_3.
    unfold Monad.bind. f_equal. apply SSPF.map_pointwise, IND.
Qed.

Theorem app_assoc : forall {M: Monad.t} {X} (mys mzs mxs : M (Mlist M X)),
    app (app mxs mys) mzs = app mxs (app mys mzs).
Proof.
  intros. unfold app.
  rewrite Monad.bind_law_3. f_equal.
  extensionality x. apply app'_assoc.
Qed.

End Mlist_Append.

(* useful tactic - repeat (try simpl; try setoid_rewrite mfix_r_cons_correct; try setoid_rewrite mfix_r_nil_correct). *)

Module Mlist_Queue.

Definition Queue (M : Monad.t) X := Mlist (Monad.Fn M) X.
Inductive Pair (M : Monad.t) X Y :=
| pair : PFunctor.Fn (Monad.Fn M).(SSPF.Fn) X -> PFunctor.Fn (Monad.Fn M).(SSPF.Fn) Y -> Pair M X Y.

Definition QueueI M X := Pair M (Mlist M.(Monad.Fn) X) (Mlist M.(Monad.Fn) X).

(* TODO *)

End Mlist_Queue.

(*
Module Identity_Monad.

Definition embed X (x : X) (s : unit) : X + nat := inl x.

Program Definition Fn : SSPF.t := 
  @SSPF.mk PFunctor.id_data unit 
          (PNatTrans.mk _ _ embed _ _) tt _ _.
Next Obligation.
  exfalso. specialize (CONST m m). eauto.
Qed.
Next Obligation.
  assert (H := equal_f EQ tt). inversion H. eauto.
Qed.

Program Definition ret : Monad.ret_type Fn := NatTrans.mk _ _ (fun X => id) _.

Program Definition join : Monad.join_type Fn := NatTrans.mk _ _ (fun X => id) _.

Program Definition t : Monad.t := Monad.mk Fn ret join _ _ _.

End Identity_Monad.

Module Option_Monad.

Definition embed X (x : option X) (s : unit) : X + nat :=
  match x with
  | Some x' => inl x'
  | None => inr 0
  end.

Program Definition Fn : SSPF.t := 
  @SSPF.mk (Functor.mk_data option option_map) unit 
          (NatTrans.mk _ _ embed _) (Some tt) _ _.
Next Obligation.
  destruct x; eauto.
Qed.
Next Obligation.
  specialize (CONST tt tt).
  destruct m. destruct u. exfalso. eauto.
  exists None. eauto.
Qed.
Next Obligation.
  destruct m, n; apply equal_f with tt in EQ; simpl in EQ; inversion EQ; eauto.
Qed.

Program Definition ret : Monad.ret_type Fn := NatTrans.mk _ _ (fun X x => Some x) _.

Program Definition join : Monad.join_type Fn := NatTrans.mk _ _(fun X x => match x with | Some x0 => x0 | None => None end) _.
Next Obligation.
  destruct x. destruct o; eauto. eauto.
Qed.

Program Definition t : Monad.t := Monad.mk Fn ret join _ _ _.
Next Obligation.
  destruct x. destruct o; simpl; eauto. eauto.
Qed.
Next Obligation.
  destruct x; simpl; eauto.
Qed.

End Option_Monad.

Module List_Monad.

Definition Fn : SSPF.t := List_SSPF.t.

Program Definition ret : Monad.ret_type Fn := NatTrans.mk _ _ (fun X x => cons x nil) _.

Fixpoint join_Fn X (l : list (list X)) : list X :=
  match l with
  | nil => nil
  | cons hd tl => hd ++ (join_Fn tl)
  end.

Program Definition join : Monad.join_type Fn := NatTrans.mk _ _ join_Fn _.
Next Obligation.
  induction x.
  eauto.
  simpl. rewrite IHx. rewrite List.map_app. eauto.
Qed.

Program Definition t : Monad.t := Monad.mk Fn ret join _ _ _.
Next Obligation.
  induction x.
  eauto.
  simpl. rewrite <- IHx.
  induction a; eauto.
  simpl. rewrite IHa.
  apply List.app_assoc.
Qed.
Next Obligation.
  induction x; eauto.
  simpl. rewrite IHx. eauto.
Qed.
Next Obligation.
  intuition.
Qed.

End List_Monad.

Module Exception_Monad.

Definition embed {A} X (x : X + A) (s : option A) : X + nat :=
  match x with
  | Some x' =>
    (match s with
    | None => inr x
    | Some s' => inl s'
    end)
  | None => inr 0
  end.

Program Definition Fn : SSPF.t := 
  @SSPF.mk (Functor.mk_data option option_map) unit 
          (NatTrans.mk _ _ embed _) (Some tt) _ _.
Next Obligation.
  destruct x; eauto.
Qed.
Next Obligation.
  specialize (CONST tt tt).
  destruct m. destruct u. exfalso. eauto.
  exists None. eauto.
Qed.
Next Obligation.
  destruct m, n; apply equal_f with tt in EQ; simpl in EQ; inversion EQ; eauto.
Qed.

Program Definition ret : Monad.ret_type Fn := NatTrans.mk _ _ (fun X x => Some x) _.

Program Definition join : Monad.join_type Fn := NatTrans.mk _ _(fun X x => match x with | Some x0 => x0 | None => None end) _.
Next Obligation.
  destruct x. destruct o; eauto. eauto.
Qed.

Program Definition t : Monad.t := Monad.mk Fn ret join _ _ _.
Next Obligation.
  destruct x. destruct o; simpl; eauto. eauto.
Qed.

*)