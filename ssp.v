Require Import FunctionalExtensionality ProofIrrelevance ClassicalDescription.
Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.

(*
  Functor
 *)

Module Functor.

Structure t_data := mk_data
{ Fn :> Type -> Type
; map : forall X Y (f: X -> Y), Fn X -> Fn Y
}.

Structure t_prop (Fn: t_data) : Prop := mk_prop
{ map_id: forall X x, 
    Fn.(map) (@id X) x = x
; map_comp: forall X Y Z (g: Y -> Z) (f: X -> Y) x, 
    (Fn.(map) g) ((Fn.(map) f) x) = Fn.(map) (fun y => g (f y)) x
}.

Definition t := sig t_prop.

Coercion data (x: t) : t_data := proj1_sig x.
Coercion prop (x: t) : t_prop (data x) := proj2_sig x.

End Functor.

(*
  Natural Transformation
 *)

Module NatTrans.

Structure t (F G: Functor.t_data) := mk
{ Nt :> forall (X: Type) (x: F X), G X

; map_nat: forall X Y (f: X -> Y) x,
    Nt Y (F.(Functor.map) f x) = G.(Functor.map) f (Nt X x)
}.

End NatTrans.

(*
  Strictly Positive Universal Functors

  - A functor (fun X => Sh -> option X) for a given shape "Sh"
 *)

Module SPUF.

Definition U (Sh: Type) (X: Type) := Sh -> (X + bool).

Definition map Sh X Y (f: X -> Y) (u: U Sh X): U Sh Y :=
  fun a => match u a with inl x => inl (f x) | inr b => inr b end.
Arguments map Sh [X Y] f u.

Definition allP Sh X (P: X -> Prop) (u: U Sh X) : Prop :=
  forall a x (EQ: u a = inl x), P x.

Lemma map_id Sh : forall X x, 
  map Sh (@id X) x = x.
Proof.
  intros. extensionality s. 
  unfold map. unfold id. destruct (x s); eauto.
Qed.

Lemma map_comp Sh : forall X Y Z (g: Y -> Z) (f: X -> Y) x, 
  (map Sh g) ((map Sh f) x) = map Sh (fun y => g (f y)) x.
Proof.
  intros. extensionality s. 
  unfold map, compose. destruct (x s); eauto.
Qed.

Definition t Sh : Functor.t := 
  exist _ _ (Functor.mk_prop (Functor.mk_data (U Sh) (map Sh)) 
                             (@map_id Sh) (@map_comp Sh)).

Lemma map_injective Sh X Y u1 u2 (f: X -> Y)
    (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
    (EQ: map Sh f u1 = map Sh f u2):
  u1 = u2.
Proof.
  extensionality s. assert (EQ' := equal_f EQ s).
  unfold map in EQ'. 
  destruct (u1 s), (u2 s); inversion EQ'; subst; eauto.
  apply INJ in H0. subst; auto.
Qed.

Lemma map_pointwise Sh X Y u (f g: X -> Y)
    (ALL: allP (fun x => f x = g x) u):
  map Sh f u = map Sh g u.
Proof.
  extensionality s. specialize (ALL s). unfold map. 
  destruct (u s); eauto.
  simpl. rewrite ALL; eauto.
Qed.

End SPUF.

(*
   Semantically Strictly Positive Functors

   - A functor that can be embeded into some universal functor.
*)

Module SSPF.

Structure t := mk
{ Fn :> Functor.t_data
; Sh : Type
; emb: NatTrans.t Fn (SPUF.t Sh)
; inh: Fn unit (* equivalent to [Fn <> (fun X => Empty_set)] *)

; inj: forall (X: Type) (x y: Fn X)
         (EQ: emb _ x = emb _ y),
       x = y
}.

Lemma functor_prop (M: t) : Functor.t_prop M.
Proof.
  split.
  - intros. apply M.(inj). unfold id. 
    rewrite M.(emb).(NatTrans.map_nat).
    rewrite (SPUF.t _).(Functor.map_id). auto.
  - intros. apply M.(inj). unfold compose.
    repeat rewrite M.(emb).(NatTrans.map_nat).
    rewrite (SPUF.t _).(Functor.map_comp). auto.
Qed.

Coercion to_functor (M: t) : Functor.t := exist _ _ (functor_prop M).

Definition on_image (M: t) X (u: SPUF.t _ X) (x: M X) : Prop := 
  u = M.(emb) _ x.
Hint Unfold on_image.

Definition back_opt (M: t) (X: Type) (u: SPUF.t _ X) : option (M X) :=
  match excluded_middle_informative (ex (unique (on_image M u))) with
  | left pf => Some (proj1_sig (constructive_definite_description _ pf))
  | _ => None
  end.

Definition back (M: t) (X: Type) (x: X) (u: SPUF.t _ X) : M X :=
  match back_opt M u with None => M.(Functor.map) (fun _ => x) M.(inh) | Some e => e end.

Lemma back_opt_unique (M: t) (X: Type) (fx: M X):
  @back_opt M X (M.(emb) _ fx) = Some fx.
Proof.
  unfold back_opt. destruct (excluded_middle_informative _) as [pf|pf].
  - f_equal. eapply M.(inj). 
    rewrite (proj2_sig (constructive_definite_description _ pf)). auto.
  - exfalso. apply pf. exists fx. split; eauto.
    intros. apply M.(SSPF.inj). auto.
Qed.

Lemma back_unique (M: t) (X: Type) x (fx: M X):
  @back M X x (M.(emb) _ fx) = fx.
Proof. unfold back. rewrite back_opt_unique. auto. Qed.

Definition sig_back A (P: A -> Prop) (default: A -> sig P) (a: A) : sig P :=
  match excluded_middle_informative (P a) with
  | left pf => exist _ a pf
  | _ => default a
  end.

Lemma sig_on_image (M: t) A (P: A -> Prop) (m: M (sig P)):
  ex (unique (SSPF.on_image M (SPUF.map _ (@proj1_sig _ _) (M.(emb) _ m)))).
Proof.
  eexists (M.(Functor.map) (@proj1_sig _ _) m). split.
  - red. rewrite (M.(emb).(NatTrans.map_nat)). eauto.  
  - intros. red in H. apply M.(SSPF.inj).
    rewrite <- H. rewrite M.(emb).(NatTrans.map_nat). auto.
Qed.

Lemma sig_all (M: t) A (P: A -> Prop) (m: M (sig P)):
  SPUF.allP P (SPUF.map _ (@proj1_sig _ _) (M.(emb) _ m)).
Proof.
  red; intros. unfold SPUF.map, option_map in EQ.
  destruct (emb M _ m a); [|inversion EQ].
  destruct s. inversion EQ. subst. auto.
Qed.

Lemma sig_back_proj (M: t) A (P: A -> Prop) def (m: SPUF.t M.(Sh) A)
    (ALL: SPUF.allP P m):
  SPUF.map _ (@proj1_sig _ P) (SPUF.map _ (sig_back def) m) = m.
Proof.
  extensionality s. unfold SPUF.map, option_map. 
  specialize (ALL s). destruct (m s); auto.
  unfold sig_back. 
  destruct (excluded_middle_informative _); [|exfalso]; auto.
Qed.

Lemma sig_back_commute (M: t) A (P: A -> Prop) def (m: M A)
    (ALL: SPUF.allP P (M.(emb) _ m)):
  SPUF.map _ (@proj1_sig _ P) (M.(emb) _ (M.(Functor.map) (sig_back def) m)) 
  = M.(emb) _ m.
Proof.
  rewrite (M.(emb).(NatTrans.map_nat)). simpl.
  rewrite sig_back_proj; eauto.
Qed.

Lemma sig_back_all (M: t) A (P: A -> Prop) (Q: sig P -> Prop) def (m: M A)
    (ALLP: SPUF.allP P (M.(emb) _ m))
    (ALLQ: SPUF.allP (fun a => forall (pf: P a), Q (exist _ _ pf)) 
                     (M.(emb) _ m)):
  SPUF.allP Q (M.(emb) _ (M.(Functor.map) (sig_back def) m)).
Proof.
  red. intros. specialize (ALLP a). specialize (ALLQ a).
  rewrite (M.(emb).(NatTrans.map_nat)) in EQ.
  destruct x. apply ALLQ.
  simpl in *. unfold SPUF.map, option_map in *.
  match goal with [|- ?x = _] => destruct x end; [|inversion EQ].
  unfold sig_back in *. destruct (excluded_middle_informative _).
  - dependent destruction EQ. auto.
  - exfalso. eauto.
Qed.

(*
Definition allP_sig (M: t) X (P: X -> Prop)
    (u: SPUF.t M.(Sh) X)
    (ALL: SPUF.allP P u):
  SPUF.t M.(Sh) (sig P)
:= fun a =>
     match u a as o
       return ((forall x, o = Some x -> P x) -> option {x : X | P x})
     with
     | Some x => fun ALLa => Some (exist P x (ALLa x eq_refl))
     | None =>   fun _ => None
     end (ALL a).
*)

End SSPF.


(* Example:

   We want to define the list [Mlist M X] parameterized over 
   a strictly postive functors [M] and a base type [X].

   Inductive Mlist (M: Type -> Type) (X: Type) : Type :=
   | Mnil : Mlist M X
   | Mcons (hd: M X) (tl: M (Mlist M X)) : Mlist M X
   .
*)

Section Mlist.

Variable M: SSPF.t.

Variable X: Type.

Inductive Mlist_ : Type :=
| Mnil_ : Mlist_
| Mcons_ (hd: M X) (tl: SPUF.t (M.(SSPF.Sh)) Mlist_) : Mlist_
.

Inductive PMlist: Mlist_ -> Prop :=
| PMnil_ : PMlist Mnil_
| PMcons_ hd tl 
    (OnHD: ex (unique (SSPF.on_image M tl)))
    (OnTL: SPUF.allP PMlist tl):
  PMlist (Mcons_ hd tl)
.
Hint Constructors PMlist.

Definition Mlist := sig PMlist.

Definition Mnil : Mlist := exist _ Mnil_ PMnil_.

Definition Mcons (hd: M X) (tl: M Mlist) : Mlist :=
  exist _ (Mcons_ hd (SPUF.map _ (@proj1_sig _ _) (M.(SSPF.emb) _ tl))) 
          (PMcons_ _ (SSPF.sig_on_image _ _ tl) (SSPF.sig_all _ _ tl)).

Lemma Mcons_inj h1 t1 h2 t2
    (EQ: Mcons h1 t1 = Mcons h2 t2):
  h1 = h2 /\ t1 = t2.
Proof.
  unfold Mcons in *. dependent destruction EQ.
  split; eauto.
  apply SPUF.map_injective in x.
  - apply M.(SSPF.inj) in x. auto.
  - intros. destruct x1, x2. simpl in EQ; subst.
    rewrite (proof_irrelevance _ p p0). auto.
Qed.

Lemma Mlist__ind' l (P: Mlist_ -> Prop)
    (BASE: P Mnil_)
    (STEP: forall hd tl (IND: SPUF.allP P tl), P (Mcons_ hd tl)):
  P l.
Proof.
  revert l. fix 1. intros. destruct l.
  - exact BASE.
  - apply STEP. red; intros.
    destruct (tl a).
    + specialize (Mlist__ind' m). inversion EQ. 
      subst. apply Mlist__ind'.
    + inversion EQ.
Qed.

Lemma Mlist_ind l (P: Mlist -> Prop)
    (BASE: P Mnil)
    (STEP: forall hd tl 
             (IND: SPUF.allP P (M.(SSPF.emb) _ tl)), 
           P (Mcons hd tl)):
  P l.
Proof.
  destruct l as [l pf]. revert pf. apply (Mlist__ind' l); intros.
  - erewrite (proof_irrelevance _ pf). exact BASE.
  - dependent destruction pf.
    destruct OnHD as [y [OnHD UNQ]]. red in OnHD. subst.

    specialize (STEP hd (M.(Functor.map) 
                         (@SSPF.sig_back _ PMlist (fun _=>Mnil)) y)).
    revert STEP. unfold Mcons, Mlist.
    match goal with [|- appcontext[exist _ _ ?pf]] => generalize pf end.
    rewrite (SSPF.sig_back_commute M (fun _=>Mnil) y); eauto.
    intros. erewrite (proof_irrelevance _ _). apply STEP.

    apply SSPF.sig_back_all; auto.
Qed.

Fixpoint mfix T (tnil: T) (tcons: M X -> M Mlist_ -> M T -> T) (l: Mlist_) : T :=
  match l with
  | Mnil_ => tnil
  | Mcons_ hd tl => tcons hd (SSPF.back _ Mnil_ tl) (SSPF.back _ tnil (SPUF.map _ (mfix tnil tcons) tl))
  end.

Lemma mfix_unique T (tnil: T) (tcons: M X -> M Mlist_ -> M T -> T) mfix'
    (NIL: mfix' Mnil = tnil)
    (CONS: forall hd tl,
           mfix' (Mcons hd tl) = tcons hd (M.(Functor.map) (@proj1_sig _ _) tl) (M.(Functor.map) mfix' tl)):
  forall l: Mlist, mfix tnil tcons (` l) = mfix' l. 
Proof.
  intros. eapply (@Mlist_ind l); eauto.
  intros. rewrite CONS. simpl. f_equal. 
  - setoid_rewrite <- M.(SSPF.emb).(NatTrans.map_nat).
    rewrite SSPF.back_unique. auto.
  - repeat setoid_rewrite <- M.(SSPF.emb).(NatTrans.map_nat).
    rewrite SSPF.back_unique.
    rewrite M.(Functor.map_comp).
    apply M.(SSPF.inj).
    setoid_rewrite M.(SSPF.emb).(NatTrans.map_nat).
    apply SPUF.map_pointwise; eauto.
Qed.

Fixpoint len (lenM: M nat -> nat) (l: Mlist_) : nat :=
  match l with
  | Mnil_ => 0
  | Mcons_ hd tl => 1 + lenM (SSPF.back _ 0 (SPUF.map _ (len lenM) tl))
  end.

Lemma len_unique lenM len'
    (NIL: len' Mnil = 0)
    (CONS: forall hd tl,
           len' (Mcons hd tl) = 1 + lenM (M.(Functor.map) len' tl)):
  forall l: Mlist, len lenM (proj1_sig l) = len' l.
Proof.
  intros. eapply (@Mlist_ind l); eauto.
  intros. rewrite CONS. simpl. f_equal. f_equal.
  repeat setoid_rewrite <- M.(SSPF.emb).(NatTrans.map_nat).
  rewrite SSPF.back_unique.
  rewrite M.(Functor.map_comp).
  apply M.(SSPF.inj).
  setoid_rewrite M.(SSPF.emb).(NatTrans.map_nat).
  apply SPUF.map_pointwise; eauto.
Qed.

End Mlist.


(* Example: An instance of SSPF.

   We want to show that the standard [list] functor is 
   a semantically strictly positive functor.
*)

Module List_SSPF.

Fixpoint embed X (l: list X) (s: list unit) : X + bool :=
  match l with
  | nil => inr false
  | cons hd tl => 
      match s with 
      | cons _ nil => inl hd
      | cons _ stl => embed tl stl
      | _ => inr false
      end
  end.

Program Definition t : SSPF.t := 
  @SSPF.mk (Functor.mk_data list List.map) (list unit) 
          (NatTrans.mk _ _ embed _) nil _.
Next Obligation.
  induction x; eauto.
  extensionality s. simpl. rewrite IHx.
  destruct s; eauto.
  destruct s; eauto.
Qed.
Next Obligation.
  assert (EQ' := equal_f EQ). clear EQ.
  revert y EQ'. induction x; intros.
  - destruct y; eauto. 
    specialize (EQ' (cons tt nil)). inversion EQ'.
  - destruct y.
    + specialize (EQ' (cons tt nil)). inversion EQ'.
    + rewrite (IHx y).
      * specialize (EQ' (cons tt nil)). inversion EQ'; subst; auto.
      * intros. specialize (EQ' (cons tt x1)). 
        destruct x1; eauto.
        destruct x, y; eauto.
Qed.

End List_SSPF.

