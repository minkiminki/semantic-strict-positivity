Require Import FunctionalExtensionality ProofIrrelevance ClassicalEpsilon.
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

Definition U (Sh: Type) (X: Type) := Sh -> option X.

Definition map Sh X Y (f: X -> Y) (u: U Sh X): U Sh Y :=
  fun a => option_map f (u a).
Arguments map Sh [X Y] f u.

Definition allP Sh X (P: X -> Prop) (u: U Sh X) : Prop :=
  forall a x (EQ: u a = Some x), P x.

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
  unfold map, option_map in EQ'. 
  destruct (u1 s), (u2 s); eauto; inversion EQ'.
  apply INJ in H0. subst; auto.
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
; tr : NatTrans.t Fn (SPUF.t Sh)
; inh : forall (X: Type), X -> Fn X

; inj: forall (X: Type) (x y: Fn X)
         (EQ: tr _ x = tr _ y),
       x = y
}.

Lemma functor_prop (F: t) : Functor.t_prop F.
Proof.
  split.
  - intros. apply F.(inj). unfold id. 
    rewrite F.(tr).(NatTrans.map_nat).
    rewrite (SPUF.t _).(Functor.map_id). auto.
  - intros. apply F.(inj). unfold compose.
    repeat rewrite F.(tr).(NatTrans.map_nat).
    rewrite (SPUF.t _).(Functor.map_comp). auto.
Qed.

Definition to_functor (F: t) : Functor.t := exist _ _ (functor_prop F).

Definition on_image (F: t) X (u: SPUF.t _ X) (x: F X) : Prop := 
  u = F.(tr) _ x.
Hint Unfold on_image.

Definition back_opt (F: t) (X: Type) (u: SPUF.t _ X) : option (F X) :=
  match excluded_middle_informative (ex (on_image F u)) with
  | left pf => Some (proj1_sig (constructive_indefinite_description _ pf))
  | _ => None
  end.

Definition map_none (T: Type) (t: T) (o: option T) : T :=
  match o with None => t | Some e => e end.

Definition back (F: t) (X: Type) (x: X) (u: SPUF.t _ X) : F X :=
  map_none (F.(inh) x) (back_opt F u).

(*
Definition allP_sig (F: t) X (P: X -> Prop)
    (u: SPUF.t F.(Sh) X)
    (ALL: SPUF.allP P u):
  SPUF.t F.(Sh) (sig P)
:= fun a =>
     match u a as o
       return ((forall x, o = Some x -> P x) -> option {x : X | P x})
     with
     | Some x => fun ALLa => Some (exist P x (ALLa x eq_refl))
     | None =>   fun _ => None
     end (ALL a).
*)

Lemma back_opt_unique (F: t) (X: Type) (fx: F X):
  @back_opt F X (F.(tr) _ fx) = Some fx.
Proof.
  unfold back_opt. destruct (excluded_middle_informative _) as [pf|pf].
  - f_equal. eapply F.(inj). 
    rewrite (proj2_sig (constructive_indefinite_description _ pf)). auto.
  - exfalso. eauto.
Qed.

Lemma back_unique (F: t) (X: Type) x (fx: F X):
  @back F X x (F.(tr) _ fx) = fx.
Proof. unfold back. rewrite back_opt_unique. auto. Qed.

Definition sig_back A (P: A -> Prop) (default: A -> sig P) (a: A) : sig P :=
  match excluded_middle_informative (P a) with
  | left pf => exist _ a pf
  | _ => default a
  end.

Lemma sig_on_image (F: t) A (P: A -> Prop) (m: F (sig P)):
  ex (SSPF.on_image F (SPUF.map _ (@proj1_sig _ _) (F.(tr) _ m))).
Proof.
  eexists (F.(Functor.map) (@proj1_sig _ _) m). red.
  rewrite (F.(tr).(NatTrans.map_nat)). eauto.  
Qed.

Lemma sig_all (F: t) A (P: A -> Prop) (m: F (sig P)):
  SPUF.allP P (SPUF.map _ (@proj1_sig _ _) (F.(tr) _ m)).
Proof.
  red; intros. unfold SPUF.map, option_map in EQ.
  destruct (tr F _ m a); [|inversion EQ].
  destruct s. inversion EQ. subst. auto.
Qed.

Lemma sig_back_proj (F: t) A (P: A -> Prop) def (m: SPUF.t F.(Sh) A)
    (ALL: SPUF.allP P m):
  SPUF.map _ (@proj1_sig _ P) (SPUF.map _ (sig_back def) m) = m.
Proof.
  extensionality s. unfold SPUF.map, option_map. 
  specialize (ALL s). destruct (m s); auto.
  unfold sig_back. 
  destruct (excluded_middle_informative _); [|exfalso]; auto.
Qed.

Lemma sig_back_commute (F: t) A (P: A -> Prop) def (m: F A)
    (ALL: SPUF.allP P (F.(tr) _ m)):
  SPUF.map _ (@proj1_sig _ P) (F.(tr) _ (F.(Functor.map) (sig_back def) m)) 
  = F.(tr) _ m.
Proof.
  rewrite (F.(tr).(NatTrans.map_nat)). simpl.
  rewrite sig_back_proj; eauto.
Qed.

Lemma sig_back_all (F: t) A (P: A -> Prop) (Q: sig P -> Prop) def (m: F A)
    (ALLP: SPUF.allP P (F.(tr) _ m))
    (ALLQ: SPUF.allP (fun a => forall (pf: P a), Q (exist _ _ pf)) 
                     (F.(tr) _ m)):
  SPUF.allP Q (F.(tr) _ (F.(Functor.map) (sig_back def) m)).
Proof.
  red. intros. specialize (ALLP a). specialize (ALLQ a).
  rewrite (F.(tr).(NatTrans.map_nat)) in EQ.
  destruct x. apply ALLQ.
  simpl in *. unfold SPUF.map, option_map in *.
  match goal with [|- ?x = _] => destruct x end; [|inversion EQ].
  unfold sig_back in *. destruct (excluded_middle_informative _).
  - dependent destruction EQ. auto.
  - exfalso. eauto.
Qed.

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
    (OnHD: ex (SSPF.on_image M tl))
    (OnTL: SPUF.allP PMlist tl):
  PMlist (Mcons_ hd tl)
.
Hint Constructors PMlist.

Definition Mlist := sig PMlist.

Definition Mnil : Mlist := exist _ Mnil_ PMnil_.

Definition Mcons (hd: M X) (tl: M Mlist) : Mlist :=
  exist _ (Mcons_ hd (SPUF.map _ (@proj1_sig _ _) (M.(SSPF.tr) _ tl))) 
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
                  (IND: SPUF.allP P (M.(SSPF.tr) _ tl)), 
             P (Mcons hd tl)):
  P l.
Proof.
  destruct l as [l pf]. revert pf. apply (Mlist__ind' l); intros.
  - erewrite (proof_irrelevance _ pf). exact BASE.
  - dependent destruction pf. destruct OnHD as [y OnHD]. red in OnHD. subst.

    specialize (STEP hd (M.(Functor.map) 
                         (@SSPF.sig_back _ PMlist (fun _=>Mnil)) y)).
    revert STEP. unfold Mcons, Mlist.
    match goal with [|- appcontext[exist _ _ ?pf]] => generalize pf end.
    rewrite (SSPF.sig_back_commute M (fun _=>Mnil) y); eauto.
    intros. erewrite (proof_irrelevance _ _). apply STEP.

    apply SSPF.sig_back_all; auto.
Qed.

Fixpoint len (lenM: M nat -> nat) (l: Mlist_) : nat :=
  match l with
  | Mnil_ => 0
  | Mcons_ hd tl => 1 + lenM (SSPF.back _ 0 (SPUF.map _ (len lenM) tl))
  end.

End Mlist.


(* Example: An instance of SSPF.

   We want to show that the standard [list] functor is 
   a semantically strictly positive functor.
*)

Module List_SSPF.

Fixpoint embed X (l: list X) (s: list unit) : option X :=
  match l with
  | nil => None
  | cons hd tl => 
      match s with 
      | cons _ nil => Some hd
      | cons _ stl => embed tl stl
      | _ => None
      end
  end.

Program Definition t : SSPF.t := 
  @SSPF.mk (Functor.mk_data list List.map) (list unit) 
          (NatTrans.mk _ _ embed _) (fun _ _ => nil) _.
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

