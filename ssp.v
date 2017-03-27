Require Import FunctionalExtensionality ProofIrrelevance ClassicalEpsilon.
Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.

Definition compose X Y Z (g: Y -> Z) (f: X -> Y) : X -> Z :=
  fun x => g(f x).

Notation "g @@ f" := (@compose _ _ _ g f) (at level 50).

Lemma compose_fold X Y Z (g: Y -> Z) (f: X -> Y) x:
   g (f x) = (g @@ f) x.
Proof. reflexivity. Qed.

Module Functor.

Structure t_data := mk_data
{ F :> Type -> Type
; map : forall X Y (f: X -> Y), F X -> F Y
}.

Structure t_prop (F: t_data) : Prop := mk_prop
{ map_id: forall X, 
    F.(map) (@id X) = @id _
; map_comp: forall X Y Z (g: Y -> Z) (f: X -> Y), 
    (F.(map) g) @@ (F.(map) f) = F.(map) (g @@ f)
}.

Definition t := sig t_prop.

Coercion data (x: t) : t_data := proj1_sig x.
Coercion prop (x: t) : t_prop (data x) := proj2_sig x.

End Functor.

Module NatTrans.

Structure t (F G: Functor.t_data) := mk
{ N :> forall (X: Type) (x: F X), G X

; map_nat: forall X Y (f: X -> Y) x,
    N Y (F.(Functor.map) f x) = G.(Functor.map) f (N X x)
}.

End NatTrans.

Module Universe.

Definition U (A: Type) (X: Type) := A -> option X.

Definition map A X Y (f: X -> Y) (u: U A X): U A Y :=
  fun a => option_map f (u a).
Arguments map A [X Y] f u.

Definition allP A X (P: X -> Prop) (u: U A X) : Prop :=
  forall a x (EQ: u a = Some x), P x.

Lemma map_id A : forall X, 
  map A (@id X) = @id _.
Proof.
  intros. extensionality x. extensionality a. 
  unfold map. unfold id. destruct (x a); eauto.
Qed.

Lemma map_comp A : forall X Y Z (g: Y -> Z) (f: X -> Y), 
  (map A g) @@ (map A f) = map A (g @@ f).
Proof.
  intros. extensionality x. extensionality a. 
  unfold map, compose. destruct (x a); eauto.
Qed.

Definition t A : Functor.t := 
  exist _ _ (Functor.mk_prop (Functor.mk_data (U A) (map A)) (@map_id A) (@map_comp A)).

Lemma map_injective A X Y u1 u2 (f: X -> Y)
    (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
    (EQ: map A f u1 = map A f u2):
  u1 = u2.
Proof.
  extensionality a. assert (EQ' := equal_f EQ a).
  unfold map, option_map in EQ'. 
  destruct (u1 a), (u2 a); eauto; inversion EQ'.
  apply INJ in H0. subst; auto.
Qed.

End Universe.

Module SSP.

Structure t := mk
{ F :> Functor.t_data
; A : Type
; tr : NatTrans.t F (Universe.t A)
; inh (X: Type) (x: X) : F X

; inj: forall (X: Type) (x y: F X)
         (EQ: tr _ x = tr _ y),
       x = y
}.

Lemma functor_prop (F: t) : Functor.t_prop F.
Proof.
  split.
  - intros. extensionality a. apply F.(inj). unfold id. 
    rewrite F.(tr).(NatTrans.map_nat).
    rewrite (Universe.t _).(Functor.map_id). auto.
  - intros. extensionality a. apply F.(inj). unfold compose.
    repeat rewrite F.(tr).(NatTrans.map_nat).
    rewrite (compose_fold (Functor.map _ _)). 
    rewrite (Universe.t _).(Functor.map_comp). auto.
Qed.

Definition to_functor (F: t) : Functor.t := exist _ _ (functor_prop F).

Definition on_image (F: t) X (u: Universe.t _ X) (x: F X) : Prop := 
  u = F.(tr) _ x.
Hint Unfold on_image.

Definition back_opt (F: t) (X: Type) (u: Universe.t _ X) : option (F X) :=
  match excluded_middle_informative (ex (on_image F u)) with
  | left pf => Some (proj1_sig (constructive_indefinite_description _ pf))
  | _ => None
  end.

Definition map_none (T: Type) (t: T) (o: option T) : T :=
  match o with None => t | Some e => e end.

Definition back (F: t) (X: Type) (x: X) (u: Universe.t _ X) : F X :=
  map_none (F.(inh) x) (back_opt F u).

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

(* Definition allP_sig A X (P: X -> Prop)  *)
(*     (u: Universe.t A X)  *)
(*     (ALL: Universe.allP P u): *)
(*   Universe.t A (sig P) *)
(* := fun a => *)
(*      match u a as o  *)
(*        return ((forall x, o = Some x -> P x) -> option {x : X | P x}) *)
(*      with *)
(*      | Some x => fun ALLa => Some (exist P x (ALLa x eq_refl)) *)
(*      | None =>   fun _ => None *)
(*      end (ALL a). *)

Definition sig_back A (P: A -> Prop) (default: A -> sig P) (a: A) : sig P :=
  match excluded_middle_informative (P a) with
  | left pf => exist _ a pf
  | _ => default a
  end.

Lemma sig_on_image (F: t) A (P: A -> Prop) (m: F (sig P)):
  ex (SSP.on_image F (Universe.map _ (@proj1_sig _ _) (F.(tr) _ m))).
Proof.
  eexists (F.(Functor.map) (@proj1_sig _ _) m). red.
  rewrite (F.(tr).(NatTrans.map_nat)). eauto.  
Qed.

Lemma sig_all (F: t) A (P: A -> Prop) (m: F (sig P)):
  Universe.allP P (Universe.map _ (@proj1_sig _ _) (F.(tr) _ m)).
Proof.
  red; intros. unfold Universe.map, option_map in EQ.
  destruct (tr F _ m a); [|inversion EQ].
  destruct s. inversion EQ. subst. auto.
Qed.

Lemma sig_back_proj S A (P: A -> Prop) def (m: Universe.t S A)
    (ALL: Universe.allP P m):
  Universe.map _ (@proj1_sig _ P) (Universe.map _ (sig_back def) m) = m.
Proof.
  extensionality a. unfold Universe.map, option_map. 
  specialize (ALL a). destruct (m a); auto.
  unfold sig_back. 
  destruct (excluded_middle_informative _); [|exfalso]; auto.
Qed.

Lemma sig_back_commute (F: t) A (P: A -> Prop) def (m: F A)
    (ALL: Universe.allP P (F.(tr) _ m)):
  Universe.map _ (@proj1_sig _ P) (F.(tr) _ (F.(Functor.map) (sig_back def) m)) = F.(tr) _ m.
Proof.
  rewrite (F.(tr).(NatTrans.map_nat)). simpl.
  rewrite sig_back_proj; eauto.
Qed.

Lemma sig_back_all (F: t) A (P: A -> Prop) (Q: sig P -> Prop) def (m: F A)
    (ALLP: Universe.allP P (F.(tr) _ m))
    (ALLQ: Universe.allP (fun a => forall (pf: P a), Q (exist _ _ pf)) (F.(tr) _ m)):
  Universe.allP Q (F.(tr) _ (F.(Functor.map) (sig_back def) m)).
Proof.
  red. intros. specialize (ALLP a). specialize (ALLQ a).
  rewrite (F.(tr).(NatTrans.map_nat)) in EQ.
  destruct x. apply ALLQ.
  simpl in *. unfold Universe.map, option_map in *.
  match goal with [|- ?x = _] => destruct x end; [|inversion EQ].
  unfold sig_back in *. destruct (excluded_middle_informative _).
  - dependent destruction EQ. auto.
  - exfalso. eauto.
Qed.

End SSP.





Section MList.

Variable M: SSP.t.

Variable X: Type.

Inductive MList_ : Type :=
| Mnil_ : MList_
| Mcons_ (hd: M X) (tl: Universe.t (M.(SSP.A)) MList_) : MList_
.

Inductive PMList: MList_ -> Prop :=
| PMnil_ : PMList Mnil_
| PMcons_ hd tl 
    (OnHD: ex (SSP.on_image M tl))
    (OnTL: Universe.allP PMList tl):
  PMList (Mcons_ hd tl)
.
Hint Constructors PMList.

Definition MList := sig PMList.

Definition Mnil : MList := exist _ Mnil_ PMnil_.

Definition Mcons (hd: M X) (tl: M MList) : MList :=
  exist _ (Mcons_ hd (Universe.map _ (@proj1_sig _ _) (M.(SSP.tr) _ tl))) 
          (PMcons_ _ (SSP.sig_on_image _ _ tl) (SSP.sig_all _ _ tl)).

Lemma Mcons_inj h1 t1 h2 t2
    (EQ: Mcons h1 t1 = Mcons h2 t2):
  h1 = h2 /\ t1 = t2.
Proof.
  unfold Mcons in *. dependent destruction EQ.
  split; eauto.
  apply Universe.map_injective in x.
  - apply M.(SSP.inj) in x. auto.
  - intros. destruct x1, x2. simpl in EQ; subst.
    rewrite (proof_irrelevance _ p p0). auto.
Qed.

Lemma MList__ind' l (P: MList_ -> Prop)
    (BASE: P Mnil_)
    (STEP: forall hd tl (IND: Universe.allP P tl), P (Mcons_ hd tl)):
  P l.
Proof.
  revert l. fix 1. intros. destruct l.
  - exact BASE.
  - apply STEP. red; intros.
    destruct (tl a).
    + specialize (MList__ind' m). inversion EQ. 
      subst. apply MList__ind'.
    + inversion EQ.
Qed.

Lemma MList_ind l (P: MList -> Prop)
    (BASE: P Mnil)
    (STEP: forall hd tl (IND: Universe.allP P (M.(SSP.tr) _ tl)), P (Mcons hd tl)):
  P l.
Proof.
  destruct l as [l pf]. revert pf. apply (MList__ind' l); intros.
  - erewrite (proof_irrelevance _ pf). exact BASE.
  - dependent destruction pf. destruct OnHD as [y OnHD]. red in OnHD. subst.

    specialize (STEP hd (M.(Functor.map) (@SSP.sig_back _ PMList (fun _=>Mnil)) y)).
    revert STEP. unfold Mcons, MList.
    match goal with [|- appcontext[exist _ _ ?pf]] => generalize pf end.
    rewrite (SSP.sig_back_commute M (fun _=>Mnil) y); eauto.
    intros. erewrite (proof_irrelevance _ _). apply STEP.

    apply SSP.sig_back_all; auto.
Qed.

Fixpoint len (lenM: M nat -> nat) (l: MList_) : nat :=
  match l with
  | Mnil_ => 0
  | Mcons_ hd tl => 1 + lenM (SSP.back _ 0 (Universe.map _ (len lenM) tl))
  end.

End MList.






Module List_SSP.

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

Program Definition t : SSP.t := 
  @SSP.mk (Functor.mk_data list List.map) (list unit) 
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

End List_SSP.

