Require Import FunctionalExtensionality Program ClassicalEpsilon ProofIrrelevance paco.
Set Implicit Arguments.
Set Automatic Coercions Import.

Definition compose X Y Z (g: Y -> Z) (f: X -> Y) : X -> Z :=
  fun x => g(f x).

Notation "g @@ f" := (@compose _ _ _ g f) (at level 50).

Module Functor.

Structure t := mk
{ F :> Type -> Type
; map : forall X Y (f: X -> Y), F X -> F Y
(* ; lift : forall X (P: X -> Prop), F X -> Prop *)
}.

(*
Structure t_sig (F: t_data) : Prop := mk_sig
{ map_id: forall X, 
    F.(map) (@id X) = @id _
; map_comp: forall X Y Z (g: Y -> Z) (f: X -> Y), 
    (F.(map) g) @@ (F.(map) f) = F.(map) (g @@ f)
}.

Definition t := sig t_sig.

Coercion data (x: t) : t_data := proj1_sig x.
*)

End Functor.

Module NatTrans.

Structure t (F G: Functor.t) := mk
{ N :> forall (X: Type) (x: F X), G X

; map_nat: forall X Y (f: X -> Y) x,
    N Y (F.(Functor.map) f x) = G.(Functor.map) f (N X x)
(* ; lift_nat: forall X (P: X->Prop) (x: F X), *)
(*     F.(Functor.lift) P x <-> G.(Functor.lift) P (N _ x) *)
}.

End NatTrans.

Module Universe.

Definition U (A: Type) (X: Type) := A -> option X.

Definition map A X Y (f: X -> Y) (u: U A X): U A Y :=
  fun a => option_map f (u a).
Arguments map A [X Y] f u.

Definition allP A X (P: X -> Prop) (es: U A X) : Prop :=
  forall a x (EQ: es a = Some x), P x.

Definition t A : Functor.t := Functor.mk (U A) (map A).

Lemma map_id A : forall X x, 
  map A (@id X) x = x.
Proof.
  intros. extensionality a. unfold map. destruct (x a); eauto.
Qed.

Lemma map_comp A : forall X Y Z (g: Y -> Z) (f: X -> Y) x, 
  (map A g) (map A f x) = map A (g @@ f) x.
Proof.
  intros. extensionality a. unfold map. destruct (x a); eauto.
Qed.

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
{ F :> Functor.t
; A : Type
; tr : NatTrans.t F (Universe.t A)
; inh (X: Type) (x: X) : F X

; inj: forall (X: Type) (x y: F X)
         (EQ: tr _ x = tr _ y),
       x = y
}.

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

Definition MList_proj (l: MList) : MList_ := proj1_sig l.

Program Definition Mnil : MList := exist _ Mnil_ _.

Program Definition Mcons (hd: M X) (tl: M MList) : MList :=
  exist _ (Mcons_ hd (Universe.map _ MList_proj (M.(SSP.tr) _ tl))) _.
Next Obligation.
  econstructor 2.
  - eexists (M.(Functor.map) MList_proj tl). red.
    rewrite (M.(SSP.tr).(NatTrans.map_nat)). eauto.
  - red; intros. unfold Universe.map, option_map in EQ.
    destruct (M.(SSP.tr) MList tl); inversion EQ.
    subst. destruct m; eauto.
Qed.

Definition MList_back (l: MList_) : MList :=
  match excluded_middle_informative (PMList l) with
  | left pf => exist _ l pf
  | _ => Mnil
  end.

Lemma MList__ind' l (P: MList_ -> Prop)
    (BASE: P Mnil_)
    (STEP: forall hd tl (IND: Universe.allP P tl), P (Mcons_ hd tl)):
  P l.
Proof.
  revert l. fix 1. intros. destruct l.
  - exact BASE.
  - apply STEP. red; intros.
    destruct (tl a).
    + specialize (MList__ind' m). inversion EQ. subst. apply MList__ind'.
    + inversion EQ.
Qed.

Lemma MList_ind l (P: MList -> Prop)
    (BASE: P Mnil)
    (STEP: forall hd tl (IND: Universe.allP P (M.(SSP.tr) _ tl)), P (Mcons hd tl)):
  P l.
Proof.
  destruct l as [l pf]. revert pf. apply (MList__ind' l); intros.
  - erewrite (proof_irrelevance _ pf). exact BASE.
  - dependent destruction pf. destruct OnHD as [y OnHD]. 
    
    specialize (STEP hd (M.(Functor.map) MList_back y)). 
    unfold Mcons in STEP. revert STEP.
    repeat match goal with [|- appcontext[exist _ _ ?pf]] => generalize pf end.
    rewrite (M.(SSP.tr).(NatTrans.map_nat)). simpl. unfold Universe.map. rewrite <- OnHD.

    replace (fun a => option_map _ (option_map _ (tl a))) with tl; cycle 1.
    { extensionality a. specialize (OnTL a). destruct (tl a); eauto.
      simpl. unfold MList_back. 
      destruct (excluded_middle_informative _); [|exfalso]; eauto. }

    intros. erewrite (proof_irrelevance _ p). apply STEP.
    red. intros. destruct x. eapply (IND a). specialize (OnTL a).
    destruct (tl a); [|inversion EQ].
    simpl in EQ. unfold MList_back in EQ.
    destruct (excluded_middle_informative _).
    + inversion EQ; eauto.
    + exfalso. eauto.
Qed.

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
  @SSP.mk (Functor.mk list List.map) (list unit) 
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

