Require Import FunctionalExtensionality ProofIrrelevance ClassicalDescription.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Logic.Eqdep_dec.
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
; map : forall X Y (f: X -> Y), Fn X -> Fn Y
; rel : forall X, X -> Fn X -> Prop
}.

Structure t_prop (Fn: t_data) : Prop := mk_prop
{ map_id: forall X x, 
    Fn.(map) (@id X) x = x
; map_comp: forall X Y Z (g: Y -> Z) (f: X -> Y) x, 
    (Fn.(map) g) ((Fn.(map) f) x) = Fn.(map) (fun y => g (f y)) x
}.

Definition id_data := mk_data (fun X => X) (fun X Y f => f) (fun _ => eq).

Lemma id_prop : t_prop id_data.
Proof.
  apply mk_prop; eauto.
Qed.

Definition t := sig t_prop.

Coercion data (x: t) : t_data := proj1_sig x.
Coercion prop (x: t) : t_prop (data x) := proj2_sig x.

Definition id_functor : t := exist _ _ id_prop.

Inductive comp_rel (F G: t_data) X : X -> F (G X) -> Prop :=
| _comp_rel x gx fgx (HG : G.(rel) x gx) (HF : F.(rel) gx fgx) : comp_rel F G x fgx.

Definition functor_comp_data (F G : t_data) := 
  mk_data (fun X => F (G X)) (fun X Y (f: X -> Y) => F.(map) (G.(map) f))
          (comp_rel F G).

Lemma functor_comp_prop (F G : t) : t_prop (functor_comp_data F G).
Proof.
  apply mk_prop; intros; simpl.
  - rewrite <- (map_id F).
    f_equal. extensionality y. apply (map_id G).
  - rewrite (map_comp F).
    f_equal. extensionality y. apply (map_comp G).
Qed.

Definition functor_comp (F G : t) : t :=
  exist _ _ (functor_comp_prop F G).

Definition pullback P A B C (pa: P -> A) (f: A -> C) (g: B -> C) :=
           (forall a b (EQ: f a = g b), exists p, a = pa p).

End PFunctor.

(*
  Natural Transformation
 *)

Module PNatTrans.

Structure t (F G: PFunctor.t_data) := mk
{ Nt :> forall (X: Type) (x: F X), G X

; map_nat: forall X Y (f: X -> Y) x,
    Nt Y (F.(PFunctor.map) f x) = G.(PFunctor.map) f (Nt X x)
; rel_nat: forall X x fx,
    F.(PFunctor.rel) x fx <-> G.(PFunctor.rel) x (Nt X fx)
}.

End PNatTrans.

(*
  Strictly Positive Universal Functors

  - A functor (fun X => Sh -> X + nat) for a given shape "Sh"
 *)

Module SPUF.

Definition U (Sh: Type) (Ext: Type) (X: Type) := Sh -> (X + Ext).

Definition map Sh Ext X Y (f: X -> Y) (u: U Sh Ext X): U Sh Ext Y :=
  fun a => match u a with inl x => inl (f x) | inr b => inr b end.
Arguments map Sh Ext [X Y] f u.

Definition allP Sh Ext X (P: X -> Prop) (u: U Sh Ext X) : Prop :=
  forall a x (EQ: u a = inl x), P x.

Lemma map_id Sh Ext : forall X x, 
  map Sh Ext (@id X) x = x.
Proof.
  intros. extensionality s. 
  unfold map. unfold id. destruct (x s); eauto.
Qed.

Lemma map_comp Sh Ext : forall X Y Z (g: Y -> Z) (f: X -> Y) x, 
  (map Sh Ext g) ((map Sh Ext f) x) = map Sh Ext (fun y => g (f y)) x.
Proof.
  intros. extensionality s. 
  unfold map, compose. destruct (x s); eauto.
Qed.

Inductive u_rel Sh Ext X : X -> U Sh Ext X -> Prop :=
| _u_rel u s x (EQ: u s = inl x) : u_rel x u.

Definition t Sh Ext : PFunctor.t := 
  exist _ _
        (PFunctor.mk_prop (PFunctor.mk_data (U Sh Ext) (map Sh Ext) (@u_rel Sh Ext))
                          (@map_id Sh Ext) (@map_comp Sh Ext)).

Lemma map_injective Sh Ext X Y u1 u2 (f: X -> Y)
    (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
    (EQ: map Sh Ext f u1 = map Sh Ext f u2):
  u1 = u2.
Proof.
  extensionality s. apply equal_f with (x:=s) in EQ.  unfold map in EQ. 
  destruct (u1 s), (u2 s); inversion EQ; subst; eauto.
  apply INJ in H0. subst; auto.
Qed.

Lemma u_rel_map Sh Ext X Y x u (f: X -> Y) (ORD: u_rel x u) :
  u_rel (f x) (SPUF.map Sh Ext f u).
Proof.
  inversion ORD. subst.
  apply (_u_rel _ s). unfold map.
  rewrite EQ. auto.
Qed.

(*
Lemma pmap_law1 Sh Ext X u (P: X -> Prop) (PT: forall x, P x):
  @pmap Sh Ext X P u.
Proof.
  unfold pmap.
  intros.
  apply PT.
Qed.

Lemma pmap_law2 Sh Ext X (u: Sh -> X+Ext) (P1 P2: X -> Prop)
      (PU1: pmap P1 u) (PU2: pmap P2 u):
  pmap (fun x => P1 x /\ P2 x) u.
Proof.
  unfold pmap in *. intros. split.
  apply PU1 with s, EQ.
  apply PU2 with s, EQ.
Qed.

Lemma pmap_law3 Sh Ext X (u: Sh -> X+Ext) (P1 P2: X -> Prop)
      (PU1: pmap P1 u) (PI: forall x, P1 x -> P2 x):
  pmap P2 u.
Proof.
  unfold pmap in *. intros.
  apply PI. apply (PU1 _ _ EQ). 
Qed.

Lemma pmap_law4 Sh Ext X Y (u: Sh -> X+Ext) P1 (P2: Y -> Prop) (f: X -> Y)
      (PU1: pmap P1 u) (PI: forall x, P1 x -> P2 (f x)):
  pmap P2 (map Sh Ext f u).
Proof.
  unfold pmap, map. intros.
  unfold pmap in PU1. specialize (PU1 s).
  destruct (u s); inversion EQ.
  subst. apply PI. eapply PU1. auto.
Qed.  
*)

Lemma preserve_pullback Sh Ext P A B C pa f g
      (PULL: @PFunctor.pullback P A B C pa f g) :
  PFunctor.pullback (map Sh Ext pa) (map Sh Ext f) (map Sh Ext g).
Proof.
  unfold PFunctor.pullback in *. intros.
  unfold map in EQ.
  assert (H1 : forall (a0 : Sh),  exists (p : sum P Ext),
               (match p with 
                | inr b => a a0 = inr b
                | inl x => a a0 = inl (pa x) end)). 
  { intros.
    apply equal_f with a0 in EQ.
    destruct (a a0); destruct (b a0); inversion EQ.
    - apply PULL in H0. destruct H0.
      exists (inl x). subst. eauto.
    - exists (inr e). subst. eauto.
  }
  apply choice in H1. destruct H1.
  exists x. unfold map. simpl. extensionality s.
  specialize (H s). destruct (x s); [destruct H|];
  symmetry; eauto.
Qed.


Lemma map_pointwise Sh Ext X Y u (f g: X -> Y)
    (ALL: allP (fun x => f x = g x) u):
  map Sh Ext f u = map Sh Ext g u.
Proof.
  extensionality s. specialize (ALL s). unfold map. 
  destruct (u s); eauto.
  simpl. rewrite ALL; eauto.
Qed.


Definition pmap Sh Ext X (P: X -> Prop) (u: U Sh Ext X) : Prop :=
  forall (x: X), u_rel x u -> P x.

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
; emb: PNatTrans.t Fn (SPUF.t Sh Ext)

; uni: forall (m: Fn unit) 
         (CONST: forall s x, ~ emb _ m s = inl x),
       exists m': Fn False, m = Fn.(PFunctor.map) (fun _ => ())  m'

; inj: forall (X: Type) (m n: Fn X)
         (EQ: emb _ m = emb _ n),
       m = n
}.

Lemma functor_prop (M: t) : PFunctor.t_prop M.
Proof.
  split.
  - intros. apply M.(inj). unfold id. 
    rewrite M.(emb).(PNatTrans.map_nat).
    rewrite (SPUF.t _ _).(PFunctor.map_id). auto.
  - intros. apply M.(inj). unfold compose.
    repeat rewrite M.(emb).(PNatTrans.map_nat).
    rewrite (SPUF.t _ _).(PFunctor.map_comp). auto.
Qed.

Coercion to_functor (M: t) : PFunctor.t := exist _ _ (functor_prop M).

(*
Inductive on_image' (M: t) X : SPUF.t _ _ X -> M X -> Type :=
| _on_image' x : on_image' M (M.(emb) _ x) x.

Inductive sig' (A: Type) (P: A -> Type) : Type :=
| exist' : forall x : A, P x -> sig' P.

Definition proj1_sig' A (P: A -> Type) (x: sig' P) : A :=
match x with
| exist' _ a _ => a end.

Inductive ex' (A : Type) (P : A -> Type) : Type :=
| ex_intro' : forall x : A, P x -> ex' P.

Lemma sig_on_image' (M: t) A (P: A -> Type) (m: M (sig' P)):
  ex' (SSPF.on_image' M (@SPUF.map M.(Sh) M.(Ext) (sig' P) A (@proj1_sig' A P) (M.(emb) _ m))).
Proof.
  eexists (M.(PFunctor.map) (@proj1_sig' A P) m).
  replace (SPUF.map (Sh M) (Ext M) (proj1_sig' (P:=P)) ((emb M) (sig' P) m))
          with (M.(emb) _  (PFunctor.map M (proj1_sig' (P:=P)) m)).
  constructor.
  rewrite (M.(emb).(PNatTrans.map_nat)). auto.
Defined.

Lemma sig_all' (M: t) A (P: A -> Type) (m: M (sig' P)):
  forall x, SPUF.u_rel x (@SPUF.map _ _ (sig' P) A (@proj1_sig' A P) (M.(emb) _ m))
                  -> P x.
Proof.
  intros. simpl in H. 



  red; intros. inversion H. unfold SPUF.map in EQ.
  destruct (emb M _ m s); [|inversion EQ].
  destruct s0. inversion EQ. subst. auto.
Qed.



Lemma sig_all (M: t) A (P: A -> Prop) (m: M (sig P)):
  SPUF.pmap P (@SPUF.map _ _ (sig P) A proj1_sig (M.(emb) _ m)).
Proof.
  red; intros. inversion H. unfold SPUF.map in EQ.
  destruct (emb M _ m s); [|inversion EQ].
  destruct s0. inversion EQ. subst. auto.
Qed.
*)

Definition on_image (M: t) X (u: SPUF.t _ _ X) (x: M X) : Prop := 
  u = M.(emb) _ x.
Hint Unfold on_image.

Definition back_opt (M: t) (X: Type) (u: SPUF.t _ _ X) : option (M X) :=
  match excluded_middle_informative (ex (unique (on_image M u))) with
  | left pf => Some (proj1_sig (constructive_definite_description _ pf))
  | _ => None
  end.

Definition back (M: t) (X: Type) (x : M X) (u: SPUF.t _ _ X) : M X :=
  match back_opt M u with None => x | Some e => e end.

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
 
Definition sig_back A (P: A -> Prop) (inh: A -> sig P) (a: A) : sig P :=
  match excluded_middle_informative (P a) with
  | left pf => exist _ a pf
  | _ => inh a
  end.

Lemma sig_on_image (M: t) A (P: A -> Prop) (m: M (sig P)):
  ex (unique (SSPF.on_image M (SPUF.map _ _ proj1_sig (M.(emb) _ m)))).
Proof.
  eexists (M.(PFunctor.map) proj1_sig m). split.
  - red. rewrite (M.(emb).(PNatTrans.map_nat)). eauto.  
  - intros. red in H. apply M.(SSPF.inj).
    rewrite <- H. rewrite M.(emb).(PNatTrans.map_nat). auto.
Qed.

Lemma sig_all (M: t) A (P: A -> Prop) (m: M (sig P)):
  SPUF.pmap P (@SPUF.map _ _ (sig P) A proj1_sig (M.(emb) _ m)).
Proof.
  red; intros. inversion H. unfold SPUF.map in EQ.
  destruct (emb M _ m s); [|inversion EQ].
  destruct s0. inversion EQ. subst. auto.
Qed.

Lemma sig_all2 (M: t) A (P: A -> Prop) (Q: sig P -> Prop) (m: M (sig P))
    (ALLQ: @SPUF.pmap _ _ A (fun a => forall (pf: P a), Q (exist _ _ pf)) 
                     (M.(emb) _ (M.(PFunctor.map) proj1_sig m))):
  @SPUF.pmap _ _ (sig P) Q (M.(emb) _ m).
Proof.
  red. intros.
  destruct x.
  unfold SPUF.pmap in ALLQ. specialize (ALLQ x).
  apply ALLQ.
  rewrite M.(emb).(PNatTrans.map_nat).
  simpl.
  unfold SPUF.map.
  simpl.
  inversion H.
  subst.
  apply (SPUF._u_rel _ s).
  destruct ((emb M) {x : A | P x} m); inversion EQ.
  auto.
Qed.

Lemma sig_back_proj (M: t) A (P: A -> Prop) (inh: A -> sig P) (m: SPUF.t M.(Sh) M.(Ext) A)
    (ALL: @SPUF.pmap _ _ A P m):
  SPUF.map _ _ proj1_sig (SPUF.map _ _ (sig_back inh) m) = m.
Proof.
  extensionality s. unfold SPUF.map. unfold SPUF.pmap in ALL.
  destruct (m s) eqn : H; auto.
  unfold sig_back.
  destruct (excluded_middle_informative _); [|exfalso]; auto.
  apply n, ALL.
  apply (SPUF._u_rel _ s). auto.
Qed.

Lemma allP_project (M: t) A (P: A -> Prop) (m: M A)
    (ALLP: @SPUF.pmap _ _ A P (M.(emb) _ m)):
  exists (m': M (sig P)), m = M.(PFunctor.map) proj1_sig m'.
Proof.
  destruct (excluded_middle_informative (exists a, P a)) as [EXa|NEXa].
  - destruct EXa as [a Pa]. 
    exists (M.(PFunctor.map) (sig_back (fun _ => exist P _ Pa)) m).
    apply M.(inj).
    rewrite !M.(emb).(PNatTrans.map_nat).
    symmetry. apply sig_back_proj; eauto.
  - destruct (M.(uni) (M.(PFunctor.map) (fun _ => ()) m)) as [m' EQm].
    + intros. unfold SPUF.pmap in ALLP. 
      rewrite M.(emb).(PNatTrans.map_nat).
      simpl in *. unfold SPUF.map in *.
      destruct (emb M A m s) eqn: EQ.
      * exfalso. apply NEXa. exists a. apply ALLP.
        apply (SPUF._u_rel _ s). auto.
      * setoid_rewrite EQ. intro FF; inversion FF. 
    + exists (M.(PFunctor.map) (False_rect _) m').
      apply M.(inj).
      assert (INJ: forall n 
                     (EQ: @SPUF.map _ _ A unit (fun _ => ()) (M.(emb) A m) = SPUF.map _ _ (fun _ => ()) n), 
                   M.(emb) A m = n).
      { intros. extensionality s.
        assert (EQf:= equal_f EQ s). unfold SPUF.map in EQf.
        destruct (M.(emb) A m s) eqn: EQ'.
        - exfalso. apply NEXa. exists a. apply ALLP. apply (SPUF._u_rel _ s EQ').
        - destruct (n s); inversion EQf; subst; eauto.
      }
      apply INJ. 
      repeat setoid_rewrite <- (M.(emb).(PNatTrans.map_nat)).
      rewrite EQm. 
      repeat rewrite M.(PFunctor.map_comp). auto.
Qed.

Lemma map_pointwise (M: t) X Y m (f g: X -> Y)
    (ALL: forall x, M.(PFunctor.rel) x m -> f x = g x):
  M.(PFunctor.map) f m = M.(PFunctor.map) g m.
Proof.
  apply inj.
  repeat rewrite PNatTrans.map_nat.
  apply SPUF.map_pointwise.
  unfold SPUF.allP.
  intros.
  apply ALL.
  apply (PNatTrans.rel_nat M.(emb)).
  apply (SPUF._u_rel _ a EQ).
Qed.

Lemma map_injective (M: SSPF.t) X Y (f: X -> Y) m1 m2
    (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
    (EQ: M.(PFunctor.map) f m1 = M.(PFunctor.map) f m2):
  m1 = m2.
Proof.
  apply inj.
  apply (SPUF.map_injective INJ).
  repeat setoid_rewrite <- (PNatTrans.map_nat M.(emb)).
  f_equal. apply EQ.
Qed.

Lemma reverse_function A B (d: A) (f: A -> B): exists g, forall x, f (g (f x)) = f x.
Proof.
  assert (H : forall b, exists a, 
               match excluded_middle_informative (exists a', f a' = b) with
               | left pf => f a = b
               | _ => a = d end).
  { intros.
    destruct (excluded_middle_informative (exists a' : A, f a' = b)).
    destruct e. exists x. apply H.
    exists d. auto.
  }
  apply choice in H. destruct H. exists x.
  intros.
  specialize (H (f x0)). 
  destruct (excluded_middle_informative (exists a' : A, f a' = f x0)).
  apply H.
  exfalso. apply n. eauto.  
Qed.

Lemma embedded_pullback (M: SSPF.t) A B (f: A -> B) :
  PFunctor.pullback (M.(PFunctor.map) f) (M.(emb) B) (SPUF.map M.(Sh) M.(Ext) f).
Proof.
  unfold PFunctor.pullback. intros.
  destruct (excluded_middle_informative (exists a: A, True)).
  - destruct e. clear H.
    assert (H := reverse_function x f). destruct H as [g].
    exists (PFunctor.map M g a).
    apply inj.
    repeat rewrite PNatTrans.map_nat. rewrite EQ.
    replace (SPUF.map (Sh M) (Ext M)) with (PFunctor.map (SPUF.t (Sh M) (Ext M))).
    repeat rewrite (PFunctor.map_comp (SPUF.t M.(Sh) M.(Ext))).
    f_equal. extensionality s. symmetry. apply H. eauto.
  - destruct (M.(uni) (M.(PFunctor.map) (fun _ => ()) a)) as [m' EQm].
    + intros.
      rewrite PNatTrans.map_nat.
      simpl. unfold SPUF.map in *.
      apply equal_f with s in EQ.
      destruct ((emb M) B a). destruct x.
      destruct (b s).
      exfalso. apply n. exists a0. apply I.
      inversion EQ.
      intro. inversion H.
    + exists (M.(PFunctor.map) (False_rect _) m').
      apply inj.
       assert (INJ: forall n 
                     (EQ: @SPUF.map _ _ B unit (fun _ => ()) (M.(emb) B a) = SPUF.map _ _ (fun _ => ()) n), 
                   M.(emb) B a = n).
      { intros. extensionality s.
        assert (EQf:= equal_f EQ s). unfold SPUF.map in EQf.
        apply equal_f with s in EQ0. unfold SPUF.map in EQ0.
        destruct ((emb M) B a s); destruct (b s); inversion EQf.
        - exfalso. apply n. eauto.
        - destruct (n0 s); inversion EQ0. subst. auto.
      }

      apply INJ. 
      repeat setoid_rewrite <- (M.(emb).(PNatTrans.map_nat)).
      rewrite EQm. 
      repeat rewrite M.(PFunctor.map_comp). auto.
Qed.

Lemma preserve_pullback (M: SSPF.t) P A B C pa f g
      (PULL: @PFunctor.pullback P A B C pa f g) :
  PFunctor.pullback (M.(PFunctor.map) pa) (M.(PFunctor.map) f) (M.(PFunctor.map) g).
Proof.
  unfold PFunctor.pullback in *. intros.
  apply (f_equal (M.(emb) C)) in EQ.
  repeat rewrite PNatTrans.map_nat in EQ.
  apply (SPUF.preserve_pullback PULL) in EQ.
  destruct EQ.
  apply (embedded_pullback M a H).
Qed.

Inductive dep_sum A (B: A -> t) (C: t -> Type) :=
  | dep (a: A) (c: C (B a)) : dep_sum B C.

End SSPF.
