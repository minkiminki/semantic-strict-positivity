Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.

Arguments proj1_sig {A P} e.
Arguments projT1 {A P} x.

(*
  Functor
 *)

Module PFunctor.

Structure t_data := mk_data
{ Fn :> Type -> Type
; mem : forall X, Fn X -> X -> Type
; eq : forall X (EQ: X -> X -> Prop), Fn X -> Fn X -> Prop
; map : forall X Y (f: X -> Y), Fn X -> Fn Y

; uni : forall X Y (a: Fn X) (ALL: forall x, mem a x -> Y), Fn Y
; uni_correct : forall X Y (a: Fn X) (ALL: forall x, mem a x -> Y)
                       (f: Y -> X) (INV: forall x r, f (ALL x r) = x),
    map f (uni ALL) = a
}.

Structure t_prop (Fn: t_data) : Type := mk_prop
{ map_id: forall X x, 
    Fn.(map) (@id X) x = x
; map_comp: forall X Y Z (g: Y -> Z) (f: X -> Y) x, 
    (Fn.(map) g) ((Fn.(map) f) x) = Fn.(map) (fun y => g (f y)) x
; map_mem: forall X Y (f: X -> Y) (a: Fn X) (x: X),
    Fn.(mem) a x -> Fn.(mem) (Fn.(map) f a) (f x)
}.

Definition t := sigT t_prop.

Coercion data (x: t) : t_data := projT1 x.
Coercion prop (x: t) : t_prop (data x) := projT2 x.

End PFunctor.


Section Id_Functor.

(*
Inductive eqT X : X -> X -> Type :=
| eq_reflT x : eqT x x.

Hint Constructors eqT.
*)

Definition ident_uni X Y (x: X) (ALL: forall y, eq x y -> Y) : Y :=
  (ALL x (eq_refl x)).

Program Definition ident_Fn : PFunctor.t_data :=
  (@PFunctor.mk_data (fun X => X) (fun X => @eq X) (fun X EQ => EQ)
                     (fun X Y (f: X -> Y) x => f x) ident_uni _).

Program Definition id_functor := existT _ ident_Fn (PFunctor.mk_prop _ _ _ _).

End Id_Functor.


Section Comp_Functor.

Variable (F G: PFunctor.t).

Definition comp_map X Y (f: X -> Y) (x: F (G X)) :=
  F.(PFunctor.map) (G.(PFunctor.map) f) x.

Inductive comp_mem X : F (G X) -> X -> Type :=
  | _comp_mem x gx fgx (HG : G.(PFunctor.mem) gx x) (HF : F.(PFunctor.mem) fgx gx) :
    comp_mem fgx x.

Definition comp_eq X (EQ: X -> X -> Prop) : F (G X) -> F (G X) -> Prop
  := F.(PFunctor.eq) (G.(PFunctor.eq) EQ).

Definition comp_uni X Y (x: F (G X)) (ALL: forall y, comp_mem x y -> Y) : F (G Y) :=
  (F.(PFunctor.uni) x (fun y r1 => 
                         (G.(PFunctor.uni) y (fun z r2 =>
                                                ALL _ (_comp_mem _ _ _ r2 r1))))).

Program Definition comp_Fn : PFunctor.t_data :=
  (@PFunctor.mk_data (fun X => F (G X)) comp_mem comp_eq comp_map comp_uni _).
Next Obligation.
Proof.
  unfold comp_map, comp_uni.
  apply F.(PFunctor.uni_correct).
  intros.
  apply G.(PFunctor.uni_correct).
  intros. apply INV.
Defined.

Program Definition comp_functor := existT _ comp_Fn (PFunctor.mk_prop _ _ _ _).
Next Obligation.
Proof.
  unfold comp_map. replace (PFunctor.map G id) with (@id (G X)).
  apply F.(PFunctor.map_id).
  extensionality s. symmetry. apply G.(PFunctor.map_id).
Qed.
Next Obligation.
  unfold comp_map.
  replace (PFunctor.map G (fun y : X => g (f y))) with
      (fun x => PFunctor.map G g (PFunctor.map G f x)).
  apply F.(PFunctor.map_comp).
  extensionality s. apply G.(PFunctor.map_comp).
Qed.
Next Obligation.
  inversion X0. subst.
  econstructor.
  apply G.(PFunctor.map_mem) with (f := f) in HG. apply HG.
  unfold comp_map.
  apply F.(PFunctor.map_mem) with (f := (PFunctor.map G f)) in HF. apply HF.
Qed.

End Comp_Functor.


Module PNatTrans.

Structure t (F G: PFunctor.t_data) := mk
{ Nt :> forall (X: Type) (x: F X), G X

; mem_nat1: forall X x fx,
    F.(PFunctor.mem) fx x -> G.(PFunctor.mem) (Nt X fx) x
; mem_nat2: forall X x fx,
    G.(PFunctor.mem) (Nt X fx) x -> F.(PFunctor.mem) fx x
; map_nat: forall X Y (f: X -> Y) x,
    Nt Y (F.(PFunctor.map) f x) = G.(PFunctor.map) f (Nt X x)
; eq_nat: forall X (EQ: X -> X -> Prop) fx1 fx2,
    F.(PFunctor.eq) EQ fx1 fx2 <-> G.(PFunctor.eq) EQ (Nt X fx1) (Nt X fx2)
(* eq_nat *)
}.

End PNatTrans.


(*
  Strictly Positive Universal Functors

  - A functor (fun X => Sh -> X + nat) for a given shape "Sh"
 *)

Module SPUF.

Definition U (Sh: Type) (Ext: Type) (X: Type) := Sh -> (X + Ext).

Inductive u_mem Sh Ext X : U Sh Ext X -> X -> Type :=
  | _u_mem u s x (EQ: u s = inl x) : u_mem u x.

Definition u_eq Sh Ext X (EQ: X -> X -> Prop) (u1 u2 : U Sh Ext X) : Prop :=
  (forall s e, u1 s = inr e <-> u2 s = inr e) /\
  (forall s x1 x2, u1 s = inl x1 -> u2 s = inl x2 -> EQ x1 x2).
 
Definition map Sh Ext X Y (f: X -> Y) (u: U Sh Ext X) (s : Sh) : Y + Ext :=
  match u s with
  | inl x => inl (f x)
  | inr e => inr e end.

Definition u_uni Sh Ext X Y (u: Sh -> (X + Ext)) (ALL: forall x, u_mem u x -> Y)
  : Sh -> (Y + Ext).
  intro.
  destruct (u X0) eqn : EQ.
  - apply (inl (ALL x (_u_mem _ _ EQ))).
  - apply (inr e).
Defined.

Lemma u_uni_correct Sh Ext X Y (u: Sh -> (X + Ext)) (ALL: forall x, u_mem u x -> Y)
                       (f: Y -> X) (INV: forall x r, f (ALL x r) = x) :
    map f (u_uni ALL) = u.
Admitted.

Definition u_Fn Sh Ext :=
  (@PFunctor.mk_data (fun X => Sh -> (X + Ext)) (@u_mem Sh Ext) (@u_eq Sh Ext)
                     (@map Sh Ext) (@u_uni Sh Ext) (@u_uni_correct Sh Ext)).

Lemma map_id Sh Ext : forall X (x: Sh -> X + Ext), 
  map (@id X) x = x.
Proof.
  intros. extensionality s. 
  unfold map. destruct (x s); eauto.
Qed.

Lemma map_comp Sh Ext : forall X Y Z (g: Y -> Z) (f: X -> Y) (x: Sh -> X + Ext), 
  (map g) ((map f) x) = map (fun y => g (f y)) x.
Proof.
  intros. extensionality s. 
  unfold map. destruct (x s); eauto.
Qed.

Lemma map_mem Sh Ext : forall X Y (f: X -> Y) (u: Sh -> X + Ext) (x: X),
    u_mem u x -> u_mem (map f u) (f x).
Proof.
  intros.
  inversion X0. subst.
  apply (_u_mem _ s). unfold map.
  rewrite EQ. auto.
Qed.

Definition t Sh Ext : PFunctor.t := 
  existT _ _ (PFunctor.mk_prop (u_Fn Sh Ext) (@map_id Sh Ext) (@map_comp Sh Ext)
                              (@map_mem Sh Ext)).

Lemma map_injective Sh Ext X Y (u1 u2: Sh -> X + Ext) (f: X -> Y)
    (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
    (EQ: map f u1 = map f u2):
  u1 = u2.
Proof.
  extensionality s. apply equal_f with (x:=s) in EQ.  unfold map in EQ. 
  destruct (u1 s), (u2 s); inversion EQ; subst; eauto.
  apply INJ in H0. subst; auto.
Qed.

Lemma map_pointwise Sh Ext X Y (u: Sh -> X + Ext) (f g: X -> Y)
    (ALL: forall x, u_mem u x -> f x = g x):
  map f u = map g u.
Proof.
  extensionality s. unfold map.
  destruct (u s) eqn : EQ; auto.
  specialize (ALL x). f_equal. apply ALL.
  econstructor. apply EQ.
Qed.

Lemma eq_symmetric Sh Ext X (EQ: X -> X -> Prop)
      (SY: forall x1 x2, EQ x1 x2 -> EQ x2 x1) (u1 u2: Sh -> X + Ext)
  : u_eq EQ u1 u2 -> u_eq EQ u2 u1.
Proof.
  intros. unfold u_eq in *. split; intros.
  - split; intros; apply H in H0; auto.
  - apply SY. destruct H. apply (H2 _ _ _ H1 H0).
Qed.

Lemma eq_reflexive Sh Ext X (EQ: X -> X -> Prop) (RE: forall x, EQ x x) 
      (u: Sh -> X + Ext) : u_eq EQ u u.
Proof.
  split; intros.
  - tauto.
  - rewrite H in H0. inversion H0. apply RE.
Qed.

Lemma eq_transitive Sh Ext X (EQ: X -> X -> Prop)
      (TR: forall x1 x2 x3, EQ x1 x2 -> EQ x2 x3 -> EQ x1 x3)
      (u1 u2 u3: Sh -> X + Ext) : u_eq EQ u1 u2 -> u_eq EQ u2 u3 -> u_eq EQ u1 u3.
Proof.
  intros. unfold u_eq in *. split; intros.
  - split; intros.
    + apply H in H1. apply H0 in H1. auto.
    + apply H0 in H1. apply H in H1. auto.
  - destruct H, H0. destruct (u2 s) eqn : US.
    + specialize (H3 _ _ _ H1 US). specialize (H4 _ _ _ US H2).
      apply (TR _ _ _ H3 H4).
    + apply H in US. rewrite US in H1. inversion H1.
Qed.

Lemma eq_identity Sh Ext X (EQ: X -> X -> Prop) (ID: forall x1 x2, EQ x1 x2 -> x1=x2)
      (u1 u2: Sh -> X + Ext) : u_eq EQ u1 u2 -> u1 = u2.
Proof.
  intros. destruct H. extensionality s.
  destruct (u1 s) eqn : EQ1; destruct (u2 s) eqn : EQ2.
  - f_equal. apply ID.
    apply (H0 _ _ _ EQ1 EQ2).
  - apply H in EQ2. rewrite EQ1 in EQ2. inversion EQ2.
  - apply H in EQ1. rewrite EQ1 in EQ2. inversion EQ2.
  - apply H in EQ2. rewrite EQ1 in EQ2. inversion EQ2. auto.
Qed.
 
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

; mem_nat1: forall X x fx,
    Fn.(PFunctor.mem) fx x -> SPUF.u_mem (emb X fx) x
; mem_nat2: forall X x fx,
    SPUF.u_mem (emb X fx) x -> Fn.(PFunctor.mem) fx x
; map_nat: forall X Y (f: X -> Y) x s,
    emb Y (Fn.(PFunctor.map) f x) s = SPUF.map f (emb X x) s
; eq_nat: forall X (EQ: X -> X -> Prop) fx1 fx2,
    Fn.(PFunctor.eq) EQ fx1 fx2 <-> SPUF.u_eq EQ (emb X fx1) (emb X fx2)

; inj: forall (X: Type) (m n: Fn X)
         (EQ: emb _ m = emb _ n),
       m = n
}.

Lemma map_injective (M: SSPF.t) X Y (f: X -> Y) m1 m2
    (INJ: forall x1 x2 (EQ: f x1 = f x2), x1 = x2)
    (EQ: M.(PFunctor.map) f m1 = M.(PFunctor.map) f m2):
  m1 = m2.
Proof.
  apply inj. apply (SPUF.map_injective INJ).
  extensionality s.
  repeat rewrite <- M.(map_nat).
  f_equal. apply EQ.
Qed.

Lemma map_pointwise (M: SSPF.t) X Y (f g: X -> Y) m
    (ALL: forall x, M.(PFunctor.mem) m x -> f x = g x):
  M.(PFunctor.map) f m = M.(PFunctor.map) g m.
Proof.
  apply inj. extensionality s. repeat rewrite M.(map_nat).
  apply equal_f. apply SPUF.map_pointwise.
  intros.
  apply ALL, mem_nat2, X0.
Qed.

Lemma eq_symmetric (M: SSPF.t) X (EQ: X -> X -> Prop)
      (SY: forall x1 x2, EQ x1 x2 -> EQ x2 x1) (u1 u2: M X)
  : M.(PFunctor.eq) EQ u1 u2 -> M.(PFunctor.eq) EQ u2 u1.
Proof.
  intros. rewrite eq_nat in *.
  revert H. apply SPUF.eq_symmetric. apply SY.
Qed.

Lemma eq_reflexive (M: SSPF.t) X (EQ: X -> X -> Prop) (RE: forall x, EQ x x) 
      (u: M X) : M.(PFunctor.eq) EQ u u.
Proof.
  apply eq_nat. apply SPUF.eq_reflexive. apply RE.
Qed.

Lemma eq_transitive (M: SSPF.t) X (EQ: X -> X -> Prop)
      (TR: forall x1 x2 x3, EQ x1 x2 -> EQ x2 x3 -> EQ x1 x3)
      (u1 u2 u3: M X) : M.(PFunctor.eq) EQ u1 u2 -> M.(PFunctor.eq) EQ u2 u3 -> M.(PFunctor.eq) EQ u1 u3.
Proof.
  intros. rewrite eq_nat in *.
  apply (SPUF.eq_transitive TR H H0).
Qed.

Lemma eq_identity (M: SSPF.t) X (EQ: X -> X -> Prop) (ID: forall x1 x2, EQ x1 x2 -> x1=x2)
      (u1 u2: M X) : M.(PFunctor.eq) EQ u1 u2 -> u1 = u2.
Proof.
  intros. apply eq_nat in H.
  apply (SPUF.eq_identity ID) in H.
  apply inj in H. auto.
Qed.

Lemma functor_prop (M: t) : PFunctor.t_prop M.
Proof.
  split; intros.
  - apply M.(inj). extensionality s.
    rewrite map_nat. rewrite SPUF.map_id. auto.
  - apply M.(inj). extensionality s.
    repeat rewrite map_nat. 
    unfold SPUF.map. rewrite map_nat. unfold SPUF.map.
    destruct (emb M X x s); auto.
  - apply mem_nat1 in X0. apply mem_nat2.
    inversion X0. subst.
    apply (SPUF._u_mem _ s).
    rewrite map_nat. unfold SPUF.map.
    rewrite EQ. auto.
Qed.    

Coercion to_functor (M: t) : PFunctor.t := existT _ _ (functor_prop M).

Program Definition to_nat_trans (M: t) : PNatTrans.t M (SPUF.t M.(Sh) M.(Ext))
                                                  := PNatTrans.mk _ _ M.(emb) _ _ _ _.
Next Obligation.
Proof.
  apply (M.(mem_nat1) _ _ X0).
Qed.
Next Obligation.
Proof.
  apply (M.(mem_nat2) _ X0).
Qed.
Next Obligation.
Proof.
  extensionality s. apply map_nat.
Qed.
Next Obligation.
Proof.
  apply SSPF.eq_nat.
Qed.

End SSPF.
