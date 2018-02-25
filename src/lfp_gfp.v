Require Import FunctionalExtensionality.
Require Import Program.
Require Import paco.

Set Implicit Arguments.
Set Primitive Projections.

Require Import index wf IFunctor ISPFunctor icoinductive iso iinductive icoinductive.

Section LFP_GFP.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.

  Definition Mu2Nu1 : forall o, Mu F o -> Nu F o := prim_rec (F:=F) (Nu F) (cCon F).

  Definition Mu2Nu2 : forall o, Mu F o -> Nu F o := corec F (Mu F) (Des (F:=F)).

  Goal True. apply I. Qed.

  Lemma Mu2Nu_eq1 : forall o (m : Mu F o), Mu2Nu1 m = Mu2Nu2 m.
  Proof.
    apply fun_unique with (FIX := cCon F); intros; unfold Mu2Nu1, Mu2Nu2.
    - apply prim_rec_red.
    - apply cDes_injective. rewrite corec_red.
      rewrite c_eta_expand1. rewrite eta_expand1. reflexivity.
  Qed.

  Lemma Mu2Nu_eq2 : forall o (m : Mu F o), Mu2Nu1 m = Mu2Nu2 m.
  Proof.
    apply cofun_eq_unique with (FIX := Des (F:=F)); intros; unfold Mu2Nu1, Mu2Nu2.
    - rewrite <- (eta_expand2 t). rewrite prim_rec_red.
      rewrite c_eta_expand1. rewrite eta_expand1. reflexivity.
    - apply corec_red.
  Qed.

  Lemma Mu2Nu_inj : forall o (m1 m2 : Mu F o), Mu2Nu1 m1 = Mu2Nu1 m2 -> m1 = m2.
  Proof.
    apply inj_preserve with (FIX := cCon F).
    - apply cCon_injective.
    - apply prim_rec_red.
  Qed.

End LFP_GFP.

Section FP_NAT.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.
  Variable G : O -> (O -> Type) -> Type.

  Context `{H1 : forall c, SPFunctor (F c)}.
  Context `{H2 : forall c, SPFunctor (G c)}.

  Context `{N : forall c, @NatTr _ _ _ (@Fn _ _ (H1 c)) (@Fn _ _ (H2 c))}.

  Definition MuTr : forall o, Mu F o -> Mu G o :=
    prim_rec (F:=F) (Mu G) (fun o (fx : F o (Mu G)) => Con G o (NT (N o) fx)).

  Definition NuTr : forall o, Nu F o -> Nu G o :=
    corec G (Nu F) (fun o (fx : Nu F o) => NT (N o) (cDes fx)).

  Lemma MuTr_ord_preserve : forall o1 (m1 : Mu F o1) o2 (m2 : Mu F o2),
      ord m1 m2 -> ord (MuTr m1) (MuTr m2).
  Proof.
    intros o1 m1 o2 m2 ORD. rewrite <- eta_expand2 in ORD.
    apply ord_correct in ORD. apply MEM_MAP with (f := MuTr) in ORD.
    rewrite <- (eta_expand2 (MuTr m2)). apply ord_correct.
    rewrite <- (eta_expand2 m2). unfold MuTr. rewrite prim_rec_red.
    rewrite eta_expand1. fold MuTr. rewrite <- MEM_COMMUTE.
    apply ORD.
  Qed.

  Lemma MuTr_ord_preserve2 (EMB : forall o, NatEmbed (N o))
    : forall o1 (m1 : Mu F o1) o2 (m2 : Mu F o2),
      ord (MuTr m1) (MuTr m2) -> ord m1 m2.
  Proof.
    intros o1 m1 o2 m2 ORD. rewrite <- eta_expand2.
    apply ord_correct. apply MEM_MAP_INJECTIVE with (f := MuTr).
    - apply inj_preserve with (fun o (fx : F o (Mu G)) => Con G o (NT (N o) fx)).
      + intros o fx1 fx2 EQ. apply Con_injective in EQ.
        apply EMB in EQ. apply EQ.
      + apply prim_rec_red.
    - rewrite <- (eta_expand2 (MuTr m2)) in ORD. apply ord_correct in ORD.
      rewrite <- (eta_expand2 m2) in ORD. unfold MuTr in ORD.
      rewrite prim_rec_red in ORD. rewrite eta_expand1 in ORD.
      fold MuTr in ORD. rewrite <- MEM_COMMUTE in ORD. apply ORD.
  Qed.

End FP_NAT.

Section FP_ISO.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.
  Variable G : O -> (O -> Type) -> Type.

  Context `{H1 : forall c, SPFunctor (F c)}.
  Context `{H2 : forall c, SPFunctor (G c)}.

  Context `{N : forall c, @NatIso _ _ _ (@Fn _ _ (H1 c)) (@Fn _ _ (H2 c))}.

  Lemma MuTr_bij : forall o (m : Mu F o),
      MuTr (N := fun c => @Tr _ _ _ _ _ (@Symmetric_NatIso _ _ _ _ _ (N c)))
           F (MuTr G m) = m.
  Proof.
    apply mem_induction_principle. intros o1 m1 FIX.
    unfold MuTr. rewrite prim_rec_red. rewrite prim_rec_red. fold MuTr.
    f_equal. repeat rewrite MAP_COMMUTE.
    rewrite MAP_COMPOSE. simpl. rewrite BIJECTION1.
    pattern m1 at 2. rewrite <- (MAP_ID _ m1).
    apply MAP_POINTWISE. apply FIX.
  Qed.

  Lemma NuTr_bij : forall o (m : Nu F o),
      bsm (NuTr (N := fun c => @Tr _ _ _ _ _ (@Symmetric_NatIso _ _ _ _ _ (N c)))
           F (NuTr G m)) m.
  Proof.
    pcofix CIH. intros o m. pfold. unfold bsm_gen.
    unfold NuTr. rewrite corec_red. rewrite corec_red.
    repeat rewrite <- MAP_COMMUTE. rewrite MAP_COMPOSE. simpl.
    rewrite BIJECTION1.
    pattern (cDes m) at 2. rewrite <- (MAP_ID _ (cDes m)).
    apply MAP_REL with (f := (fun (i : O) (x : Nu F i) =>
        corec F (Nu G) (fun (o0 : O) (fx : Nu G o0) => NTinv (N o0) (cDes fx)) i
          (corec G (Nu F) (fun (o0 : O) (fx : Nu F o0) => NT Tr (cDes fx)) i x)))
    (g := fun _ => id). 
    apply REL_MONOTONE with (R := fun _ => eq).
    - intros. destruct H. right. apply CIH.
    - apply REL_EQ_EQ. reflexivity.
  Qed.

End FP_ISO.