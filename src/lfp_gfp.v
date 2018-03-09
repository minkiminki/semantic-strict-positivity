Require Import FunctionalExtensionality.
Require Import Program.
Require Import paco.

Set Implicit Arguments.
Set Primitive Projections.

Require Import index wf IFunctor ISPFunctor icoinductive iso
        iinductive icoinductive icombinator1 pafix pacofix.

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

Section SPF_SQUARE.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.

  Definition square : O -> Type := Mu (fun o => Comp F (F o)).

  Definition square_fn1 : forall o, square o -> Mu F o :=
    prim_rec (F:=fun o : O => Comp F (F o)) (Mu F)
             (fun (o : O) (fx : Comp F (F o) (Mu F)) => Con F o (map (Con F) fx)).

  Definition square_fn2 : forall o, Mu F o -> square o :=
    parec_top
      (fun o fx => Con (fun o0 => Comp F (F o0)) _
                       (map (F:=F o) (fun i x => (map (F:= F i) (fun i0 m => snd m)
                                                      (Des (fst x)))) (Des fx))).

  Goal True. apply I. Qed.


  Lemma square_bij2 : forall o (m : Mu (fun o0 => Comp F (F o0)) o),
      square_fn2 (square_fn1 m) = m.
  Proof.
    apply fun_unique with (FIX := Con _).
    - intros o fx.
      unfold square_fn1 at 1. rewrite prim_rec_red. simpl. rewrite MAP_COMPOSE.
      fold square_fn1. unfold square_fn2 at 1.
      rewrite parec_top_red. f_equal.
      fold square_fn2. rewrite MAP_COMPOSE. rewrite eta_expand1.
      rewrite MAP_COMPOSE. simpl. f_equal.
      extensionality i. extensionality x.
      rewrite painup_top_red. simpl. rewrite eta_expand1.
      simpl. fold square_fn1. fold square_fn2.
      rewrite MAP_COMPOSE. rewrite MAP_COMPOSE. simpl.
      reflexivity.
    - intros o fx. f_equal. symmetry. apply MAP_ID.
  Qed.

(*
  Lemma square_bij1 : forall o (m : Mu F o), square_fn1 (square_fn2 m) = m.
  Proof.
    apply mem_induction_principle.
    intros o fx IH.
    

    unfold square_fn2 at 1. rewrite parec_top_red.
    fold square_fn2. rewrite eta_expand1. rewrite MAP_COMPOSE.
    unfold square_fn1 at 1. rewrite prim_rec_red. simpl.
    fold square_fn1. rewrite MAP_COMPOSE. simpl. rewrite MAP_COMPOSE.
    f_equal.

    simpl. pattern fx at 2. rewrite <- (MAP_ID _ fx).

    apply MAP_POINTWISE. intros i x MEM.

    rewrite MAP_COMPOSE. simpl.
      
    pattern x at 1. rewrite <- (eta_expand2 x). rewrite painup_top_red.
    simpl. fold square_fn2. rewrite eta_expand1. rewrite MAP_COMPOSE.
    simpl. specialize (IH _ _ MEM). 


  Lemma square_bij1 : forall o (m : Mu F o), square_fn1 (square_fn2 m) = m.
  Proof.
    apply fun_unique with (FIX := Con _).
    - intros o fx. unfold square_fn2 at 1. rewrite parec_top_red.
      fold square_fn2. rewrite eta_expand1. rewrite MAP_COMPOSE.
      unfold square_fn1 at 1. rewrite prim_rec_red. simpl.
      fold square_fn1. rewrite MAP_COMPOSE. simpl. rewrite MAP_COMPOSE.
      f_equal.

      simpl. 

      f_equal.

      extensionality i. extensionality x. rewrite MAP_COMPOSE. simpl.
      
      pattern x at 1. rewrite <- (eta_expand2 x). rewrite painup_top_red.
      simpl. fold square_fn2. rewrite eta_expand1. rewrite MAP_COMPOSE.
      simpl.


      rewrite parec_top_red. fold square_fn2. rewrite eta_expand1.
      rewrite MAP_COMPOSE. 

    - intros o fx. f_equal. symmetry. apply MAP_ID.


    apply mem_induction_principle.
    intros o1 fx IH.



    unfold square_fn2 at 1. rewrite parec_top_red.
    fold square_fn2. simpl. rewrite eta_expand1. simpl.
    rewrite MAP_COMPOSE. simpl.

unfold square_fn1 at 1. rewrite prim_rec_red.

    repeat rewrite MAP_COMPOSE.
    rewrite eta_expand1. simpl. repeat rewrite MAP_COMPOSE. simpl. 
    f_equal. pattern fx at 2. rewrite <- (MAP_ID _ fx). apply MAP_POINTWISE.

    intros o2 m MEM.

    simpl. rewrite MAP_COMPOSE.
    fold square_fn1. pattern m at 1. rewrite <- (eta_expand2 m).
    rewrite painup_top_red. fold square_fn2. fold square_fn1. rewrite eta_expand1.
    rewrite MAP_COMPOSE. 
    set square_fn2. unfold square_fn2 in s. unfold parec_top in s.

fold square_fn2. 

    apply fun_unique with (FIX := Con _).
    - intros o fx. rewrite <- (eta_expand1 _ _ fx).
      rem
 
apply mem_induction_principle.
      
      intros o fx. unfold square_fn2 at 1. simpl. rewrite parec_top_red. simpl.
      fold square_fn2. unfold square_fn1 at 1. rewrite prim_rec_red.

      simpl. repeat rewrite MAP_COMPOSE.
      rewrite eta_expand1. rewrite MAP_COMPOSE. simpl. 
      f_equal. 

      f_equal.


      extensionality i. extensionality x. fold square_fn1. fold square_fn2.
      rewrite MAP_COMPOSE. 

      pattern x at 1. rewrite <- (eta_expand2 x).
      rewrite painup_top_red. simpl. rewrite eta_expand1. simpl.
      rewrite MAP_COMPOSE. simpl.
      fold square_fn2.



      f_equal. simpl. repeat rewrite MAP_COMPOSE.
      rewrite eta_expand1. rewrite MAP_COMPOSE. simpl. 
      f_equal. extensionality i. extensionality x. fold square_fn1. fold square_fn2.
      rewrite MAP_COMPOSE. 

      pattern x at 1. rewrite <- (eta_expand2 x).
      rewrite painup_top_red. simpl. rewrite eta_expand1. simpl.
      rewrite MAP_COMPOSE. simpl.
      fold square_fn2.

      

rewrite MAP_COMPOSE.
      rewrite painup_top_red.
 fold square_fn2.


admit.
    - intros o fx. f_equal. symmetry. apply MAP_ID. 
    
*)

End SPF_SQUARE.