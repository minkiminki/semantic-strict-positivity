Require Import FunctionalExtensionality.
Require Import Program.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.

Require Import index wf Functor SPFunctor pullback_sfunctor.

Section INDUCTIVE.

  Variable F : Type -> Type.
  Context `{H : SPFunctor F}.
  
  Inductive Mu : Type :=
  | Con' : Container (@degree _ H) Mu -> Mu.

  Definition Con (fx : F Mu) : Mu := Con' (NT _ fx).

  Definition Des' (m : Mu) : Container (@degree _ H) Mu :=
    match m with
    | Con' s => s end.

  Definition Des (m : Mu) : F Mu := NTinv _ (Des' m).

  Lemma eta_expand2 : forall (x : Mu), Con (Des x) = x.
  Proof.
    intros. unfold Des, Con. rewrite BIJECTION2.
    destruct x. reflexivity.
  Qed.

  Lemma eta_expand1 : forall (x : F Mu), Des (Con x) = x.
  Proof.
    intros. unfold Des, Con.
    rewrite <- BIJECTION1.
    destruct (NT Mu x). reflexivity.
  Qed.

  Definition ord : Mu -> Mu -> Prop :=
   fun m1 m2 => mem (Des' m2) m1.

  Lemma ord_wf : well_founded ord.
  Proof.
    unfold well_founded. fix 1.
    intro m2. constructor.
    intros m1 ORD. destruct ORD.
    rewrite <- H0. apply ord_wf.
  Qed.

  Definition ord_c := clos_trans_n1 _ ord.

  Lemma ord_correct : forall (m : Mu) (fx : F Mu),
      @mem F _ Mu fx m <-> ord m (Con fx).
  Proof.
    intros. rewrite MEM_COMMUTE. reflexivity.
  Qed.

  Lemma acc_clos_trans A (R : A -> A -> Prop) :
    forall a, Acc R a -> Acc (clos_trans_n1 _ R) a.
  Proof.
    apply Acc_ind. intros a BASE STEP.
    constructor. intros a' REL. destruct REL as [a REL | a1 a2 REL1 REL2].
    - apply STEP. apply REL.
    - apply (Acc_inv (STEP _ REL1) REL2).
  Qed.

  Lemma wf_clos_trans A (R : A -> A -> Prop) :
    well_founded R -> well_founded (clos_trans_n1 _ R).
  Proof.
    intros W a. apply acc_clos_trans, W.
  Qed.
  
  Lemma ord_c_wf : well_founded ord_c.
  Proof.
    apply wf_clos_trans. apply ord_wf.
  Qed.

  Lemma clos_trans_n1_transitive A (R : A -> A -> Prop) :
    forall x y z, clos_trans_n1 _ R x y -> clos_trans_n1 _ R y z ->
                  clos_trans_n1 _ R x z.
  Proof.
    intros x y z REL1 REL2.
    apply Operators_Properties.clos_trans_tn1_iff.
    apply Operators_Properties.clos_trans_tn1_iff in REL1.
    apply Operators_Properties.clos_trans_tn1_iff in REL2.
    apply (t_trans _ _ _ _ _ REL1 REL2).
  Qed.

  Lemma ord_transitive (x y z : Mu) :
    ord_c x y -> ord_c y z -> ord_c x z.
  Proof.
    apply clos_trans_n1_transitive.
  Qed.

  Definition rec (P : Mu -> Type)
             (FIX : forall (m1 : Mu), 
                 (forall (m2 : Mu), ord_c m2 m1 -> P m2) -> P m1) :
    forall (m : Mu), P m :=
    Fix ord_c_wf P FIX.

  Definition rec_simpl (P : Type)
             (FIX : forall (m1 : Mu), 
                 (forall (m2 : Mu), ord_c m2 m1 -> P) -> P) :
    Mu -> P :=
    rec _ FIX.

  Lemma rec_red (P : Mu -> Type)
        (FIX : forall (m1 : Mu), 
            (forall (m2 : Mu), ord_c m2 m1 -> P m2) -> P m1)
        (fx : F Mu) :
    rec P FIX (Con fx) = FIX (Con fx) (fun fy _ => rec P FIX fy).
  Proof.
    apply Init.Wf.Fix_eq.
    intros x f g EXT. f_equal.
    extensionality y. extensionality p. apply EXT.
  Qed.

  Lemma rec_simpl_red (P : Type)
        (FIX : forall (m1 : Mu), 
            (forall (m2 : Mu), ord_c m2 m1 -> P) -> P) 
        (fx : F Mu) :
    rec_simpl FIX (Con fx) = FIX (Con fx) (fun fy _ => rec_simpl FIX fy).
  Proof.
    apply (rec_red _ FIX fx).
  Qed.

  Definition induction_principle (P : Mu -> Prop)
             (FIX : forall (m1 : Mu), 
                 (forall (m2 : Mu), ord m2 m1 -> P m2) -> P m1) :
    forall (m : Mu), P m.
  Proof.
    apply (Fix ord_wf P FIX).
  Qed.

  Definition str_induction_principle (P : Mu -> Prop)
             (FIX : forall (m1 : Mu), 
                 (forall (m2 : Mu), ord_c m2 m1 -> P m2) -> P m1) :
    forall (m : Mu), P m.
  Proof.
    apply (Fix ord_c_wf P FIX).
  Qed.

  Definition mem_induction_principle (P : Mu -> Prop)
             (FIX : forall (fx : F Mu), 
                 (forall (m : Mu), mem fx m -> P m) -> P (Con fx)) :
    forall (m : Mu), P m.
  Proof.
    apply induction_principle.
    intro m1. destruct (eta_expand2 m1).
    intros. apply FIX.
    intros. apply H0, ord_correct, H1.
  Qed.

  Lemma ord_lemma (m : Mu)
    : forall (x : Mu), mem (Des m) x -> ord_c x m.
  Proof.
    intros x MEM.
    rewrite <- eta_expand2. apply tn1_step, ord_correct, MEM.
  Qed.

  Definition Des_ord (m : Mu) : F (sig (fun x => ord_c x m)) :=
    map (fun x => exist (fun x => ord_c x m) _ (ord_lemma _ _ (proj2_sig x)))
        (tag _ (Des m)).

  Lemma Des_ord_correct (fx : F Mu)
    : map (@proj1_sig _ _) (Des_ord (Con fx)) = fx.
  Proof.
    unfold Des_ord. rewrite MAP_COMPOSE.
    simpl. rewrite TAG. apply eta_expand1.
  Qed.

  Definition prim_rec (P : Type)
             (FIX : F P -> P) :=
    rec_simpl (fun m1 f => FIX (map (fun fx => f (proj1_sig fx) (proj2_sig fx))
                                    (Des_ord m1))).

  Lemma prim_rec_red (P : Type)
        (FIX : F P -> P) (fx : F Mu) :
    prim_rec FIX (Con fx) = FIX (map (prim_rec FIX) fx).
  Proof.
    unfold prim_rec. rewrite rec_simpl_red.
    pattern fx at 5. rewrite <- (Des_ord_correct fx).
    rewrite MAP_COMPOSE. reflexivity.
  Qed.

  Lemma Con_injective (fx1 fx2 : F Mu) (EQ : Con fx1 = Con fx2) :
    fx1 = fx2.
  Proof.
    unfold Con in *. apply (INJECTIVE (H1 := ISO)).
    inversion EQ. reflexivity.
  Qed.

  Lemma Des_injective (m1 m2 : Mu) (EQ : Des m1 = Des m2) :
    m1 = m2.
  Proof.
    unfold Des in *. apply (INJECTIVE_R (H1 := ISO)) in EQ. 
    destruct m1, m2. simpl in *. destruct EQ.
    reflexivity.
  Qed.

  Lemma mu_eq_eq : forall (fx1 : F Mu) (fx2 : F Mu),
      Con fx1 = Con fx2 <-> rel eq fx1 fx2.
  Proof.
    intros. split; intro EQ.
    - apply (REL_EQ_EQ _), Con_injective, EQ.
    - f_equal. apply (REL_EQ_EQ _) in EQ. apply EQ.
  Qed.

  Lemma fun_unique (T : Type) (f1 f2 : Mu -> T)
        (FIX : F T -> T) :
    (forall (fx : F Mu), f1 (Con fx) = FIX (map f1 fx)) ->
    (forall (fx : F Mu), f2 (Con fx) = FIX (map f2 fx)) ->
    forall (m : Mu), f1 m = f2 m.
  Proof.
    intros COM1 COM2.
    apply mem_induction_principle. intros.
    rewrite COM1. rewrite COM2. f_equal.
    apply (MAP_POINTWISE _). apply H0.
  Qed.

  Lemma mu_universal (P : Type)
        (FIX : F P -> P) :
    exists! (f : Mu -> P),
      (forall (fx : F Mu), f (Con fx) = FIX (map f fx)).
  Proof.
    exists (prim_rec FIX). split.
    - apply prim_rec_red.
    - intros f EQ. extensionality fx.
      apply fun_unique with (FIX := FIX); [apply prim_rec_red | apply EQ].
  Qed.

  Lemma inj_preserve (T : Type) (f : Mu -> T)
        (FIX : F T -> T)
        (INJ : forall fx1 fx2, FIX fx1 = FIX fx2 -> fx1 = fx2) :
    (forall (fx : F Mu), f (Con fx) = FIX (map f fx)) ->
    (forall m1 m2, f m1 = f m2 -> m1 = m2).
  Proof.
    intro COM.
    apply (mem_induction_principle (fun m => forall m', f m = f m' -> m = m')).
    intros fx INH m'. rewrite <- (eta_expand2 m'). intro EQ.
    rewrite COM in EQ. rewrite COM in EQ. f_equal.
    apply INJ in EQ.
    apply (MAP_MEM_INJECTIVE _ _ INH _ EQ).
  Qed.

(*

  (* this is the most general one!! however i'm not sure it can be proven without K *)

  Definition rec_mem2 (T : forall o, Mu o -> Type)
             (FIX : forall o1 (m1 : F o1 Mu), 
                 (forall o2 m2, mem m1 m2 -> T o2 m2) -> T o1 (Con m1)) :
    forall o (m : Mu o), T o m.
    apply rec_mem'.
    intros. specialize (FIX _ (NTinv _ m1)).

    unfold Con in FIX. rewrite BIJECTION2 in FIX. apply FIX.
    intros. apply X0. apply MEM_COMMUTE in H0. rewrite BIJECTION2 in H0. apply H0.
  Defined.

  Lemma rec_mem_red2 (T : forall o, Mu o -> Type)
        (FIX : forall o1 (m1 : F o1 Mu), 
            (forall o2 (m2 : Mu o2), mem m1 m2 -> T o2 m2) -> T o1 (Con m1)) :
    forall o (m : F o Mu),
      rec_mem2 T FIX (Con m) = FIX _ m (fun o2 m2 _ => rec_mem2 T FIX m2).
    intros. unfold Con. unfold rec_mem2 at 1. simpl.
    rewrite rec_mem'_red. simpl.
    
    set (f := fun m' : F o Mu => (fun (o2 : O) (m2 : Mu o2) (_ : mem m' m2) => rec_mem2 T FIX m2)).

    assert (eq_rect (NT Mu (NTinv Mu (NT Mu m)))
  Defined.

*)

End INDUCTIVE.
