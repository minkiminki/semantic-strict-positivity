Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor.

Section INDUCTIVE.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.
  
  Inductive Mu o : Type :=
  | Con' : Container (@degree _ _ (H o)) Mu -> Mu o.

  Definition Con o (fx : F o Mu) : Mu o := Con' o (NT _ fx).

  Definition Des' o (m : Mu o) : Container (@degree _ _ (H o)) Mu :=
    match m with
    | Con' _ s => s end.

  Definition ord : forall o1, Mu o1 -> forall o2, Mu o2 -> Prop :=
   fun o1 m1 o2 m2 => mem (Des' m2) m1.

  Lemma ord_wf : iwell_founded ord.
  Proof.
    unfold iwell_founded. fix 2.
    intros o2 m2. constructor.
    intros o1 m1 ORD. destruct ORD.
    rewrite <- H0. apply ord_wf.
  Qed.

  Inductive ord_c : forall i (x: Mu i) j (y : Mu j), Type :=
  | itn1_step {i} (x: Mu i) {j} (y : Mu j) : ord x y -> ord_c x y
  | itn1_trans {i} (x: Mu i) {j} (y : Mu j) {k} (z : Mu k)
    : ord_c x y -> ord y z -> ord_c x z.

  Lemma ord_correct : forall o1 (m : Mu o1) o2 (fx : F o2 Mu),
      @mem O (F o2) _ Mu fx o1 m <-> ord m (Con fx).
  Proof.
    intros. rewrite MEM_COMMUTE. reflexivity.
  Qed.

  Lemma ord_transitive o1 o2 o3 (x : Mu o1) (y : Mu o2) (z : Mu o3) :
    ord_c x y -> ord_c y z -> ord_c x z.
  Proof.
    intros ORD1 ORD2. revert x ORD1. induction ORD2. 
    - intros x0 ORD. apply (itn1_trans ORD o).
    - intros x0 ORD.
      apply (itn1_trans (IHORD2 _ ORD) o).
  Qed.

  Definition rec_mem (T : forall o, Mu o -> Type)
             (FIX : forall o1 (m1 : F o1 Mu), 
                 (forall o2 (m2 : Mu o2), mem m1 m2 -> T o2 m2) -> T o1 (Con m1)) :
    forall o (m : Mu o), T o m.
  Admitted.

  Lemma rec_mem_red (T : forall o, Mu o -> Type)
        (FIX : forall o1 (m1 : F o1 Mu), 
            (forall o2 (m2 : Mu o2), mem m1 m2 -> T o2 m2) -> T o1 (Con m1)) :
    forall o (m : F o Mu),
      rec_mem T FIX (Con m) = FIX _ m (fun o2 m2 _ => rec_mem T FIX m2).
  Admitted.

  Definition Des : forall o, Mu o -> F o Mu :=
    rec_mem (fun o _ => F o Mu) (fun _ m _ => m).

  Lemma eta_expand1 : forall o (x : F o Mu), Des (Con x) = x.
  Proof.
    intros o x. unfold Des. rewrite rec_mem_red. reflexivity.
  Qed.

  Lemma eta_expand2 : forall o (x : Mu o), Con (Des x) = x.
  Proof.
    apply rec_mem. intros o1 m1 IH.
    unfold Des. rewrite rec_mem_red. reflexivity.
  Qed.

  Definition rec (P : forall o, Mu o -> Type)
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord m2 m1 -> P o2 m2) -> P o1 m1) :
    forall o (m : Mu o), P o m.
    apply rec_mem. intros o1 m1 IH. apply FIX.
    intros o2 m2 ORD. apply IH. 
    apply ord_correct. apply ORD.
  Defined.

  Lemma rec_red (P : forall o, Mu o -> Type)
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord m2 m1 -> P o2 m2) -> P o1 m1)
        o (fx : F o  Mu) :
    rec _ FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec _ FIX fy).
  Proof.
    unfold rec at 1. apply rec_mem_red.
  Qed.

  Definition rec_c' (P : forall o, Mu o -> Type)
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2 m2) -> P o1 m1) :
    forall o (m : Mu o),
      P o m * (forall (o2 : O) (m2 : Mu o2), ord_c m2 m -> P o2 m2).
    apply rec.
    intros o1 m1 IH. split.
    - apply FIX. intros o2 m2 ORD. destruct ORD.
      + apply (fst (IH _ x o)).
      + apply (snd (IH _ _ o) _ _ ORD).
    - intros o2 m2 ORD. destruct ORD.
      + apply (fst (IH _ x o)).
      + apply (snd (IH _ _ o) _ _ ORD).
  Defined.

  Definition rec_c (P : forall o, Mu o -> Type)
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2 m2) -> P o1 m1) :
    forall o (m : Mu o), P o m.
    intros o m. apply (fst (rec_c' _ FIX m)).
  Defined.

  Lemma rec_c_red (P : forall o, Mu o -> Type)
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2 m2) -> P o1 m1)
        o (fx : F o  Mu) :
    rec_c _ FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec_c _ FIX fy).
  Proof.
    unfold rec_c, rec_c' at 1. rewrite rec_red. simpl. f_equal.
    extensionality o2. extensionality m2. extensionality ORD.
    destruct ORD. simpl. reflexivity. 
    simpl.
  Admitted.

  Definition rec_simpl1 (P : forall o, Type)
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2) -> P o1) :
    forall o, Mu o -> P o :=
    rec_c _ FIX.

  Definition rec_simpl2 T
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord_c m2 m1 -> T) -> T) :
    forall o, Mu o -> T :=
    rec_simpl1 _ FIX.

  Lemma rec_simpl1_red (P : forall o, Type)
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2) -> P o1) 
        o (fx : F o Mu) :
    rec_simpl1 _ FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec_simpl1 _ FIX fy).
  Proof.
    apply (rec_c_red _ FIX fx).
  Qed.

  Lemma rec_simpl2_red T
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord_c m2 m1 -> T) -> T)
        o (fx : F o Mu) :
    rec_simpl2 FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec_simpl2 FIX fy).
  Proof.
    apply (rec_simpl1_red _ FIX fx).
  Qed.

  Definition induction_principle (P : forall o, Mu o -> Prop)
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord m2 m1 -> P o2 m2) -> P o1 m1) :
    forall o (m : Mu o), P o m.
  Proof.
    apply (iFix ord_wf P FIX).
  Qed.

(*
  Definition str_induction_principle (P : forall o, Mu o -> Prop)
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2 m2) -> P o1 m1) :
    forall o (m : Mu o), P o m.
  Proof.
    
    apply (iFix ord_c_wf P FIX).
  Qed.

  Definition mem_induction_principle (P : forall o, Mu o -> Prop)
             (FIX : forall o1 (fx : F o1 Mu), 
                 (forall o2 (m : Mu o2), mem fx m -> P _ m) -> P _ (Con fx)) :
    forall o (m : Mu o), P o m.
  Proof.
    apply induction_principle.
    intros o1 m1. destruct (eta_expand2 m1).
    intros. apply FIX.
    intros. apply H0, ord_correct, H1.
  Qed.

  Lemma ord_lemma o (m : Mu o)
    : forall (i : O) (x : Mu i), mem (Des m) x -> ord_c x m.
  Proof.
    intros i x MEM.
    rewrite <- eta_expand2. apply itn1_step, ord_correct, MEM.
  Qed.

  Definition Des_ord o (m : Mu o) : F o (sigI (fun i x => @ord_c i x _ m)) :=
    @map _ (F o) _ _ _ (sigImply _ (ord_lemma m)) (tag _ (Des m)).

  Lemma Des_ord_correct o (fx : F o Mu)
    : map (@projI1 _ _ _) (Des_ord (Con fx)) = fx.
  Proof.
    unfold Des_ord. rewrite MAP_COMPOSE.
    simpl. rewrite TAG. apply eta_expand1.
  Qed.

  Definition prim_rec (P : forall (o : O), Type)
             (FIX : forall o, F o P -> P o) :=
    rec_simpl1 P (fun o1 m1 f => FIX _ (map (fun o fx => f _ (projI1 fx) (projI2 fx))
                                            (Des_ord m1))).

  Lemma prim_rec_red (P : forall (o : O), Type)
        (FIX : forall o, F o P -> P o) o (fx : F o Mu) :
    prim_rec FIX (Con fx) = FIX o (map (prim_rec FIX) fx).
  Proof.
    unfold prim_rec. rewrite rec_simpl1_red.
    pattern fx at 5. rewrite <- (Des_ord_correct fx).
    rewrite MAP_COMPOSE. reflexivity.
  Qed.

  Definition simple_rec T
             (FIX : forall o, F o (fun _ => T) -> T) :
    forall o, Mu o -> T :=
    prim_rec FIX.
  
  Lemma simple_rec_red T (FIX : forall o, F o (fun _ => T) -> T)
        o (fx : F o Mu) :
    simple_rec FIX (Con fx) = FIX _ (map (simple_rec FIX) fx).
  Proof.
    apply (prim_rec_red FIX).
  Qed.

  Lemma Con_injective o (fx1 fx2 : F o Mu) (EQ : Con fx1 = Con fx2) :
    fx1 = fx2.
  Proof.
    unfold Con in *. apply (INJECTIVE (H1 := ISO)).
    inversion EQ. reflexivity.
  Qed.

  Lemma Des_injective o (m1 m2 : Mu o) (EQ : Des m1 = Des m2) :
    m1 = m2.
  Proof.
    unfold Des in *. apply (INJECTIVE_R (H1 := ISO)) in EQ. 
    destruct m1, m2. simpl in *. destruct EQ.
    reflexivity.
  Qed.

  Lemma mu_eq_eq : forall o (fx1 : F o Mu) (fx2 : F o Mu),
      Con fx1 = Con fx2 <-> rel (fun _ => eq) fx1 fx2.
  Proof.
    intros. split; intro EQ.
    - apply REL_EQ_EQ, Con_injective, EQ.
    - f_equal. apply REL_EQ_EQ in EQ. apply EQ.
  Qed.

  Lemma fun_unique (T : O -> Type) (f1 f2 : forall o, Mu o -> T o)
        (FIX : forall o, F o T -> T o) :
    (forall o (fx : F o Mu), f1 o (Con fx) = FIX o (map f1 fx)) ->
    (forall o (fx : F o Mu), f2 o (Con fx) = FIX o (map f2 fx)) ->
    forall o (m : Mu o), f1 o m = f2 o m.
  Proof.
    intros COM1 COM2.
    apply mem_induction_principle. intros.
    rewrite COM1. rewrite COM2. f_equal.
    apply MAP_POINTWISE. apply H0.
  Qed.

  Lemma mu_universal (P : forall (o : O), Type)
        (FIX : forall o, F o P -> P o) :
    exists! (f : forall o, Mu o -> P o),
      (forall o (fx : F o Mu), f o (Con fx) = FIX o (map f fx)).
  Proof.
    exists (prim_rec FIX). split.
    - apply prim_rec_red.
    - intros f EQ. extensionality o. extensionality fx.
      apply fun_unique with (FIX := FIX); [apply prim_rec_red | apply EQ].
  Qed.

  Lemma inj_preserve (T : O -> Type) (f : forall o, Mu o -> T o)
        (FIX : forall o, F o T -> T o)
        (INJ : forall o fx1 fx2, FIX o fx1 = FIX o fx2 -> fx1 = fx2) :
    (forall o (fx : F o Mu), f o (Con fx) = FIX o (map f fx)) ->
    (forall o m1 m2, f o m1 = f o m2 -> m1 = m2).
  Proof.
    intro COM.
    apply (mem_induction_principle (fun o m => forall m', f o m = f o m' -> m = m')).
    intros o1 fx INH m'. rewrite <- (eta_expand2 m'). intro EQ.
    rewrite COM in EQ. rewrite COM in EQ. f_equal.
    apply INJ in EQ.
  Admitted.

*)

End INDUCTIVE.
