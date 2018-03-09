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

  Definition Des o (m : Mu o) : F o Mu := NTinv _ (Des' m).

  Lemma eta_expand2 : forall o (x : Mu o), Con (Des x) = x.
  Proof.
    intros. unfold Des, Con. rewrite BIJECTION2.
    destruct x. reflexivity.
  Qed.

  Lemma eta_expand1 : forall o (x : F o Mu), Des (Con x) = x.
  Proof.
    intros. unfold Des, Con.
    rewrite <- BIJECTION1.
    destruct (NT Mu x). reflexivity.
  Qed.

  Definition ord : forall o1, Mu o1 -> forall o2, Mu o2 -> Prop :=
   fun o1 m1 o2 m2 => mem (Des' m2) m1.

  Lemma ord_wf : iwell_founded ord.
  Proof.
    unfold iwell_founded. fix 2.
    intros o2 m2. constructor.
    intros o1 m1 ORD. destruct ORD.
    rewrite <- H0. apply ord_wf.
  Qed.

  Definition ord_c := iclos_transn1 ord.

  Lemma ord_correct : forall o1 (m : Mu o1) o2 (fx : F o2 Mu),
      @mem O (F o2) _ Mu fx o1 m <-> ord m (Con fx).
  Proof.
    intros. rewrite MEM_COMMUTE. reflexivity.
  Qed.

  Lemma ord_c_wf : iwell_founded ord_c.
  Proof.
    apply wf_iclos_trans. apply ord_wf.
  Qed.

  Lemma ord_transitive o1 o2 o3 (x : Mu o1) (y : Mu o2) (z : Mu o3) :
    ord_c x y -> ord_c y z -> ord_c x z.
  Proof.
    apply iclos_transn1_transitive.
  Qed.

  Definition rec (P : forall o, Mu o -> Type)
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2 m2) -> P o1 m1) :
    forall o (m : Mu o), P o m :=
    iFix ord_c_wf P FIX.

  Definition rec_simpl1 (P : forall o, Type)
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2) -> P o1) :
    forall o, Mu o -> P o :=
    rec _ FIX.

  Definition rec_simpl2 T
             (FIX : forall o1 (m1 : Mu o1), 
                 (forall o2 (m2 : Mu o2), ord_c m2 m1 -> T) -> T) :
    forall o, Mu o -> T :=
    rec_simpl1 _ FIX.

  Lemma rec_red (P : forall o, Mu o -> Type)
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2 m2) -> P o1 m1)
        o (fx : F o  Mu) :
    rec _ FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec _ FIX fy).
  Proof.
    apply iFix_eq.
  Qed.

  Lemma rec_simpl1_red (P : forall o, Type)
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2) -> P o1) 
        o (fx : F o Mu) :
    rec_simpl1 _ FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec_simpl1 _ FIX fy).
  Proof.
    apply (rec_red _ FIX fx).
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

(*apply MAP_MEM_INJECTIVE in EQ. 
    - apply EQ. 
    - apply INH.
  Qed.
*)

(*

  Definition rec_mem' (T : forall o, Mu o -> Type)
             (FIX : forall o1 m1, 
                 (forall o2 m2, mem m1 m2 -> T o2 m2) -> T o1 (Con' o1 m1)) :
    forall o (m : Mu o), T o m.
    apply rec. intros o1 m1 f.
    destruct m1. apply FIX.
    intros o2 m2 MEM. apply f, itn1_step, MEM.
  Defined.

  Lemma rec_mem'_red (T : forall o, Mu o -> Type)
             (FIX : forall o1 m1, 
                 (forall o2 m2, mem m1 m2 -> T o2 m2) -> T o1 (Con' o1 m1)) :
    forall o m,
      rec_mem' T FIX (Con' o m) = FIX _ m (fun o2 m2 _ => rec_mem' T FIX m2).
  Proof.  
    intros. apply iFix_eq.
  Qed.

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
    (fun c : Container P Mu =>
     (forall (o2 : O) (m2 : Mu o2), mem (NTinv Mu (NT Mu m)) m2 -> T o2 m2) ->
     T o (Con' o c)) (FIX o (NTinv Mu (NT Mu m))) (NT Mu m) 
    (BIJECTION2 Mu (NT Mu m)) (f (NTinv Mu (NT Mu m))) =
  FIX o m (f m)); [| apply H0].

    simpl. remember (BIJECTION2 Mu (NT Mu m)). 
  Admitted.

  Lemma rec_mem_lemma o1 (m1 : Mu o1) o2 (m2 : Mu o2) :
    mem (Des m1) m2 -> ord_c m2 m1.
  Proof.
    intro MEM. rewrite <- eta_expand2.
    apply itn1_step, ord_correct, MEM.
  Qed.



  Definition rec_mem (T : forall o, Mu o -> Type)
             (FIX : forall o1 (m1 : F o1 Mu), 
                 (forall o2 (m2 : Mu o2), mem m1 m2 -> T o2 m2) -> T o1 (Con m1)) :
    forall o (m : Mu o), T o m.
    apply rec. intros o1 m1 f.

    
    rewrite <- eta_expand2. apply FIX. 

    intros o2 m2 MEM. apply f. apply (rec_mem_lemma _ _ MEM).
  Defined.

  Lemma rec_mem_red (T : forall o, Mu o -> Type)
        (FIX : forall o1 (m1 : F o1 Mu), 
            (forall o2 (m2 : Mu o2), mem m1 m2 -> T o2 m2) -> T o1 (Con m1)) :
    forall o (m : F o Mu),
      rec_mem T FIX (Con m) = FIX _ m (fun o2 m2 _ => rec_mem T FIX m2).


    intros. unfold rec_mem at 1. rewrite rec_red. simpl.
    set (f := fun (m' : F o Mu) => fun (o2 : O) (m2 : Mu o2) (_ : mem m' m2) => rec_mem T FIX m2).
    assert (eq_rect (Con (Des (Con m))) (T o)
                    (FIX o (Des (Con m)) (f (Des (Con m)))) (Con m) (eta_expand2 (Con m)) =
            FIX o m (f m)).
    - remember (eta_expand2 (Con m)).

      
      assert (m' : Mu o). admit.
      assert (Des m' = m). admit.
      destruct H0. simpl. 

      admit.

  Definition Des2 : forall o, Mu o -> F o Mu :=
    rec_mem (fun o _ => F o Mu) (fun _ m _ => m). 

  Goal True. apply I. Qed.

  Lemma Des2_eta1 : forall o (x : Mu o), Con (Des2 x) = x.
  Proof.
    apply rec_mem. intros o1 m1 FIX.
    unfold Des2. rewrite rec_mem_red. reflexivity.
  Qed.

  Lemma Des2_eta2 : forall o (fx : F o Mu), Des2 (Con fx) = fx.
  Proof.
    intros. unfold Des2. rewrite rec_mem_red. reflexivity. 
  Qed.
*)

End INDUCTIVE.
