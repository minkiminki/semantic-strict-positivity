Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor.

Section INDUCTIVE.

  Variable I O : Type.
  Variable F : O -> (I + O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.
  Variable X : (iType I).

  Definition X_ (T : O -> Type) : I + O -> Type :=
    fun io : I + O => match io with
                      | inl i => X i
                      | inr o1 => T o1
                      end.

  Goal True. Proof. constructor. Qed.

  Definition X_fun (T1 T2 : O -> Type) (f : forall o, T1 o -> T2 o) io :
    X_ T1 io -> X_ T2 io :=
    match io as io' return (X_ T1 io' -> X_ T2 io') with
    | inl i => (fun x' => x')
    | inr o => (fun x' => f o x')
    end.

  Inductive Mu : O -> Type :=
  | Con' o : sigT (fun (s : S) =>
                    ((forall (i : I), (@P _ _ (H o) s (inl i)) -> X i) *
                     (forall (o1 : O), (@P _ _ (H o) s (inr o1)) -> Mu o1))%type)
            -> Mu o.

  Definition Des' o (m : Mu o) : sigT (fun (s : S) =>
                    ((forall (i : I), (@P _ _ (H o) s (inl i)) -> X i) *
                     (forall (o1 : O), (@P _ _ (H o) s (inr o1)) -> Mu o1))%type) :=
    match m with
    | Con' o s => s end.


  (* I wanna define Mu as below *)
  Fail Inductive Mu' : O -> Type :=
  | Con'' o : sigT (fun (s : S) =>
                     (forall (io : I + O), (@P _ _ (H o) s io) -> 
                                           match io with
                                           | inl i => X i
                                           | inr o1 => Mu' o1
                                           end)) -> Mu' o.
   (* but this definition can't pass the coq's strict positivity checker *)

  Definition Con o (fx : F o (X_ Mu)) : Mu o :=
    match (NT _ fx) with
    | existT _ s f => Con' o (existT _ s
                                     ((fun i (p : P s (inl i)) => f (inl i) p),
                                      (fun o1 (p : P s (inr o1)) => f (inr o1) p))) end.

  Definition Des o (m : Mu o) : F o (X_ Mu) :=
    match m with
    | Con' _ (existT _ s (f1, f2)) =>
      NTinv _
            (existT (fun s' => forall i, P s' i -> (X_ Mu) i) s
                    (fun (io : I + O) (p : P s io) =>
                       match io as io' return (P s io' -> (X_ Mu) io') with
                       | inl i => fun p' : P s (inl i) => f1 i p'
                       | inr o1 => fun p' : P s (inr o1) => f2 o1 p'
                       end p)) end.

  Goal True.
    auto.
  Qed.

  Lemma eta_expand2 : forall o (x : Mu o), Con (Des x) = x.
  Proof.
    intros. unfold Des, Con. destruct x as [o m].
    destruct m as [s [f1 f2]]. rewrite BIJECTION2.
    f_equal.
  Qed.

  Lemma eta_expand1 : forall o (x : F o (X_ Mu)), Des (Con x) = x.
  Proof.
    intros. unfold Des, Con.
    destruct (NT _ x) eqn : EQ.
    rewrite <- BIJECTION1. f_equal. rewrite EQ. f_equal.
    extensionality io. extensionality p.
    destruct io; reflexivity.
  Qed.
  (* if we define Mu as Mu', extensionality isn't necessary *)

(*
  Inductive ord : forall o1, Mu o1 -> forall o2, Mu o2 -> Prop :=
  | _ord (o1 o2 : O) (s : S) (p : P s (inr o1)) f1 f2 :
      ord (f2 o1 p) (Con' o2 (existT _ s (f1, f2))).
*)

  Definition ord : forall o1, Mu o1 -> forall o2, Mu o2 -> Prop :=
    fun o1 m1 o2 m2 =>
      exists (p : P (projT1 (Des' m2)) (inr o1)),
        (m1 = (snd (projT2 (Des' m2))) o1 p).

  Lemma ord_wf : iwell_founded ord.
  Proof.
    unfold iwell_founded. fix 2.
    intros o2 m2. constructor.
    intros o1 m1 ORD. destruct ORD as [p H1].
    rewrite H1. apply ord_wf.
  Qed.

  Definition ord_c := iclos_transn1 ord.

(*
  Lemma ORD_LEMMA o1 o2 (x1 : Mu o1) (x2 : Mu o2) :
    ord x1 x2 ->
    exists s (f1 : forall i : I, P s (inl i) -> X i)
             (f2 : forall x : O, P s (inr x) -> Mu x) (p : P s (inr o1)), x1 = f2 o1 p /\ x2 = Con' o2 (existT _ s (f1, f2)).
  Proof.
    intro.
    destruct H0. exists s. exists f1. exists f2. eauto.
  Qed.
*)

  Lemma Con'_INJ : forall o x y, Con' o x = Con' o y -> x = y.
  Proof.
    intros. apply f_equal with (f := @Des' o) in H0.
    simpl in H0. apply H0.
  Qed.

  Lemma ord_correct : forall o1 (m : Mu o1) o2 (fx : F o2 (X_ Mu)),
      @mem (I + O) (F o2) _ (X_ Mu) fx (inr o1) m <-> ord m (Con fx).
  Proof.
    intros; split; [intro MEM | intro ORD].
    - apply MEM_COMMUTE in MEM. simpl in MEM.
      unfold Con. destruct (NT _ fx) eqn : EQ.
      apply CONTAINER_MEM in MEM. destruct MEM.
      rewrite <- H0. unfold ord. exists x1; reflexivity.
    - apply MEM_COMMUTE. unfold Con in ORD.
      destruct (NT _ fx). simpl in *. unfold ord in ORD. simpl in *.
      destruct ORD. apply CONTAINER_MEM.
      exists x1. symmetry. apply H0.
  Qed.

  Lemma ord_c_wf : iwell_founded ord_c.
  Proof.
    apply wf_iclos_trans.
    apply ord_wf.
  Qed.

  Lemma ord_transitive o1 o2 o3 (x : Mu o1) (y : Mu o2) (z : Mu o3) :
    ord_c x y -> ord_c y z -> ord_c x z.
  Proof.
    apply iclos_transn1_transitive.
  Qed.

  Definition Des_ord o (m : Mu o) : F o (X_ (sigI (fun i x => @ord_c i x _ m))).
    eapply (map _ (tag _ (Des m))).
    Unshelve.
 destruct i. simpl in *.

    - apply (@projI1 _ _ (@mem (I + O) (F o) Fn (X_ Mu) (Des m))).
    - 

      intro. 

      eapply existI.
      
      
      set (itn1_step _ ord (eq_ind _ _ ((proj1 (iff_and ((ord_correct (projI1 X0)) o (Des m)))) (projI2 X0)) _ (eta_expand2 m))). 
      apply i.

  Defined.

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

  Definition prim_rec1 (P : forall (o : O), Type)
             (FIX : forall o, F o (X_ P) -> P o) :
    forall o, Mu o -> P o :=
    rec_simpl1 P
               (fun (o1 : O) (m1 : Mu o1) (f : forall (o2 : O) (m2 : Mu o2), ord_c m2 m1 -> P o2) =>
                  FIX o1 (map (X_fun (sigI (fun (i : O) (x : Mu i) => ord_c x m1)) P
                                     (fun (o : O) (X0 : sigI (fun (i : O) (x : Mu i)
                                                              => ord_c x m1) o) =>
                                        f o (projI1 X0) (projI2 X0))) (Des_ord m1))).

  Definition prim_rec2 T
             (FIX : forall o, F o (X_ (fun _ => T)) -> T) :
    forall o, Mu o -> T :=
    prim_rec1 FIX.

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
             (FIX : forall o1 (fx : F o1 (X_ Mu)), 
                 (forall o2 (m : Mu o2), @mem (I + O) (F o1) _ (X_ Mu) fx (inr o2) m
                                         -> P _ m) -> P _ (Con fx)) :
    forall o (m : Mu o), P o m.
  Proof.
    apply induction_principle.
    intros.
    revert H0. destruct (eta_expand2 m1).
    intros.
    apply FIX.
    intros.
    apply H0, ord_correct, H1.
  Qed.

  Lemma rec_red (P : forall o, Mu o -> Type)
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2 m2) -> P o1 m1)
        o (fx : F o (X_ Mu)) :
    rec _ FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec _ FIX fy).
  Proof.
    apply iFix_eq.
  Qed.

  Lemma rec_simpl1_red (P : forall o, Type)
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord_c m2 m1 -> P o2) -> P o1) 
        o (fx : F o (X_ Mu)) :
    rec_simpl1 _ FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec_simpl1 _ FIX fy).
  Proof.
    apply (rec_red _ FIX fx).
  Qed.

  Lemma rec_simpl2_red T
        (FIX : forall o1 (m1 : Mu o1), 
            (forall o2 (m2 : Mu o2), ord_c m2 m1 -> T) -> T)
        o (fx : F o (X_ Mu)) :
    rec_simpl2 FIX (Con fx) = FIX _ (Con fx) (fun _ fy _ => rec_simpl2 FIX fy).
  Proof.
    apply (rec_simpl1_red _ FIX fx).
  Qed.

  Lemma prim_rec1_red (P : forall (o : O), Type)
        (FIX : forall o, F o (X_ P) -> P o) o (fx : F o (X_ Mu)) :
    prim_rec1 FIX (Con fx) = FIX _ (map (X_fun _ _ (prim_rec1 FIX)) fx).
  Proof.
    unfold prim_rec1.
    rewrite rec_simpl1_red.
    unfold X_fun. simpl in *. f_equal. unfold Des_ord.
    rewrite MAP_COMPOSE. simpl in *. 
    
    


    
  Admitted.
  
  Lemma prim_rec2_red T (FIX : forall o, F o (X_ (fun _ => T)) -> T)
        o (fx : F o (X_ Mu)) :
    prim_rec2 FIX (Con fx) = FIX _ (map (X_fun _ _ (prim_rec2 FIX)) fx).
  Proof.
    apply (prim_rec1_red FIX).
  Qed.

End INDUCTIVE.