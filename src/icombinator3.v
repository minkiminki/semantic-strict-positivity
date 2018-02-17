(*Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor icombinator icombinator2.
Require Import iinductive.

Section MU.

  Variable I O : Type.
  Variable F : O -> (I + O -> Type) -> Type.
  Context `{forall c, SPFunctor (F c)}.

  Definition Mu2 o X := Mu F X o.

  Definition Mu_map o X Y (f : forall i : I, X i -> Y i) :=
    @prim_rec1 _ _ F _ X (Mu F Y)
               (fun (o0 : O) fx =>
                  Con F Y o0
                      (map
                         (fun (i : I + O) =>
                            match i as s return (X_ X (Mu F Y) s -> X_ Y (Mu F Y) s) with
                            | inl i0 => fun x' : X_ X (Mu F Y) (inl i0) => f i0 x'
                            | inr o1 => fun x' : X_ X (Mu F Y) (inr o1) => x'
                            end) fx)) o.

  Arguments Mu_map {o X Y} f.

  Goal True. constructor. Qed.

  Lemma Mu_map_red X Y (f : forall i : I, X i -> Y i) o (x : F o (X_ X (Mu F X))) :
    Mu_map f (Con _ _ _ x) =
    Con F Y o
        (map (fun i : I + O =>
                match i as s return (X_ X (Mu F X) s -> X_ Y (Mu F Y) s) with
                | inl i0 => f i0
                | inr o0 => Mu_map f
                end) x).
  Proof.
    unfold Mu_map. rewrite prim_rec1_red. simpl. f_equal.
    rewrite MAP_COMPOSE. simpl. f_equal.
    extensionality i. extensionality x0. destruct i; auto.
  Qed.

  Lemma Mu_map_compose X Y Z (f : forall i, X i -> Y i) (g : forall i, Y i -> Z i) o (fx : Mu F X o) :
    Mu_map g (Mu_map f fx) = Mu_map (fun i x => g i (f i x)) fx.
  Proof.
    revert o fx. apply (@mem_induction_principle _ _ F).

    intros. symmetry.
    rewrite Mu_map_red. rewrite Mu_map_red. rewrite Mu_map_red.
    rewrite MAP_COMPOSE. f_equal.
    giveup.
  Qed.

  Definition Mu_mem o X :=
    @prim_rec2 _ _ F _ _ _
               (fun o1 (fx : F o1 (X_ X _)) i (x : X i) =>
                  mem fx x \/ (exists o2 (p : X_ X _ (inr o2)), mem fx p)) o.

  Definition AD X : ( forall (o1 : O) (m1 : Mu F X o1),
  (forall (o2 : O) (m2 : Mu F X o2), ord_c m2 m1 -> Mu2 o2 (sigI (Mu_mem m2))) ->
  Mu2 o1 (sigI (Mu_mem m1))).
          intros. apply Con.
    eapply (map _ (Des_ord m1)). Unshelve.
    intros. destruct i; simpl in *.
    - apply (existI X1). giveup.
    - eapply (Mu_map (sigImply _ _) (X0 _ (projI1 X1) (projI2 X1))).
      Unshelve. giveup. Defined.

  Program Definition Mu_Functor o : Functor (Mu2 o) :=
    Build_Functor _ (@Mu_map o) (@Mu_mem o) _
                  (fun (X : iType I) fx =>
                     rec (fun (o0 : O) (m : Mu F X o0)
                          => Mu2 o0 (sigI (Mu_mem m))) (AD (X:=X)) fx) _.
  Next Obligation.    
    revert o fx fy.
    apply (@prim_rec1 _ _ F _ X (fun o1 => Mu2 o1 Y -> Prop)).

    intros.
    apply Des in X1.
    eapply (rel _ X0 X1). Unshelve.

    intros. clear o X0 X1.

    destruct i.
    - apply (R _ X2 X3).
    - apply (X2 X3).
  Defined.
  Next Obligation.

    revert o fx.
    apply (@mem_induction_principle _ _ F _ X).
    intros. 
    
    rewrite rec_red. unfold AD at 1. simpl.
    rewrite Mu_map_red. simpl. f_equal.

    rewrite MAP_COMPOSE. simpl.

    match goal with
    | [ |- map ?ff ?x = ?x1 ] => set (f := ff) end.
    replace f with (fun i : I + O =>
      match
        i as s
        return
          (X_ X (sigI (fun (i0 : O) (x : Mu F X i0) => ord_c x (Con F X o1 fx))) s ->
           X_ X (Mu F X) s)
      with
      | inl i0 => id
      | inr o0 =>
          fun
            X0 : sigI (fun (i0 : O) (x : Mu F X i0) => ord_c x (Con F X o1 fx)) o0
          =>
          Mu_map (projI1 (P:=Mu_mem (projI1 X0)))
            (rec (fun (o2 : O) (m0 : Mu F X o2) => Mu2 o2 (sigI (Mu_mem m0)))
               (AD (X:=X)) (projI1 X0))
      end).
    - clear f. unfold Des_ord.
      rewrite MAP_COMPOSE. simpl.
      match goal with
      | [ |- map ?ff ?x = ?x1 ] => set (f := ff) end.
      
      set (f1 := projI1 (P := @mem (I + O) (F o1) Fn (X_ X (Mu F X)) (Des (Con F X o1 fx)))).            
      set (f2 := fun i : I + O =>
      match i as s return (X_ X (Mu F X) s -> X_ X (Mu F X) s) with
      | inl i0 => id
      | inr o0 =>
          fun X0 : Mu F X o0 =>
          Mu_map (projI1 (P:=Mu_mem X0))
            (rec (fun (o2 : O) (m0 : Mu F X o2) => Mu2 o2 (sigI (Mu_mem m0)))
               (AD (X:=X)) X0)
      end).
      replace f with (fun i x => f2 i (f1 i x)).
      + rewrite <- MAP_COMPOSE. unfold f2, f1. clear f2 f1 f.
        rewrite (eta_expand1 F _ _ fx). rewrite TAG. giveup.
      + unfold f, f1, f2. extensionality i. destruct i; reflexivity.
    - unfold f. extensionality i. destruct i; simpl; try reflexivity.
      extensionality X0. rewrite Mu_map_compose. f_equal.
      extensionality i. extensionality x. apply sigImply_proj1.
  Qed.

  
  

  

Definition Mu C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type) `{H : forall c, SPF (F c)} :
  (C2 -> (C1 -> Type) -> Type). Admitted.
Instance Mu_SPF C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type)
        `{H : forall c, SPF (F c)} : forall c, SPF (Mu F c). Admitted.

Definition Nu C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type) `{H : forall c, SPF (F c)} :
  (C2 -> (C1 -> Type) -> Type). Admitted.
Instance Nu_SPF C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type)
        `{H : forall c, SPF (F c)} : forall c, SPF (Nu F c). Admitted.




End MU.
*)