Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor iinductive hott.

Section Mu.

  Variable A B : Type.
  Variable (F : (A -> Type) -> B -> (B -> Type)-> Type).

  Context `{SPF1 : forall b X, SPFunctor (F X b)}.
  Context `{SPF2 : forall b Y, SPFunctor (fun X => F X b Y)}.

  Arguments map {C F} Functor {X Y} f x.
  Arguments Fn {C F} SPFunctor.

  Definition bimap b X1 X2 Y1 Y2 (f : forall a, X1 a -> X2 a)
             (g : forall b0, Y1 b0 -> Y2 b0) : F X1 b Y1 -> F X2 b Y2 :=
    fun fx => map (Fn (SPF1 b X2)) g (map (Fn (SPF2 b Y1)) f fx).

  Definition mu b (X : A -> Type) := Mu (F X) b.
  
  Goal True. apply I. Qed.
  
  Program Definition mu_Functor b : Functor (mu b)
    := Build_Functor _ _ _ _ _.
  Next Obligation.
    revert b X0. apply prim_rec.
    intros o fx.
    apply Con. apply (map (Fn (SPF2 _ _)) f fx). Show Proof.
  Defined.
  Next Obligation.
    revert b X0 i X1.
    apply (@simple_rec _ (F X) _ (forall i : A, X i -> Prop)). intros o fx i x.
    apply or.
    - apply (mem fx x).
    - apply (exists j (p : forall i : A, X i -> Prop), mem fx p (i := j) /\ p i x).
  Defined.  
  Next Obligation.
    revert b fx fy. apply (@prim_rec _ (F X) _ (fun b => Mu (F Y) b -> Prop)).
    intros o fx m.

    apply Des in m.
  Admitted.
  Next Obligation.
    revert b fx. apply rec. intros o1 m1 FIX.

    unfold mu. apply Con.
    
    set (Des_ord m1).

    set (tag X f). simpl in *.
    eapply (bimap _ _ _ _ y). Unshelve.

    - intros a x. apply (existI (projI1 x)). 
      unfold mu_Functor_obligation_2. simpl.
      set (projI2 x). 




apply (existI x). sigI
    

    unfold mu_Functor_obligation_2, mu. simpl.

  Definition mu_map b (X Y : A ->
  