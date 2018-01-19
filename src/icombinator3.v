Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor icombinator icombinator2.
Require Import iinductive.

Section MU.

  Variable I O : Type.
  Variable F : O -> (I + O -> Type) -> Type.
  Context `{forall c, SPFunctor (F c)}.
(*  
  Definition Mu2 o X := Mu F X o.
  Program Definition Mu_Functor o : Functor (Mu2 o) := Build_Functor _ _ _ _ _ _.
  Next Obligation.
    revert o X0.
    
    apply (@prim_rec1 _ _ F _ X (Mu F Y)). 
    intros.
    apply Con.

    eapply (map _ X0). Unshelve.

    intros. destruct i; simpl in *.
    - apply (f _ X1).
    - apply X1.
  Defined.
  Next Obligation.
    revert o X0 i X1.
    apply (@prim_rec2 _ _ F _ X (forall i, X i -> Prop)). 

    intros.
    
  
Definition Mu C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type) `{H : forall c, SPF (F c)} :
  (C2 -> (C1 -> Type) -> Type). Admitted.
Instance Mu_SPF C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type)
        `{H : forall c, SPF (F c)} : forall c, SPF (Mu F c). Admitted.

Definition Nu C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type) `{H : forall c, SPF (F c)} :
  (C2 -> (C1 -> Type) -> Type). Admitted.
Instance Nu_SPF C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type)
        `{H : forall c, SPF (F c)} : forall c, SPF (Nu F c). Admitted.


*)

End MU.
