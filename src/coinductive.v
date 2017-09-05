Require Import paco.
Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor spec.

Section coinductive.

  Variable PF : Type -> Type.
  Context `{SPF : SPFunctor PF}.

  Definition fcofix : Type. Admitted. (* coinductive type *)

  Definition Fcofix : PF fcofix -> fcofix. Admitted. (* constructor *)

  Definition fcofix_des : fcofix ->  PF fcofix. Admitted. (* destructor *)

  Definition Fcofix_inj : forall x1 x2 (EQ: Fcofix x1 = Fcofix x2), x1 = x2. Admitted.
  (* constructors are injective *)

  Definition c_des_correct1 : forall x, Fcofix (fcofix_des x) = x. Admitted.

  Definition c_des_correct2 : forall x, fcofix_des (Fcofix x) = x. Admitted.
  (* these say that destructors are the inverse of constructors *)


(* for corecursive functions *)
(* we use mendler style corecursion *)

  Definition grd_fcofix : Type -> Type. Admitted.

  Definition val : forall (A : Type), fcofix -> grd_fcofix A. Admitted.

  Definition grd : forall (A : Type), PF (sum A (grd_fcofix A)) -> grd_fcofix A. Admitted.
  (* constructors for grd_fcofix *)

  Definition grd_fcofix_des : forall (A: Type),
      grd_fcofix A -> fcofix + (PF (sum A (grd_fcofix A))). Admitted.
  (* destructors for grd_fcofix *)

  Definition val_des_correct : forall A (x: fcofix),
      grd_fcofix_des (val A x) = inl x. Admitted.

  Definition grd_des_correct : forall A (f: PF (sum A (grd_fcofix A))),
      grd_fcofix_des (@grd A f) = inr f. Admitted.
  (* destructros are the inverse of constructors *)

  Definition to_fcofix : forall A, (A -> grd_fcofix A) ->
                                 (sum A (grd_fcofix A)) -> fcofix. Admitted.
  (* users don't need to know this function *)

  Definition fcorec : forall A, (A -> grd_fcofix A) -> (A -> fcofix). Admitted.
  (* corecursive function!!! *)

  Definition fcorec_p : forall A (f: A -> PF A), A -> fcofix. Admitted.
  (* primitive corecursion *)


(* reduction rules for corecursive functions *)

  Definition fcorec_red : forall A (f: A -> grd_fcofix A) (a: A),
      fcofix_des (fcorec f a) = match (grd_fcofix_des (f a)) with
                                | inl x => fcofix_des x
                                | inr m => SPF.(map) (to_fcofix f) m end. Admitted.
        
  Definition to_fcofix_correct1 : forall A (f: A -> grd_fcofix A) a,
    to_fcofix f (inl a) = fcorec f a. Admitted.

  Definition to_fcofix_correct2 : forall A (f: A -> grd_fcofix A) x,
    to_fcofix f (inr (val A x)) = x. Admitted.

  Definition to_fcofix_correct3 : forall A (f: A -> grd_fcofix A) m,
    to_fcofix f (inr (@grd A m)) = Fcofix (SPF.(map) (to_fcofix f) m). Admitted.

  Definition fcorec_p_red : forall A (f: A -> PF A) a,
    fcofix_des (fcorec_p f a) = SPF.(map) (fcorec_p f) (f a). Admitted.

(* bisimilarity *)

  Definition bsm_gen_mon : monotone2 (bsm_gen Fcofix). Admitted.

  Definition bsm (x1 x2 : fcofix) : Prop := paco2 (bsm_gen Fcofix) bot2 x1 x2.

  Definition bsm_eq : forall x1 x2, bsm x1 x2 <-> x1 = x2. Admitted.
  (* bisimilarity axiom.
     its proof relies on the bisimilarity axiom of universal functors *)

(* tactics for reduction *)

End coinductive.


Global Opaque fcofix Fcofix fcofix_des Fcofix_inj c_des_correct1 c_des_correct2 grd_fcofix val grd grd_fcofix_des val_des_correct grd_des_correct to_fcofix fcorec fcorec_p fcorec_red fcorec_p_red to_fcofix_correct1 to_fcofix_correct2 to_fcofix_correct3 bsm_gen_mon bsm_eq.


Ltac csimpl := repeat (autounfold;
                       repeat rewrite c_des_correct2;
                       repeat rewrite val_des_correct;
                       repeat rewrite grd_des_correct;
                       repeat rewrite fcorec_red;
                       repeat rewrite fcorec_p_red;
                       repeat rewrite to_fcofix_correct1;
                       repeat rewrite to_fcofix_correct2;
                       repeat rewrite to_fcofix_correct3;
                       unfold id;
                       simpl).

Ltac csimpl_in H := repeat (autounfold in H;
                            repeat rewrite c_des_correct2 in H;
                            repeat rewrite val_des_correct in H;
                            repeat rewrite grd_des_correct in H;
                            repeat rewrite fcorec_red in H;
                            repeat rewrite fcorec_p_red in H;
                            repeat rewrite to_fcofix_correct1 in H;
                            repeat rewrite to_fcofix_correct2 in H;
                            repeat rewrite to_fcofix_correct3 in H;
                            unfold id in H;
                            simpl in H).

Arguments fcofix PF {SPF}.
Arguments Fcofix PF {SPF}.
