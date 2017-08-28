Set Implicit Arguments.
Set Automatic Coercions Import.
Require Import Coq.Relations.Relation_Operators.
Require Import Functor SPFunctor paco.

Inductive less_ones X (R : X -> X -> Prop) y : Type :=
| w_ord x (ORD: R x y) : less_ones R y.
Arguments less_ones {X} {R}.
Arguments w_ord {X} {R} {y} x ORD.

Arguments clos_trans_n1 {A} R.

Inductive bsm_gen PF `{SPFunctor PF} (fcofix : Type) (Fcofix : PF fcofix -> fcofix)
          bsm : fcofix -> fcofix -> Prop :=
| _bsm_gen : forall (x1 x2 : PF fcofix) (R: rel bsm x1 x2),
    bsm_gen Fcofix bsm (Fcofix x1) (Fcofix x2).

Definition bsm PF `{SPFunctor PF} (fcofix : Type) (Fcofix : PF fcofix -> fcofix) x1 x2 := paco2 (bsm_gen Fcofix) bot2 x1 x2.
Arguments bsm {PF} {H} {H0} {H1} {fcofix} Fcofix x1 x2.
Hint Unfold bsm.

Module Type INDUCTIVE.

  Section inductive.

  Variable PF : Type -> Type.
  Variable H : (FunctorData PF).
  Variable H0 : (SFunctorData PF).
  Variable SPF : (SPFunctor PF).

(* constructor and destructor *)

  Variable ffix : Type. (* inductive type *)

  Variable Ffix : PF ffix -> ffix. (* constructor *)

  Variable ffix_des : ffix -> PF ffix. (* destructor *)

  Hypothesis Ffix_inj : forall x1 x2 (EQ: Ffix x1 = Ffix x2), x1 = x2.
  (* constructors are injective *)

  Hypothesis des_correct1 : forall x, Ffix (ffix_des x) = x.

  Hypothesis des_correct2 : forall x, ffix_des (Ffix x) = x.
  (* these say that destructors are the inverse of constructors *)


(* order and induction principle *)

  Variable ffix_ord : ffix -> ffix -> Prop. (* order on ffix *)

  Hypothesis ord_correct : forall m x, mem m x <-> ffix_ord x (Ffix m).
  (* membership relations in SPFunctor became order on ffix *)

  Variable ord_transtive : forall x y z (Rxy: clos_trans_n1 ffix_ord x y) (Ryz: clos_trans_n1 ffix_ord y z),
      clos_trans_n1 ffix_ord x z.

  Hypothesis ffix_ord_wf: well_founded ffix_ord.

  Hypothesis ffix_ord_c_wf : well_founded (clos_trans_n1 ffix_ord).
  (* well order *)

  Hypothesis ffix_des_ord : forall (x: ffix), PF (@less_ones _ (clos_trans_n1 ffix_ord) x).
  (* destruct with order *)

  Variable order_part : forall m x, mem m x -> (clos_trans_n1 ffix_ord) x (Ffix m).
  (* users don't need to know this *)

  Hypothesis des_ord_correct : forall (m : PF ffix),
      ffix_des_ord (Ffix m) = map_dep m (fun x r => w_ord _ (order_part m x r)).

(* induction principles with different forms *)

  Hypothesis ffix_ord_induction : forall x (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord x y -> P x) -> P y),
    P x.

  Hypothesis ffix_str_induction : forall x (P: ffix -> Prop)
        (STEP: forall y, (forall x, (clos_trans_n1 ffix_ord) x y -> P x) -> P y),
    P x.
    (* strong induction *)

  Hypothesis ffix_mem_induction : forall x (P: ffix -> Prop)
        (STEP: forall m (IND: forall y, mem m y -> P y), P (Ffix m)),
    P x.


(* recursive function *)

  Variable frec : forall T (FIX: forall m (FN: forall y, (clos_trans_n1 ffix_ord) y m -> T), T),
      ffix -> T.

  Variable frec_d: forall (P: ffix -> Type)
                          (FIX: forall m (FN: forall y, (clos_trans_n1 ffix_ord) y m -> P y), P m),
      forall x : ffix, P x.
  (* dependent functions *)

  Variable frec_p : forall T (f: PF T -> T),
      ffix -> T.
  (* primitive recursion : simple but not general *)


(* reduction rules for recursive functions *)

  Hypothesis frec_red : forall T
      (FIX: forall m (FN: forall y, (clos_trans_n1 ffix_ord) y m -> T), T) x,
    frec FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec FIX y).

  Hypothesis frec_d_red : forall (P: ffix -> Type)
      (FIX: forall m (FN: forall y, (clos_trans_n1 ffix_ord) y m -> P y), P m) x,
    frec_d P FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec_d P FIX y).

  Hypothesis frec_p_red : forall T (f: PF T -> T) m,
    frec_p f (Ffix m) = f (map (frec_p f) m).


(* tactics for reduction *)

  Ltac msimpl := repeat (autounfold;
                         repeat rewrite frec_red;
                         repeat rewrite frec_d_red;
                         repeat rewrite frec_p_red;
                         repeat rewrite des_ord_correct;
                         repeat rewrite des_correct2;
                         unfold id;
                         simpl).

  Ltac msimpl_in H := repeat (autounfold;
                              repeat rewrite frec_red in H;
                              repeat rewrite frec_p_red in H;
                              repeat rewrite frec_d_red in H;
                              repeat rewrite des_ord_correct in H;
                              repeat rewrite des_correct2 in H;
                              unfold id in H;
                              simpl in H).

  End inductive.

End INDUCTIVE.


Module Type COINDUCTIVE.

  Section coinductive.

  Variable PF : Type -> Type.
  Variable H : (FunctorData PF).
  Variable H0 : (SFunctorData PF).
  Variable SPF : (SPFunctor PF).

(* constructor and destructor *)

  Variable fcofix : Type. (* coinductive type *)

  Variable Fcofix : PF fcofix -> fcofix. (* constructor *)

  Variable fcofix_des : fcofix ->  PF fcofix. (* destructor *)

  Hypothesis Fcofix_inj : forall x1 x2 (EQ: Fcofix x1 = Fcofix x2), x1 = x2.
  (* constructors are injective *)

  Hypothesis c_des_correct1 : forall x, Fcofix (fcofix_des x) = x.

  Hypothesis c_des_correct2 : forall x, fcofix_des (Fcofix x) = x.
  (* these say that destructors are the inverse of constructors *)


(* for corecursive functions *)
(* we use mendler style corecursion *)

  Variable grd_fcofix : Type -> Type.

  Variable val : forall (A : Type), fcofix -> grd_fcofix A.

  Variable grd : forall (A : Type), PF (sum A (grd_fcofix A)) -> grd_fcofix A.
  (* constructors for grd_fcofix *)
  Arguments grd A p.

  Variable grd_fcofix_des : forall (A: Type),
      grd_fcofix A -> fcofix + (PF (sum A (grd_fcofix A))).
  (* destructors for grd_fcofix *)

  Hypothesis val_des_correct : forall A (x: fcofix),
      grd_fcofix_des (val A x) = inl x.

  Hypothesis grd_des_correct : forall A (f: PF (sum A (grd_fcofix A))),
      grd_fcofix_des (@grd A f) = inr f.
  (* destructros are the inverse of constructors *)

  Variable to_fcofix : forall A, (A -> grd_fcofix A) ->
                                 (sum A (grd_fcofix A)) -> fcofix.
  (* users don't need to know this function *)


  Variable fcorec : forall A, (A -> grd_fcofix A) -> (A -> fcofix).
  (* corecursive function!!! *)

  Variable fcorec_p : forall A (f: A -> PF A), A -> fcofix.
  (* primitive corecursion *)


(* reduction rules for corecursive functions *)

  Hypothesis fcorec_red : forall A (f: A -> grd_fcofix A) (a: A),
      fcofix_des (fcorec f a) = match (grd_fcofix_des (f a)) with
                                | inl x => fcofix_des x
                                | inr m => map (to_fcofix f) m end.
        
  Hypothesis to_fcofix_correct1 : forall A (f: A -> grd_fcofix A) a,
    to_fcofix f (inl a) = fcorec f a.

  Hypothesis to_fcofix_correct2 : forall A (f: A -> grd_fcofix A) x,
    to_fcofix f (inr (val A x)) = x.

  Hypothesis to_fcofix_correct3 : forall A (f: A -> grd_fcofix A) m,
    to_fcofix f (inr (@grd A m)) = Fcofix (map (to_fcofix f) m).

  Variable fcorec_p_red : forall A (f: A -> PF A) a,
    fcofix_des (fcorec_p f a) = map (fcorec_p f) (f a).


(* bisimilarity *)

  Hypothesis bsm_gen_mon : monotone2 (bsm_gen Fcofix).
  Hint Resolve bsm_gen_mon : paco.

  Hypothesis bsm_eq : forall (x1 x2 : fcofix), bsm Fcofix x1 x2 <-> x1 = x2.
  (* bisimilarity axiom.
     its proof relies on the bisimilarity axiom of universal functors *)


(* tactics for reduction *)

  Ltac csimpl := repeat (repeat rewrite c_des_correct2;
                         repeat rewrite val_des_correct;
                         repeat rewrite grd_des_correct;
                         repeat rewrite fcorec_red;
                         repeat rewrite fcorec_p_red;
                         repeat rewrite to_fcofix_correct1;
                         repeat rewrite to_fcofix_correct2;
                         repeat rewrite to_fcofix_correct3;
                         unfold id;
                         simpl).

  Ltac csimpl_in H := repeat (repeat rewrite c_des_correct2 in H;
                              repeat rewrite val_des_correct in H;
                              repeat rewrite grd_des_correct in H;
                              repeat rewrite fcorec_red in H;
                              repeat rewrite fcorec_p_red in H;
                              repeat rewrite to_fcofix_correct1 in H;
                              repeat rewrite to_fcofix_correct2 in H;
                              repeat rewrite to_fcofix_correct3 in H;
                              unfold id in H;
                              simpl in H).

  End coinductive.

End COINDUCTIVE.