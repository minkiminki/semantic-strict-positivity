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

Module Type INDUCTIVE.

  Variable ffix : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, Type. (* inductive type *)

  Variable Ffix : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, PF ffix -> ffix. (* constructor *)

  Variable ffix_des : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, ffix -> PF ffix. (* destructor *)

  Hypothesis Ffix_inj : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x1 x2 (EQ: Ffix x1 = Ffix x2), x1 = x2.
  (* constructors are injective *)

  Hypothesis des_correct1 : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x, Ffix (ffix_des x) = x.

  Hypothesis des_correct2 : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x, ffix_des (Ffix x) = x.
  (* these say that destructors are the inverse of constructors *)


(* order and induction principle *)

  Variable ffix_ord : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, ffix -> ffix -> Prop. (* order on ffix *)

  Hypothesis ord_correct : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall m x, mem m x <-> ffix_ord x (Ffix m).
  (* membership relations in SPFunctor became order on ffix *)

  Variable ord_transtive : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x y z (Rxy: clos_trans_n1 (@ffix_ord PF _ _ _) x y) (Ryz: clos_trans_n1 (@ffix_ord PF _ _ _) y z),
      clos_trans_n1 (@ffix_ord PF _ _ _) x z.

  Hypothesis ffix_ord_wf: forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, well_founded (@ffix_ord PF _ _ _).

  Hypothesis ffix_ord_c_wf : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, well_founded (clos_trans_n1 (@ffix_ord PF _ _ _)).
  (* well order *)

  Hypothesis ffix_des_ord : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall (x: ffix), PF (@less_ones _ (clos_trans_n1 (@ffix_ord PF _ _ _)) x).
  (* destruct with order *)

  Variable order_part : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall m x, mem m x -> (clos_trans_n1 (@ffix_ord PF _ _ _)) x (Ffix m).
  (* users don't need to know this *)

  Hypothesis des_ord_correct : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall (m : PF ffix),
      ffix_des_ord (Ffix m) = map_dep m (fun x r => w_ord _ (order_part m x r)).

(* induction principles with different forms *)

  Hypothesis ffix_ord_induction : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord x y -> P x) -> P y),
    P x.

  Hypothesis ffix_str_induction : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x (P: ffix -> Prop)
        (STEP: forall y, (forall x, (clos_trans_n1 (@ffix_ord PF _ _ _)) x y -> P x) -> P y),
    P x.
    (* strong induction *)

  Hypothesis ffix_mem_induction : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x (P: ffix -> Prop)
        (STEP: forall m (IND: forall y, mem m y -> P y), P (Ffix m)),
    P x.


(* recursive function *)

  Variable frec : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall T (FIX: forall m (FN: forall y, (clos_trans_n1 (@ffix_ord PF _ _ _)) y m -> T), T),
      ffix -> T.

  Variable frec_d: forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall (P: ffix -> Type)
                          (FIX: forall m (FN: forall y, (clos_trans_n1 (@ffix_ord PF _ _ _)) y m -> P y), P m),
      forall x : ffix, P x.
  (* dependent functions *)

  Variable frec_p : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall T (f: PF T -> T),
      ffix -> T.
  (* primitive recursion : simple but not general *)


(* reduction rules for recursive functions *)

  Hypothesis frec_red : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall T
      (FIX: forall m (FN: forall y, (clos_trans_n1 (@ffix_ord PF _ _ _)) y m -> T), T) x,
    frec FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec FIX y).

  Hypothesis frec_d_red : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall (P: ffix -> Type)
      (FIX: forall m (FN: forall y, (clos_trans_n1 (@ffix_ord PF _ _ _)) y m -> P y), P m) x,
    frec_d P FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec_d P FIX y).

  Hypothesis frec_p_red : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall T (f: PF T -> T) m,
    frec_p f (Ffix m) = f (map (frec_p f) m).

End INDUCTIVE.


Module Type COINDUCTIVE.

(* constructor and destructor *)

  Variable fcofix : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, Type. (* coinductive type *)

  Variable Fcofix : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, PF fcofix -> fcofix. (* constructor *)

  Variable fcofix_des : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, fcofix ->  PF fcofix. (* destructor *)

  Hypothesis Fcofix_inj : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x1 x2 (EQ: Fcofix x1 = Fcofix x2), x1 = x2.
  (* constructors are injective *)

  Hypothesis c_des_correct1 : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x, Fcofix (fcofix_des x) = x.

  Hypothesis c_des_correct2 : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall x, fcofix_des (Fcofix x) = x.
  (* these say that destructors are the inverse of constructors *)


(* for corecursive functions *)
(* we use mendler style corecursion *)

  Variable grd_fcofix : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, Type -> Type.

  Variable val : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall (A : Type), fcofix -> grd_fcofix A.

  Variable grd : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall (A : Type), PF (sum A (grd_fcofix A)) -> grd_fcofix A.
  (* constructors for grd_fcofix *)

  Variable grd_fcofix_des : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall (A: Type),
      grd_fcofix A -> fcofix + (PF (sum A (grd_fcofix A))).
  (* destructors for grd_fcofix *)

  Hypothesis val_des_correct : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A (x: fcofix),
      grd_fcofix_des (val A x) = inl x.

  Hypothesis grd_des_correct : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A (f: PF (sum A (grd_fcofix A))),
      grd_fcofix_des (grd A f) = inr f.
  (* destructros are the inverse of constructors *)

  Variable to_fcofix : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A, (A -> grd_fcofix A) ->
                                 (sum A (grd_fcofix A)) -> fcofix.
  (* users don't need to know this function *)


  Variable fcorec : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A, (A -> grd_fcofix A) -> (A -> fcofix).
  (* corecursive function!!! *)

  Variable fcorec_p : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A (f: A -> PF A), A -> fcofix.
  (* primitive corecursion *)


(* reduction rules for corecursive functions *)

  Hypothesis fcorec_red : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A (f: A -> grd_fcofix A) (a: A),
      fcofix_des (fcorec f a) = match (grd_fcofix_des (f a)) with
                                | inl x => fcofix_des x
                                | inr m => map (to_fcofix f) m end.
        
  Hypothesis to_fcofix_correct1 : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A (f: A -> grd_fcofix A) a,
    to_fcofix f (inl a) = fcorec f a.

  Hypothesis to_fcofix_correct2 : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A (f: A -> grd_fcofix A) x,
    to_fcofix f (inr (val A x)) = x.

  Hypothesis to_fcofix_correct3 : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A (f: A -> grd_fcofix A) m,
    to_fcofix f (inr (grd A m)) = Fcofix (map (to_fcofix f) m).

  Variable fcorec_p_red : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall A (f: A -> PF A) a,
    fcofix_des (fcorec_p f a) = map (fcorec_p f) (f a).

(* bisimilarity *)

  Hypothesis bsm_gen_mon : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, monotone2 (bsm_gen (@Fcofix PF _ _ _)).
  Hint Resolve bsm_gen_mon : paco.

  Definition bsm PF `{SPFunctor PF} x1 x2 := paco2 (bsm_gen (@Fcofix PF _ _ _)) bot2 x1 x2.

  Hypothesis bsm_eq : forall PF `{H : FunctorData PF} `{H0 : @SFunctorData PF _} `{SPF : @SPFunctor PF _ _}, forall (x1 x2 : fcofix), bsm x1 x2 <-> x1 = x2.
  (* bisimilarity axiom.
     its proof relies on the bisimilarity axiom of universal functors *)


(* tactics for reduction *)

End COINDUCTIVE.