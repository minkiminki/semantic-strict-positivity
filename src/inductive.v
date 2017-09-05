Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor spec.

Section inductive.

  Variable PF : Type -> Type.
  Context `{SPF : SPFunctor PF}.

  Definition ffix : Type. Admitted. (* inductive type *)

  Definition Ffix : PF ffix -> ffix. Admitted. (* constructor *)

  Definition ffix_des : ffix -> PF ffix. Admitted. (* destructor *)

  Definition Ffix_inj : forall x1 x2 (EQ: Ffix x1 = Ffix x2), x1 = x2. Admitted.
  (* constructors are injective *)

  Definition des_correct1 : forall x, Ffix (ffix_des x) = x. Admitted.

  Definition des_correct2 : forall x, ffix_des (Ffix x) = x. Admitted.
  (* these say that destructors are the inverse of constructors *)

(* order and induction principle *)

  Definition ffix_ord : ffix -> ffix -> Prop. Admitted. (* order on ffix *)

  Definition ffix_ord_c := @clos_trans_n1 ffix ffix_ord. (* closure of ffix_ord *)

  Definition ord_correct : forall m x, SPF.(mem) m x <-> ffix_ord x (Ffix m). Admitted.
  (* membership relations in SPFunctor became order on ffix *)

  Definition ord_transitive : forall x y z (Rxy: ffix_ord_c x y) (Ryz: ffix_ord_c y z),
      ffix_ord_c x z. Admitted.

  Definition ffix_ord_wf: well_founded ffix_ord. Admitted.

  Definition ffix_ord_c_wf : well_founded ffix_ord_c. Admitted.
  (* well order *)

  Definition ffix_des_ord : forall (x: ffix), PF (@less_ones ffix ffix_ord_c x). Admitted.
  (* destruct with order *)

  Definition order_part : forall m x, SPF.(mem) m x -> ffix_ord_c x (Ffix m). Admitted.
  (* users don't need to know this *)

  Definition des_ord_correct : forall (m : PF ffix),
      ffix_des_ord (Ffix m) = SPF.(map_dep) m (fun x r => w_ord _ (order_part m x r)). Admitted.
(* induction principles with different forms *)

  Definition ffix_ord_induction : forall x (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord x y -> P x) -> P y),
    P x. Admitted.

  Definition ffix_str_induction : forall x (P: ffix -> Prop)
        (STEP: forall y, (forall x, ffix_ord_c x y -> P x) -> P y),
    P x. Admitted.
    (* strong induction *)

  Definition ffix_mem_induction : forall x (P: ffix -> Prop)
        (STEP: forall m (IND: forall y, SPF.(mem) m y -> P y), P (Ffix m)),
    P x. Admitted.

(* recursive function *)

  Definition frec : forall T (FIX: forall m (FN: forall y, ffix_ord_c y m -> T), T),
      ffix -> T. Admitted. 

  Definition frec_d: forall (P: ffix -> Type)
                          (FIX: forall m (FN: forall y, ffix_ord_c y m -> P y), P m),
      forall x : ffix, P x. Admitted.
  (* dependent functions *)

  Definition frec_p : forall T (f: PF T -> T),
      ffix -> T. Admitted.
  (* primitive recursion : simple but not general *)


(* reduction rules for recursive functions *)

  Definition frec_red : forall T
      (FIX: forall m (FN: forall y, ffix_ord_c y m -> T), T) x,
    frec FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec FIX y). Admitted.

  Definition frec_d_red : forall (P: ffix -> Type)
      (FIX: forall m (FN: forall y, ffix_ord_c y m -> P y), P m) x,
    frec_d P FIX (Ffix x) = FIX (Ffix x) (fun y _ => frec_d P FIX y). Admitted.

  Definition frec_p_red : forall T (f: PF T -> T) m,
    frec_p f (Ffix m) = f (SPF.(map) (frec_p f) m). Admitted.

End inductive.

Global Opaque ffix Ffix ffix_des Ffix_inj des_correct1 des_correct2 ffix_ord ord_correct ord_transitive ffix_ord_wf ffix_ord_c_wf ffix_des_ord order_part des_ord_correct order_part des_ord_correct ffix_ord_induction ffix_str_induction ffix_mem_induction frec frec_d frec_p frec_red frec_d_red frec_p_red.

Ltac msimpl := repeat (autounfold;
                       repeat rewrite frec_red;
                       repeat rewrite frec_d_red;
                       repeat rewrite frec_p_red;
                       repeat rewrite des_ord_correct;
                       repeat rewrite des_correct2;
                       repeat unfold id;
                       simpl).

Ltac msimpl_in H := repeat (autounfold in H;
                            repeat rewrite frec_red in H;
                            repeat rewrite frec_p_red in H;
                            repeat rewrite frec_d_red in H;
                            repeat rewrite des_ord_correct in H;
                            repeat rewrite des_correct2 in H;
                            repeat unfold id in H;
                            simpl in H).

Arguments ffix PF {SPF}.
Arguments Ffix PF {SPF}.
