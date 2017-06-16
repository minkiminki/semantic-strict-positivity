Require Import FunctionalExtensionality ProofIrrelevance ClassicalDescription.
Require Import ClassicalChoice ChoiceFacts.
Require Import Coq.Logic.Eqdep_dec.
Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.
Require Import ssp combinator fixpoint.

Ltac msimplp := repeat (try simpl; try setoid_rewrite mfix_fn_correct;
                       try setoid_rewrite mfix_destruct_correct1;
                       try setoid_rewrite mfix_destruct_correct2).

Ltac msimpl := repeat (try simpl; try rewrite mfix_fn_correct;
                       try rewrite mfix_destruct_correct1;
                       try rewrite mfix_destruct_correct2).

Module Tree.

Inductive tree : Type :=
| node : list tree -> tree.

Inductive well_founded : tree -> Prop :=
| wf_leaf : well_founded (node nil)
| wf_internal hd tl (WHD: well_founded hd) (WTL: well_founded (node tl)) :
                      well_founded (node (cons hd tl)).

Theorem tree_well_founded x : well_founded x.
Proof.
  induction x.
Abort.

End Tree.


Module Tree_SSP.

Definition tree_gen : SSPF.t := List_sspf.

Definition tree := Mfixpoint tree_gen.
Definition node (l: list tree) := Mfix_mk tree_gen l.

Inductive well_founded : tree -> Prop :=
| wf_leaf : well_founded (node nil)
| wf_internal hd tl (WHD: well_founded hd) (WTL: well_founded (node tl)) :
                      well_founded (node (cons hd tl)).

Theorem tree_well_founded x : well_founded x.
Proof.
  apply Mfixpoint_ind. simpl.
  induction m; intros.
  - apply wf_leaf.
  - dependent destruction IND.
    apply (wf_internal H (IHm IND)).
Qed.

End Tree_SSP.


Module Option_Nat.

Definition nat := Mfixpoint (Option_sspf).
Definition O := Mfix_mk Option_sspf None.
Definition S x := Mfix_mk Option_sspf (Some x).

Definition induction_principle n (P: nat -> Prop) (PO : P O) (PS : forall n, P n -> P (S n)) : P n.
Proof.
  apply (Mfixpoint_ind n).
  intros. simpl in IND. unfold option_pmap in IND.
  destruct m.
  - apply PS, IND.
  - apply PO.
Qed.  
  
Inductive le (n: nat) : nat -> Prop := 
| le_n : le n n
| le_S : forall m : nat, le n m -> le n (S m).

Definition lt n m := le (S n) m.

Inductive natural_order (n: nat) : nat -> Prop :=
| succ : natural_order n (S n). 

Lemma wf : well_founded natural_order.
Proof.
  unfold well_founded. intros.
  apply induction_principle.
  - constructor.
    intros.
    remember O.
    inversion H.
    subst.
    apply (Mfix_mk_inj) in H0.
    inversion H0.
  - intros.
    constructor.
    intros.
    remember (S n).
    inversion H0.
    inversion Heqm.
    subst.
    apply (Mfix_mk_inj) in H1. inversion H1.
    auto.
Qed.

Lemma wf2 : well_founded lt.
Proof.
  unfold well_founded. intros.
  apply (induction_principle).
  - constructor.
    intros.
    remember O.    
    inversion H.
    + subst.
      apply (Mfix_mk_inj) in H0.
      inversion H0.
    + subst.
      apply (Mfix_mk_inj) in H1.
      inversion H1.
  - intros.
    constructor.
    intros.
    remember (S n).
    inversion H0.
    + subst.
      apply (Mfix_mk_inj) in H1.
      inversion H1.      
      subst. auto.
    + subst.
      apply (Mfix_mk_inj) in H2.
      inversion H2.      
      subst.
      inversion H.
      unfold lt at 1 in H3.
      apply H3, H1.
Qed.      

Inductive lex : nat * nat -> nat * nat -> Prop := 
| lex_n : forall n m1 m2, lex (n, m1) (S n, m2)
| lex_S : forall n m, lex (n, m) (n, S m).

Lemma wf_lex : well_founded lex.
Proof.
  unfold well_founded.
  intros.
  destruct a.
  apply (induction_principle n).
  - constructor.
    intros.
    remember O.
    inversion H;
    subst.
    apply (Mfix_mk_inj) in H2.
    inversion H2.
    apply (induction_principle m0).
    + constructor.
      intros.
      remember O.
      inversion H0.
      subst.
      apply (Mfix_mk_inj) in H3.
      inversion H3.
      subst.
      apply (Mfix_mk_inj) in H4.
      inversion H4.
    + intros.
      constructor.
      intros.
      remember O. remember (S n0).
      inversion H1.
      subst.
      apply (Mfix_mk_inj) in H4.
      inversion H4.
      subst.
      apply (Mfix_mk_inj) in H5.
      inversion H5.
      subst.
      auto.
    - intros.
Abort.

Lemma trivalence : forall n m, le n m \/ lt m n.
Proof.
  intros.
Abort.

(* @jeehoonkang: use `Program Definition` *)

Definition fibonacci_gen (_: Option_sspf nat) 
           (x: Option_sspf (vfx Option_sspf Datatypes.nat)) :=
  match x with
  | None => 1
  | Some a =>
    match (mfix_destruct a) with
    | (None, _) => 1
    | (Some x', v') =>
      match (mfix_destruct x') with
      | (_, v'') => v'' + v' end end end.

Definition fibonacci := mfix_fnd fibonacci_gen.

Lemma fibonacci_0 : fibonacci O = 1.
Proof.
  unfold fibonacci, mfix_fnd, O.
  msimpl.
  auto.
Qed.

Lemma fibonacci_1 : fibonacci (S O) = 1.
Proof.
  unfold fibonacci, mfix_fnd, O, S.
  msimpl.
  auto.
Qed.

Lemma fibonacci_SS x : fibonacci (S (S x)) = fibonacci x + fibonacci (S x).
Proof.
  unfold fibonacci, mfix_fnd, O, S.
  msimpl.
  destruct (@mfix_destruct (Prod Option_sspf (Const Datatypes.nat))
        (@mfix_fn Option_sspf (vfx Option_sspf Datatypes.nat)
           (fun (mfx : option (Mfixpoint Option_sspf))
              (mvfx : option (vfx Option_sspf Datatypes.nat)) =>
            Mfix_mk (Prod Option_sspf (Const Datatypes.nat))
              (@pair (option (vfx Option_sspf Datatypes.nat)) Datatypes.nat mvfx
                 (fibonacci_gen mfx mvfx))) x)).
  auto.
Qed.
