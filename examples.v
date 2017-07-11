Require Import Program.
Set Implicit Arguments.
Set Automatic Coercions Import.
Require Import ssp combinator fixpoint.

Arguments proj1_sig {A P} e.
Arguments projT1 {A P} x.
Arguments morder {M y} x OR.

Opaque Mfixpoint Mfix_destruct Mfix_mk Mfix_destruct_ord Mfixpoint_fn
       Mfixpoint_fn_depend destruct_order.

Ltac mdestruct x x' := try (rewrite <- (destruct_correct1 x) in *; remember (Mfix_destruct x) as x' eqn : _EQ; clear _EQ; clear x; simpl in x').

Ltac minduction x := apply (Mfixpoint_ind' x); intro; intro.
Ltac minductionr x := apply (Mfixpoint_indr x); intro; intro.
Ltac msinduction x := apply (Mfixpoint_s_ind x); intro; intro.

Ltac minversion H x y := remember x as _a eqn : _EQ1; remember y as _b eqn : _EQ2; 
apply mfix_mk_inj in H;
inversion H; repeat rewrite _EQ2 in *; repeat rewrite _EQ1 in *; clear _EQ2; clear _b; clear _EQ1; clear _a.

Ltac minversion2 H x y := remember x as _a eqn : _EQ1; remember y as _b eqn : _EQ2; inversion H; repeat rewrite _EQ2 in *; repeat rewrite _EQ1 in *; clear _EQ2; clear _b; clear _EQ1; clear _a.

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
  minductionr x; induction m; simpl in *.
  - constructor.
  - apply wf_internal.
    + apply IND. constructor. constructor.
    + apply IHm.
      intros. apply IND.
      apply inr, X.
Qed.

End Tree_SSP.


Section opt_nat.

Definition nat := Mfixpoint Option_sspf.
Definition O := Mfix_mk Option_sspf None.
Definition S x := Mfix_mk Option_sspf (Some x).

Hint Unfold O S.

Definition to_nat := Mfixpoint_fn (fun (n: nat) f =>
  match Mfix_destruct_ord n with
  | None => 0
  | Some (morder n' pf) => (f n' pf) + 1 end).

Definition fibonacci := Mfixpoint_fn (fun (n: nat) f =>
  match Mfix_destruct_ord n with
  | None => 1
  | Some (morder n' pf1) =>
    match Mfix_destruct_ord n' with
    | None => 1
    | Some (morder n'' pf2) => (f n' pf1) + (f n'' (link_order pf2 pf1)) end end).

Fixpoint to_nat2 (n: Datatypes.nat) : nat :=
  match n with
  | Datatypes.O => O
  | Datatypes.S n' => S (to_nat2 n') end.

Definition ackermann := Mfixpoint_fn (fun (n: nat) f =>
  match Mfix_destruct_ord n with
  | None => (fun m => Mfix_mk Option_sspf (Some m))
  | Some (morder n' pf1) =>
    Mfixpoint_fn (fun (m: nat) g =>
      match Mfix_destruct_ord m with
      | None => f n' pf1 (Mfix_mk Option_sspf (Some (Mfix_mk Option_sspf None)))
      | Some (morder m' pf2) => f n' pf1 (g m' pf2) end)
  end).

(*
Eval compute in (fibonacci (to_nat2 20)).

Eval compute in (fibonacci (S (S (S (S (S O)))))).
 = 8

Eval compute in (to_nat (S (S (S (S O))))). 
 = 4

Eval compute in (to_nat (ackermann (S (S O)) (S (S O)))).
Eval compute in (ack 2 2).

*)

Lemma fibonacci_c_2 : forall n, fibonacci (S (S n)) = fibonacci (S n) + fibonacci n.
Proof.
  intros. unfold fibonacci, S.
  msimpl. auto.
Qed.

Lemma ackermann_c_1 : forall n, ackermann O n = S n.
Proof.
  intros. unfold ackermann, O, S.
  msimpl. auto.
Qed.

Lemma ackermann_c_2 : forall m, ackermann (S m) O = ackermann m (S O).
Proof.
  intros. unfold ackermann, O, S.
  msimpl. auto. 
Qed.

Lemma ackermann_c_3 : forall m n, ackermann (S m) (S n) = ackermann m (ackermann (S m) n).
Proof.
  intros. unfold ackermann, O, S.
  msimpl. auto. 
Qed.

(* TODO induction and inversion tactic*)

Definition pred (n: nat) :=
  match Mfix_destruct n with
  | None => Mfix_mk Option_sspf None
  | Some x => x end.

Definition evenb := Mfixpoint_fn (fun (n:nat) f =>
  match Mfix_destruct_ord n with
  | None => true
  | Some (morder n' pf1) =>
    match Mfix_destruct_ord n' with
    | None => false
    | Some (morder n'' pf2) => f n'' (link_order pf2 pf1) end end).

Definition oddb (n:nat) : bool := negb (evenb n).

Definition plus := Mfixpoint_fn (fun (n : nat) f =>
(fun (m : nat) =>
  match Mfix_destruct_ord n with
  | None => m
  | Some (morder n' pf) => Mfix_mk Option_sspf (Some (f n' pf m)) end)).

Definition mult := Mfixpoint_fn (fun (n: nat) f =>
(fun (m : nat) =>
  match Mfix_destruct_ord n with
  | None => Mfix_mk Option_sspf None
  | Some (morder n' pf) => plus m (f n' pf m)
  end)).

Definition minus := Mfixpoint_fn (fun (n: nat) f =>
(fun (m: nat) => 
  match Mfix_destruct_ord n with
  | None => Mfix_mk Option_sspf None
  | Some (morder n' pf) =>
    match Mfix_destruct m with
    | None => n
    | Some m' => f n' pf m' end end)).

Definition exp (base: nat) := Mfixpoint_fn (fun (power : nat) f =>
  match Mfix_destruct_ord power with
  | None => Mfix_mk Option_sspf (Some (Mfix_mk Option_sspf None))
  | Some (morder p pf) => mult base (f p pf) end).

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Theorem plus_n_O : forall n:nat, n = n + (Mfix_mk Option_sspf None).
Proof.
  intro n. minductionr n. destruct m; unfold plus in *; simpl in IND.
  - specialize (IND m (eq_refl m)).
    rewrite IND at 1. msimpl. auto.
  - msimpl. auto.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  Mfix_mk Option_sspf (Some (n + m)) = n + (Mfix_mk Option_sspf (Some m)).
Proof.
  intro. minductionr n. destruct m; unfold plus in *.
  - msimpl. intro.
    specialize (IND m (eq_refl m) m0). msimpl_in IND.
    rewrite IND. auto.
  - msimpl. auto.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intro. minductionr n; destruct m.
  - intro. unfold plus. msimpl. fold plus.
    rewrite IND.
    apply plus_n_Sm.
    constructor.
  - intro. unfold plus. msimpl.
    apply plus_n_O.
Qed.

Inductive lt : nat -> nat -> Prop :=
| lt_base n : lt n (S n)
| lt_stem n m : lt n m -> lt n (S m).

Definition bbb (n: nat) :=
  match Mfix_destruct n with
  | None => 1
  | Some n' => 1 end.

Lemma bbb1 n : bbb n = 1.
Proof.
  mdestruct n a. destruct a; unfold bbb; msimpl; auto.
Qed.

Lemma sss n : S (S n) = S O -> False.
Proof.
  intros. apply mfix_mk_inj in H.
  inversion H.
Qed.

End opt_nat.