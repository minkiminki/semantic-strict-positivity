Set Implicit Arguments.

Require Import Notations.
Require Import Logic.
Require Import Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Relations.Relation_Operators.

Require Import index.

Section Well_founded.

  Variable C : Type.
  Variable A : iType C.
  Variable R : forall {i}, A i -> forall {j}, A j -> Prop.

  Inductive iAcc {i} (x: A i) : Prop :=
  | iAcc_intro : (forall j (y: A j), R y x -> @iAcc j y) -> iAcc x.

  Lemma iAcc_inv : forall i (x:A i), iAcc x -> forall j (y:A j), R y x -> iAcc y.
  Proof.
    intros.
    destruct H.
    apply (H _ _ H0).
  Defined.

  Definition iwell_founded := forall i (a:A i), iAcc a.

  Hypothesis iRwf : iwell_founded.

  Theorem iwell_founded_induction_type :
    forall P: forall {i}, (A i) -> Type,
      (forall i (x:A i), (forall j (y:A j), R y x -> P y) -> P x) -> forall i (a:A i), P a.
  Proof.
    intros. apply iAcc_rect.
    - intros. apply X. apply X0.
    - apply iRwf.
  Defined.

  Theorem iwell_founded_induction :
    forall P: forall {i}, (A i) -> Set,
      (forall i (x:A i), (forall j (y:A j), R y x -> P y) -> P x) -> forall i (a:A i), P a.
  Proof.
    intro. apply (iwell_founded_induction_type P).
  Defined.

  Theorem iwell_founded_ind :
    forall P: forall {i}, (A i) -> Prop,
      (forall i (x:A i), (forall j (y:A j), R y x -> P y) -> P x) -> forall i (a:A i), P a.
  Proof.
    intro. apply (iwell_founded_induction_type P).
  Defined.

  Section FixPoint.

    Variable P : forall i, A i -> Type.
    Variable F : forall {i} (x:A i), (forall j (y:A j), R y x -> P y) -> P x.

    Fixpoint iFix_F i (x:A i) (a:iAcc x) : P x :=
      F (fun j (y:A j) (h:R y x) => iFix_F (iAcc_inv a h)).

    Scheme iAcc_inv_dep := Induction for iAcc Sort Prop.

    Lemma iFix_F_eq :
      forall i (x:A i) (r:iAcc x),
        F (fun j (y:A j) (p:R y x) => iFix_F (x:=y) (iAcc_inv r p)) = iFix_F (x:=x) r.
    Proof.
      intros. destruct r. auto.
    Defined.

    Definition iFix i (x:A i) := iFix_F (iRwf x).

    Lemma iF_ext :
      forall i (x:A i) (f g:forall j (y:A j), R y x -> P y),
        (forall j (y:A j) (p:R y x), f _ y p = g _ y p) -> F f = F g.
    Proof.
      intros.
      replace g with f. reflexivity.
      extensionality j. extensionality y. extensionality p.
      apply H.
    Qed.

    Lemma iFix_F_inv : forall i (x:A i) (r s:iAcc x), iFix_F r = iFix_F s.
    Proof.
      fix 4.
      intros. destruct r, s.
      simpl. apply iF_ext. intros.
      apply iFix_F_inv.
    Qed.

    Lemma iFix_eq : forall i (x:A i), iFix x = F (fun j (y:A j) (p:R y x) => iFix y).
    Proof.
      unfold iFix. intros.
      destruct (iRwf x). simpl. apply iF_ext.
      intros. apply iFix_F_inv.
    Qed.

  End FixPoint.

End Well_founded.

Arguments iwell_founded {C} {A} R.
Arguments iAcc {C} {A} R {i}.

Section Transitive_Closure.

  Variable C : Type.
  Variable A : iType C.
  Variable R : forall {i}, A i -> forall {j}, A j -> Prop.

  Inductive iclos_transn1 : forall i (x: A i) j (y : A j), Prop :=
  | itn1_step {i} (x: A i) {j} (y : A j) : R x y -> iclos_transn1 x y
  | itn1_trans {i} (x: A i) {j} (y : A j) {k} (z : A k)
    : iclos_transn1 x y -> R y z -> iclos_transn1 x z.

  Lemma iclos_transn1_transitive i j k (x : A i) (y : A j) (z : A k) :
    iclos_transn1 x y -> iclos_transn1 y z -> iclos_transn1 x z.
  Proof.
    intros. revert x H. induction H0; intros.
    - eapply itn1_trans; eauto.
    - eapply itn1_trans; auto. 
  Defined.

  Lemma wf_iclos_trans : iwell_founded R -> iwell_founded iclos_transn1.
  Proof.
    intro.
    unfold iwell_founded.
    apply iFix with (R := R); auto. 
    intros.
    constructor.
    intros. destruct H1.
    - apply H0, H1. 
    - specialize (H0 _ _ H2). destruct H0. auto.
  Defined.

End Transitive_Closure.

Arguments iclos_transn1 {C} {A} R.

Inductive less_ones C {X : C -> Type} (R : forall i, X i -> forall j, X j -> Prop)
          {j} (y : X j) : C -> Type :=
| w_ord i (x : X i) (ORD: R _ x _ y) : less_ones R y i.
Arguments less_ones {C} {X} {R} {j}.
Arguments w_ord {C} {X} {R} {j} {y} {i} x ORD.
