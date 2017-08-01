Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor.

Program Definition id_SPFunctorMixin :=
  @SPFunctor.Mixin
    id id_functorMixin.(Functor.map) id_sFunctorMixin.(SFunctor.mem) id_sFunctorMixin.(SFunctor.rel)
    () Empty_set
    (fun _ x _ => inl x)
    _ _ _ _.
Next Obligation.
  eapply fapp in EQ; [|apply ()]. inv EQ. auto.
Qed.
Next Obligation.
  split; intros.
  - econstructor; [apply ()|].
    subst. constructor.
  - inv H. inv MEM. auto.
Qed.
Next Obligation.
  simplify. constructor; intros.
  - specialize (H ()). inv H. auto.
  - econstructor. auto.
Qed.
Canonical Structure id_SPFunctorType := spFunctorType _ id_SPFunctorMixin.


Program Definition option_SPFunctorMixin :=
  @SPFunctor.Mixin
    option option_functorMixin.(Functor.map) option_sFunctorMixin.(SFunctor.mem) option_sFunctorMixin.(SFunctor.rel)
    () ()
    (fun _ x _ =>
       match x with
       | Some x => inl x
       | None => inr ()
       end)
    _ _ _ _.
Next Obligation.
  destruct x1, x2; simplify; auto.
  - eapply fapp in EQ; [|apply ()]. inv EQ. auto.
  - eapply fapp in EQ; [|apply ()]. inv EQ.
  - eapply fapp in EQ; [|apply ()]. inv EQ.
Qed.
Next Obligation.
  destruct fx1; auto.
Qed.
Next Obligation.
  split; intros.
  - econstructor; [apply ()|].
    subst. constructor.
  - inv H. destruct fx; simplify; inv MEM; auto.
Qed.
Next Obligation.
  destruct fx1, fx2; simplify; auto; constructor; intros;
    repeat (match goal with
            | [H: () -> _ |- _] => specialize (H ())
            | [H: option_frel _ _ _ |- _] => inv H
            | [H: coproduct_rel _ _ _ _ _ |- _] => inv H
            | [|- option_frel _ _ _] => econstructor
            | [|- coproduct_rel _ _ _ _ _] => econstructor
            end; auto).
  econstructor.
Qed.
Canonical Structure option_SPFunctorType := spFunctorType _ option_SPFunctorMixin.


Program Definition prod_SPFunctorMixin (F1 F2 : SPFunctorType) :=
  @SPFunctor.Mixin
    (fun X => prod (F1 X) (F2 X)) (product_functorMixin F1 F2).(Functor.map) (product_sFunctorMixin F1 F2).(SFunctor.mem) (product_sFunctorMixin F1 F2).(SFunctor.rel)
    _ _
    _
    _ _ _ _.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Canonical Structure prod_SPFunctorType (F1 F2: SPFunctorType) := spFunctorType (product_sFunctorType F1 F2) (prod_SPFunctorMixin F1 F2).


Program Definition const_SPFunctorMixin (D: Type) :=
  @SPFunctor.Mixin
    (fun X => D) (const_functorMixin D).(Functor.map) (const_sFunctorMixin D).(SFunctor.mem) (const_sFunctorMixin D).(SFunctor.rel)
    _ _
    _
    _ _ _ _.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Canonical Structure const_SPFunctorType (D: Type) := spFunctorType (const_sFunctorType D) (const_SPFunctorMixin D).
