Set Implicit Arguments.

Require Import spec Functor SPFunctor inductive coinductive combinator paco.

Notation "p << q" := (ord_transitive p q) (at level 50, left associativity)
                       : ssp_scope.

Notation " x [ o ]" := (w_ord x o) (at level 50, right associativity)
                       : ssp_scope.

Notation "\> x" := (ffix_des x) (at level 50) : ssp_scope.

Notation "\>> x" := (ffix_des_ord x) (at level 50) : ssp_scope.

Notation "<\ x" := (Ffix _ x) (at level 50) : ssp_scope.

Notation "\\> x" := (fcofix_des x) (at level 50) : ssp_scope.

Notation "<\\ x" := (Fcofix _ x) (at level 50) : ssp_scope.

Lemma des_exist (PF : Type -> Type)`{SPF : SPFunctor PF} (x : ffix PF) :
  exists m, Ffix PF m = x.
Proof.
  exists (ffix_des x). apply des_correct1.
Qed.

Lemma cdes_exist (PF : Type -> Type)`{SPF : SPFunctor PF} (x : fcofix PF) :
  exists m, Fcofix PF m = x.
Proof.
  exists (fcofix_des x). apply c_des_correct1.
Qed.

Ltac sdestruct d :=
  match goal with
  | [ H : context[d] |- _] => revert H; sdestruct d; intro H
  | [ |- _] => let x := fresh "x" in
               let e := fresh "e" in (try (destruct (cdes_exist d) as [x e];
                                      destruct e; try clear d));
                                     (try (destruct (des_exist d) as [x e];
                                      destruct e; try clear d))
  end.

Ltac eta_expand_all d := 
  match goal with
  | [ H : context[d] |- _] => revert H; eta_expand_all d; intro H
  | [ |- _] => (try destruct (des_correct1 d));
               (try destruct (c_des_correct1 d))
  end.

Ltac eta_expand_in d H := (try rewrite <- (des_correct1 d) in H);
                          (rewrite <- (c_des_correct1 d) in H).

Ltac eta_expand d := (try rewrite <- (des_correct1 d));
                     (rewrite <- (c_des_correct1 d)).

Ltac mem_induction d :=
  match goal with
  | [ H : context[d] |- _] => revert H; mem_induction d; intro H
  | [ |- _] => apply (ffix_mem_induction d);
               let x := fresh "x" in
               let IND := fresh "IND" in intros x IND; try clear d
  end.

Ltac ord_induction d :=
  match goal with
  | [ H : context[d] |- _] => revert H; ord_induction d; intro H
  | [ |- _] => apply (ffix_ord_induction d);
               let x := fresh "x" in
               let IND := fresh "IND" in intros x IND; try clear d
  end.

Ltac str_induction d :=
  match goal with
  | [ H : context[d] |- _] => revert H; str_induction d; intro H
  | [ |- _] => apply (ffix_str_induction d); 
               let x := fresh "x" in
               let IND := fresh "IND" in intros x IND; try clear d
  end.

Ltac mauto := try (msimpl; csimpl; auto; fail).

Ltac minversion H := (try apply Ffix_inj in H); (try apply Fcofix_inj in H);
                     (try inversion H).
