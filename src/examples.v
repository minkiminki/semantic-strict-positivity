Set Implicit Arguments.
Set Automatic Coercions Import.

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

Definition bsm' {PF} `{SPF : SPFunctor PF} x1 x2 := @bsm PF H H0 SPF (fcofix PF) (Fcofix PF) x1 x2.

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
  
Open Scope ssp_scope.

Module opt_nat.

Definition mynat := ffix option.
Definition myO := Ffix option None.
Definition myS x := Ffix option (Some x).
Hint Unfold myS myO.

Definition fibonacci := frec (fun (m : mynat) f =>
                                match \>> m with
                                | None => 1
                                | Some (m' [p1]) =>
                                  match \>> m' with
                                  | None => 1
                                  | Some (m'' [p2]) => f m'' (p2<<p1) + f m' p1
                                  end end).
Hint Unfold fibonacci.

Goal forall n, fibonacci (myS (myS n)) = fibonacci n + fibonacci (myS n).
Proof.
  intros. mauto.
Qed.

Fixpoint to_mynat n :=
  match n with
  | O => <\ None
  | S n' => <\ (Some (to_mynat n')) end.

Goal (fibonacci (to_mynat 3)) = 3.
  mauto.
Qed.

Goal forall n m, myS (myS n) = myS (myS m) -> n = m.
Proof.
  intros.
  apply Ffix_inj in H. inversion H.
  apply Ffix_inj in H1. inversion H1.
  reflexivity.
Qed.

Definition to_nat := frec (fun (n: mynat) f =>
                             match \>> n with
                             | None => 0
                             | Some (n' [pf]) => (f n' pf) + 1 end).
Hint Unfold to_nat.

Lemma sssss : to_nat (myS (myS (myS myO))) = 3.
Proof.
  mauto.
Qed.

Definition foo : mynat -> nat :=
  fun n =>
    match \> n with
    | None => 0
    | Some n' => 0 end.

Goal forall n, foo (myS n) = 0 -> foo n = 0.
Proof.
  intros. sdestruct n.
  destruct x; unfold foo; mauto.
Qed.

Definition plus m := frec (fun (n: mynat) f =>
                             match \>> n with
                             | None => m
                             | Some (n' [pf]) => myS (f n' pf) end).
Hint Unfold plus.

Goal forall n, plus n myO = n.
Proof.
  intros. mauto.
Qed.

Lemma plus_0n n : plus myO n = n.
Proof.
  mem_induction n; destruct x.
  - simplify. msimpl. rewrite IND; auto.
  - mauto.
Qed.

Lemma plus_Smn n m : plus (myS m) n = myS (plus m n).
Proof.
  mem_induction n. destruct x.
  - msimpl. simplify. rewrite IND; mauto.
  - mauto.
Qed.

Goal forall n m, plus n m = plus m n.
Proof.
  intros. mem_induction n; destruct x; intros.
  - msimpl. simplify. rewrite <- (IND f); auto.
    apply plus_Smn.
  - msimpl. apply plus_0n.
Qed.

End opt_nat.


Section stream.

Variable A: Type.

Definition stream_gen := Prod (Const A) Ident.

Definition stream := fcofix stream_gen.

Definition Cons n x := Fcofix stream_gen (n, x).

Definition hd (x: stream) :=
match \\> x with
| (n, x') => n end.

Definition tl (x: stream) :=
match \\> x with
| (n, x') => x' end.


End stream.

Hint Unfold Cons hd tl.

Definition enumeration : nat -> stream nat :=
  fcorec (fun n : nat => grd nat (n, inl n)).

Definition inf_true : fcofix (stream_gen bool)
  := fcorec (fun u: unit => grd unit (true, inl tt)) tt. 

Hint Unfold enumeration inf_true.

Lemma inf_true_c : hd inf_true = true.
Proof.
  mauto.
Qed.


Lemma ssssss : hd (tl (tl (tl (tl (tl inf_true))))) = true.
Proof.
  mauto.
Qed.

Module Inftree.

Definition tree_gen := Prod (Const nat) (Prod Ident Ident).

Definition inftree := fcofix tree_gen.

Definition node n x1 x2 := Fcofix tree_gen (n, (x1, x2)).
Hint Unfold inftree node.

Arguments grd_fcofix PF {H} {H0} {SPF} A.

Definition one_gen : bool -> grd_fcofix tree_gen bool := (fun b : bool =>
                                                            match b with
                                                            | true => grd bool (1, (inl true, inl false))
                                                            | false => grd bool (2, (inl true, inl false)) end).

Definition one : inftree := fcorec one_gen true.

Definition eins_gen : bool -> grd_fcofix tree_gen bool := (fun b: bool =>
                                                             match b with
                                                             | true => grd bool (1, (inl true, inr (grd bool (2, (inl true, inl false)))))
                                                             | false => grd bool (2, (inl true, inl false)) end).

Definition eins : inftree := fcorec eins_gen true.

Lemma teq'_two_one : forall r,
    (r (fcorec one_gen false) (fcorec eins_gen false) : Prop)
    -> paco2 (bsm_gen (Fcofix tree_gen)) r (fcorec one_gen true) (fcorec eins_gen true).
Proof.
  intros. pcofix CIH.
  pfold.
  eta_expand (fcorec one_gen true). eta_expand (fcorec eins_gen true).
  constructor. csimpl. split; [auto|].
  split; [right; auto |].
  right. eta_expand_in (fcorec eins_gen false) H. csimpl_in H. apply H.
Qed.

Lemma teq'_one_two : forall r,
  (r (fcorec one_gen true) (fcorec eins_gen true) : Prop)
  -> paco2 (bsm_gen (Fcofix tree_gen)) r (fcorec one_gen false) (fcorec eins_gen false).
Proof.
  intros; pcofix CIH.
  pfold.
  eta_expand (fcorec one_gen false). eta_expand (fcorec eins_gen false).
  constructor. csimpl. tauto.
Qed.

Theorem teq'_eins : bsm' one eins.
Proof.
  pcofix CIH.
  pmult; apply teq'_two_one, teq'_one_two, CIH.
Qed.

Theorem teq'_zwei : bsm' (fcorec one_gen false) (fcorec eins_gen false).
Proof.
  pcofix CIH.
  pmult; apply teq'_one_two, teq'_two_one, CIH.
Qed.

End Inftree.

