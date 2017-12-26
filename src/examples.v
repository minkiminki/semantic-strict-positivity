Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import spec Functor SPFunctor inductive coinductive combinator paco tactics.

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

Definition ackermann := frec (fun (n: mynat) f =>
match \>> n with
| None => (fun m => myS m)
| Some (n' [pf1]) =>
  frec (fun (m: mynat) g =>
  match \>> m with
  | None => f n' pf1 (myS myO)
  | Some (m' [pf2]) => f n' pf1 (g m' pf2) end)
end).
Hint Unfold ackermann.

Goal forall n, fibonacci (myS (myS n)) = fibonacci n + fibonacci (myS n).
Proof.
  intros. mauto.
Qed.

Goal forall n m, myS (myS n) = myS (myS m) -> n = m.
Proof.
  intros. unfold myS in *.
  minversion H. minversion H1. auto.
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

Goal to_nat (ackermann (myS (myS myO)) (myS (myS myO))) = 7.
Proof.
  autounfold.
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

Global Instance stream_gen_SPF : SPFunctor stream_gen.
Proof.
  unfold stream_gen. apply prod_SPFunctor.
  apply const_SPFunctor. apply id_SPFunctor.
Qed.  

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

Definition one_gen : bool -> grd_fcofix tree_gen bool :=
  (fun b : bool =>
     match b with
     | true => grd bool (1, (inl true, inl false))
     | false => grd bool (2, (inl true, inl false)) end).

Definition one : inftree := fcorec one_gen true.

Definition eins_gen : bool -> grd_fcofix tree_gen bool :=
  (fun b: bool =>
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

Theorem teq'_eins : bsm one eins.
Proof.
  pcofix CIH.
  pmult; apply teq'_two_one, teq'_one_two, CIH.
Qed.

Theorem teq'_zwei : bsm (fcorec one_gen false) (fcorec eins_gen false).
Proof.
  pcofix CIH.
  pmult; apply teq'_one_two, teq'_two_one, CIH.
Qed.

End Inftree.

Module list_tree.

Inductive tree :=
| node : list tree -> tree.

Inductive well_founded : tree -> Prop :=
| wf_leaf : well_founded (node nil)
| wf_internal hd tl (WHD: well_founded hd) (WTL: well_founded (node tl)) :
                      well_founded (node (cons hd tl)).

Theorem tree_well_founded x : well_founded x.
Proof.
  induction x.
Abort.

End list_tree.

Module list_tree_ssp.

Definition tree := ffix list.

Definition node (l : list tree) := Ffix list l.
Hint Unfold node.

Inductive well_founded : tree -> Prop :=
| wf_leaf : well_founded (node nil)
| wf_internal hd tl (WHD: well_founded hd) (WTL: well_founded (node tl)) :
                      well_founded (node (cons hd tl)).

Theorem tree_well_founded x : well_founded x.
Proof.
  mem_induction x. induction x0.
  - constructor.
  - constructor.
    + apply IND. sconstructor.
    + apply IHx0. intros. apply IND.
      right. auto.
Qed.

End list_tree_ssp.

Fixpoint power n (X: Type) : Type :=
  match n with
  | O => unit
  | S n' => X * (power n' X) end.

Fail Inductive power_tree : Type :=
| node (n : nat) : power n power_tree -> power_tree.

Instance power_FunctorData (n : nat) : FunctorData (power n).
Proof.
  induction n; simpl.
  - apply const_functorData.
  - apply product_functorData.
    + apply id_functorData.
    + apply IHn.
Defined.

Instance power_SFunctorData (n : nat) : SFunctorData (power n).
Proof.
  induction n; simpl.
  - apply const_sFunctorData.
  - apply product_sFunctorData.
    + apply id_sFunctorData.
    + apply IHn.
Defined.

Instance power_SPFunctor (n : nat) : SPFunctor (power n).
Proof.
  induction n; simpl.
  - apply const_SPFunctor.
  - apply prod_SPFunctor.
    + apply id_SPFunctor.
    + apply IHn.
Defined.

Definition sigma_power X := sigT (fun n => power n X).

Instance sigma_power_SPF : SPFunctor sigma_power.
Proof.
  apply dep_sum_SPFunctor. apply power_SPFunctor.
Qed.

Definition power_tree : Type := ffix sigma_power.

Definition node (n : nat) (l : power n power_tree) : power_tree :=
  Ffix sigma_power (existT _ n l).
