(*
Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor inductive coinductive combinator paco.

Opaque ffix Ffix ffix_des ffix_des_ord frec frec_p frec_d order_part.
Opaque Fcofix fcofix_des val grd grd_fcofix_des to_fcofix fcorec fcorec_p_red.
Global Opaque rffix rFfix rffix_des rffix_des_ord rfrec rfrec_p rfrec_d rorder_part.


Module opt_nat.

Definition mynat := ffix option_SPFunctorType.
Definition myO := Ffix option_SPFunctorType None.
Definition myS x := Ffix option_SPFunctorType (Some x).

Hint Resolve rfrec_red rfrec_d_red rfrec_p_red rdes_ord_correct rdes_correct2 drop_id.
Hint Resolve frec_red frec_d_red frec_p_red des_ord_correct des_correct2 drop_id.

Ltac rcompute := repeat (try rewrite rfrec_red;
                         try rewrite rfrec_d_red;
                         try rewrite rfrec_p_red;
                         try rewrite rdes_ord_correct;
                         try rewrite rdes_correct2;
                         try rewrite drop_id;
                         simpl).

Ltac mcompute := repeat (try rewrite frec_red;
                         try rewrite frec_d_red;
                         try rewrite frec_p_red;
                         try rewrite des_ord_correct;
                         try rewrite des_correct2;
                         try rewrite drop_id;
                         simpl).


Ltac simp := repeat (repeat rewrite rfrec_red;
                         repeat rewrite rfrec_d_red;
                         repeat rewrite rfrec_p_red;
                         repeat rewrite rdes_ord_correct;
                         repeat rewrite rdes_correct2;
                         repeat rewrite drop_id;
                         simpl).


Definition mynat' := rffix option_SPFunctorType.
Definition myO' := rFfix option_SPFunctorType None.
Definition myS' x := rFfix option_SPFunctorType (Some x).

Definition fibonacci := rfrec (fun (m : mynat') f =>
                                 match rffix_des_ord _ m with
                                 | None => 1
                                 | Some (w_ord _ _ m' p1) =>
                                   match rffix_des_ord _ m' with
                                   | None => 1
                                   | Some (w_ord _ _ m'' p2) => f m'' (rord_transtive p2 p1) + f m' p1 end end).

Definition fibonacci2 := frec (fun (m : mynat) f =>
                                 match ffix_des_ord m with
                                 | None => 1
                                 | Some (w_ord _ _ m' p1) =>
                                   match ffix_des_ord m' with
                                   | None => 1
                                   | Some (w_ord _ _ m'' p2) => f m'' (ord_transtive p2 p1) + f m' p1 end end).


Fixpoint to_mynat n :=
match n with
| O => rFfix option_SPFunctorType None
| S n' => rFfix option_SPFunctorType (Some (to_mynat n')) end.

Fixpoint to_mynat2 n :=
match n with
| O => Ffix option_SPFunctorType None
| S n' => Ffix option_SPFunctorType (Some (to_mynat2 n')) end.

Goal (fibonacci (to_mynat 3)) = 89.
  unfold fibonacci, myS', myO'. simpl.

  rewrite rfrec_red.
  rewrite rdes_ord_correct. simpl.
  rewrite rdes_ord_correct. simpl.
  
  rewrite rfrec_red.
  rewrite rdes_ord_correct. simpl.
  rewrite rdes_ord_correct. simpl.
  
  

  mcompute. auto 10000.
  simp. auto.
Qed.


Ltac rcompute := repeat (try rewrite rfrec_red;
                         try rewrite rfrec_d_red;
                         try rewrite rfrec_p_red;
                         try rewrite rdes_ord_correct;
                         try rewrite rdes_correct2;
                         try rewrite drop_id;
                         simpl).


Fixpoint fibonacci' n :=
  match n with
  | O => 1
  | S n' =>
    match n' with
    | O => 1
    | S n'' => fibonacci' n'' + fibonacci' n' end end.

Goal (fibonacci2 (to_mynat2 10)) = 89.
  unfold fibonacci2, myS, myO. simpl.
  msimpl.
  

Goal (fibonacci' 10) = 89.
  simp.



Fixpoint to_mynat n :=
match n with
| O => rFfix option_SPFunctorType None
| S n' => rFfix option_SPFunctorType (Some (to_mynat n')) end.



Eval rcompute in (fibonacci (myS' (myS' (myS' myO')))).

Goal forall n m, myS (myS n) = myS (myS m) -> n = m.
Proof.
  intros.
  apply Ffix_inj in H. inversion H.
Abort.

Definition ssss : S 5 = S 5 :=
  match (S 5) with
  | S a => eq_refl (S a)
  | O => eq_refl O end.

Print ssss.

Goal forall n, n = 5 -> S n = 6.
Proof.
  intros.
  destruct H. auto.
Qed.


Definition to_nat := frec (fun (n: mynat) f =>
  match ffix_des_ord n with
  | None => 0
  | Some (w_ord n' pf) => (f n' pf) + 1 end).

Lemma sssss : to_nat (myS (myS (myS myO))) = 3.
Proof.
  unfold myS. unfold to_nat. unfold myO.
  msimpl. auto.
Qed.

End opt_nat.


Section stream.

Variable A: Type.

Definition stream_gen := (prod_SPFunctorType (const_SPFunctorType A) id_SPFunctorType).

Definition stream := fcofix stream_genx.

Definition Cons n x := Fcofix stream_gen (n, x).

Definition hd (x: stream) :=
match fcofix_des x with
| (n, x') => n end.

Definition tl (x: stream) :=
match fcofix_des x with
| (n, x') => x' end.

End stream.

Definition enumeration : nat -> stream nat :=
  fcorec (fun n : nat => grd (stream_gen nat) nat (n, inl n)).



Definition inf_true := fcorec (fun u: unit => grd (stream_gen bool) unit (true, inl tt)) tt. 


Lemma inf_true_c : hd inf_true = true.
Proof.
  unfold hd. unfold inf_true.
  csimpl. auto.
Qed.

Lemma idddd A (x:A) : id x = x.
Proof. auto. Qed.

Lemma ssssss : hd (tl (tl (tl (tl (tl inf_true))))) = true.
Proof.
  unfold hd, tl, inf_true. 
  csimpl. auto.
Qed.

Module Inftree.

Definition tree_gen := (prod_SPFunctorType (const_SPFunctorType nat) (prod_SPFunctorType id_SPFunctorType id_SPFunctorType)).

Definition inftree := fcofix tree_gen.

Definition node n x1 x2 := Fcofix tree_gen (n, (x1, x2)).

Definition one_gen := (fun b : bool =>
                                      match b with
                                      | true => grd tree_gen bool (1, (inl true, inl false))
                                      | false => grd tree_gen bool (2, (inl true, inl false)) end).

Definition one : inftree := fcorec one_gen true.

Definition eins_gen := (fun b: bool =>
                          match b with
                          | true => grd tree_gen bool (1, (inl true, inr (grd tree_gen bool (2, (inl true, inl false)))))
                          | false => grd tree_gen bool (2, (inl true, inl false)) end).

Definition eins : inftree := fcorec eins_gen true.

Lemma one_eins_bsm : bsm one eins.
Proof.
  pcofix CIH.
  pfold.
  rewrite <- (c_des_correct1 one). rewrite <- (c_des_correct1 eins).
  constructor.
  unfold one, eins. unfold one_gen, eins_gen. csimpl.
  split; auto. split; auto. fold one_gen. fold eins_gen.
  left. pfold.
  rewrite <- (c_des_correct1 (fcorec one_gen false)).
  unfold one_gen. unfold eins_gen. 
  constructor. csimpl. fold one_gen. fold eins_gen.
  split; auto. split; auto.
  left. pcofix CIH'.
  pfold.
  rewrite <- (c_des_correct1 (fcorec one_gen false)).
  rewrite <- (c_des_correct1 (fcorec eins_gen false)).
  constructor. csimpl.
  split; auto.
Qed.

Lemma teq'_two_one : forall r,
  (r (fcorec one_gen false) (fcorec eins_gen false) : Prop)
  -> paco2 (@bsm_gen tree_gen) r (fcorec one_gen true) (fcorec eins_gen true).
Proof.
  intros; pcofix CIH.
  pfold.
  rewrite <- (c_des_correct1 (fcorec one_gen true)).
  rewrite <- (c_des_correct1 (fcorec eins_gen true)).
  constructor. csimpl.
  split; auto. split; auto.
  left. pfold.
  rewrite <- (c_des_correct1 (fcorec one_gen false)).
  constructor. csimpl.
  split; auto.
Qed.

Lemma teq'_one_two : forall r,
  (r (fcorec one_gen true) (fcorec eins_gen true) : Prop)
  -> paco2 (@bsm_gen tree_gen) r (fcorec one_gen false) (fcorec eins_gen false).
Proof.
  intros; pcofix CIH.
  pfold.
  rewrite <- (c_des_correct1 (fcorec one_gen false)).
  rewrite <- (c_des_correct1 (fcorec eins_gen false)).
  constructor. csimpl.
  split; auto. 
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

*)