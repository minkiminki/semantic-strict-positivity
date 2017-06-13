Require Import Program.
Set Implicit Arguments.

(*
   Parameter Functor: option
*)

Module MPoption.

Definition t := option.

Inductive allP X (P: X -> Prop) : t X -> Prop :=
| allP_none : allP P None
| allP_some x
    (SOME: P x) :
  allP P (Some x)
.

Definition map := option_map.

Lemma all_step X (P: X -> Prop)
    (IND : forall x: X, P x)
    (m : t X):
  allP P m.
Proof.
  destruct m; constructor; auto.
Defined.

Lemma all_map X Y (f g: X -> Y) (l: t X)
    (ALL:allP (fun x => f x = g x) l):
  map f l = map g l.
Proof.
  destruct l; simpl; eauto.
  dependent destruction ALL.
  rewrite SOME; eauto.
Qed.

End MPoption.

(*
   Parameter Functor: list
*)

Module MPlist.

Definition t := list.

Definition map := List.map.

Inductive allP X (P: X -> Prop) : list X -> Prop :=
| allP_nil : allP P nil
| allP_cons hd tl 
    (HD: P hd) 
    (TL: allP P tl) :     
  allP P (cons hd tl)
.

Lemma all_step X (P: X -> Prop)
    (IND : forall x: X, P x)
    (m : list X):
  allP P m.
Proof.
  induction m; constructor; auto.
Defined.

Lemma all_map X Y (f g: X -> Y) (l: list X)
    (ALL:allP (fun x => f x = g x) l):
  map f l = map g l.
Proof.
  induction l; simpl; eauto.
  dependent destruction ALL.
  rewrite HD. rewrite IHl; eauto.
Qed.

End MPlist.

(*
   MP: package of all parameter functors
*)

Module MP.

Inductive mpsort : Type :=
| mpoption
| mplist 
.

Inductive t X : mpsort -> Type :=
| t_option : MPoption.t X -> t X mpoption
| t_list : MPlist.t X -> t X mplist
.

Definition map s X Y (f: X -> Y) (m: t X s) : t Y s :=
  match m with
  | t_option m => t_option (MPoption.map f m)
  | t_list m => t_list (MPlist.map f m)
  end.

Inductive allP X (P: X -> Prop) : forall s, t X s -> Prop :=
| a_option
    (m: MPoption.t X) (ALL: MPoption.allP P m): allP P (t_option m)
| a_list 
    (m: MPlist.t X) (ALL: MPlist.allP P m): allP P (t_list m)
.

Lemma all_map s X Y (f g: X -> Y) (l: t X s)
    (ALL:allP (fun x => f x = g x) l):
  map f l = map g l.
Proof.
  destruct s; dependent destruction l
  ; dependent destruction ALL; simpl; f_equal
  ; eauto using MPoption.all_map, MPlist.all_map.
Qed.

End MP.

(*
   Example: Mlist parameterized over MP.
*)

Inductive Mlist s (X: Type) : Type :=
| Mnil : Mlist s X
| Mcons (hd: MP.t X s) (tl: MP.t (Mlist s X) s) : Mlist s X
.
Arguments Mnil {s X}.

Lemma Mlist_ind' s X (l: Mlist s X) (P: Mlist s X -> Prop)
    (BASE: P Mnil)
    (STEP: forall hd tl 
             (IND: MP.allP P tl), 
           P (Mcons hd tl)):
  P l.
Proof.
  destruct s.
  { revert l. fix 1. intros. destruct l.
    + exact BASE.
    + apply STEP. dependent destruction tl.
      apply MP.a_option, MPoption.all_step; auto.
  }
  { revert l. fix 1. intros. destruct l.
    + exact BASE.
    + apply STEP. dependent destruction tl.
      apply MP.a_list, MPlist.all_step; auto.
  }
Qed.

Fixpoint mfix s X T 
  (tnil: T) 
  (tcons: MP.t X s -> MP.t (Mlist s X) s -> MP.t T s -> T) 
  (l: Mlist s X) : T 
  :=
  match l with
  | Mnil => tnil
  | Mcons hd tl => tcons hd tl (MP.map (mfix tnil tcons) tl)
  end.

Lemma mfix_unique s X T tnil tcons (mfix': Mlist s X -> T)
  (NIL: mfix' Mnil = tnil)
  (CONS: forall hd tl,
         mfix' (Mcons hd tl) = tcons hd tl (MP.map mfix' tl)):
  forall l, mfix tnil tcons l = mfix' l.
Proof.
  intros. eapply (@Mlist_ind' s X l); eauto.
  intros. simpl. erewrite CONS, MP.all_map; eauto.
Qed.

Fixpoint len s X (lenM: MP.t nat s -> nat) (l: Mlist s X) : nat :=
  match l with
  | Mnil => 0
  | Mcons hd tl => 1 + lenM (MP.map (len lenM) tl)
  end.

Lemma len_unique s X lenM len'
    (NIL: len' Mnil = 0)
    (CONS: forall hd tl,
           len' (Mcons hd tl) = 1 + lenM (MP.map len' tl)):
  forall l: Mlist s X, len lenM l = len' l.
Proof.
  intros. eapply (@Mlist_ind' s X l); eauto.
  intros. simpl. erewrite CONS, MP.all_map; eauto.
Qed.
