Set Implicit Arguments.
Require Import Program.

Definition eq_recursor : forall A (P : A -> Type) (x : A) (p : P x) (y : A),
                                  x = y -> P y.
  intros.
  destruct H. apply p.
Defined.

Definition prod_eq : forall A B (x y : A * B), x = y -> (fst x = fst y) * (snd x = snd y).
  intros. destruct x, y; constructor; inversion H; reflexivity.
Defined.

Definition eq_prod : forall A B (x y : A * B), (fst x = fst y) * (snd x = snd y) -> x = y.
  intros. destruct x, y. destruct H. simpl in *. destruct e, e0. reflexivity.
Defined.

Lemma prod_eq_eq1 : forall A B (x y : A*B) (e : x = y), eq_prod _ _ (prod_eq e) = e.
Proof.
  intros. destruct e. destruct x. reflexivity.
Qed.

Lemma prod_eq_eq2 : forall A B (x y : A*B) (e : (fst x = fst y) * (snd x = snd y)),
    prod_eq (eq_prod _ _ e) = e.
Proof.
  intros. destruct e. destruct x, y. simpl in *. destruct e, e0. reflexivity.
Qed.

Lemma eq_recursor_prod A (P Q: A -> Type) (x: A) (p: P x) (q: Q x) (y: A) (e : x = y) :
  eq_recursor (fun a : A => (P a * Q a)%type) (p, q) e =
  (eq_recursor P p e, eq_recursor Q q e).
Proof.
  destruct e. reflexivity.
Qed.

Lemma eq_recursor_lemma A C (P : A -> C -> Type) (Q : C -> Type) (x y : A) (e : x = y)
  (f : forall i : C, P x i -> Q i) :
  eq_recursor (fun a : A => forall i : C, P a i -> Q i) f e =
  (fun (i : C) (p : P y i) => f i (eq_recursor (fun a : A => P a i) p (eq_sym e))).
Proof.
  destruct e. simpl. extensionality i. extensionality p. reflexivity.
Qed.
