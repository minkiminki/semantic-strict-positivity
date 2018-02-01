Set Implicit Arguments.

Record eqv (A B : Type) := Eqv {
                               fn1 : A -> B;
                               fn2 : B -> A;
                               bij1 : forall a, fn2 (fn1 a) = a;
                               bij2 : forall b, fn1 (fn2 b) = b;
                             }.
Notation "A ~ B" := (eqv A B) (at level 50).

Goal True. constructor. Qed.

Definition code_inl A B (a : A) (x : A + B) : Type :=
  match x with
  | inl a0 => (a = a0)
  | inr b0 => False end.

Lemma sum_eq_inl1 A B a x : (@eq (sum A B) (inl a) x) -> code_inl a x.
Proof.
  intro.
  apply (eq_rect (inl a) (code_inl a) eq_refl x H).
Defined.

Lemma sum_eq_inl2 A B a x : code_inl a x -> (@eq (sum A B) (inl a) x).
Proof.
  intro.
  destruct x.
  - apply (f_equal inl X).
  - destruct X.
Defined.

Lemma sum_eq A B a x : (@eq (sum A B) (inl a) x) ~ (code_inl a x).
Proof.
  apply (Eqv (@sum_eq_inl1 _ _ _ _) (@sum_eq_inl2 _ _ _ _));
    unfold sum_eq_inl1, sum_eq_inl2, f_equal.
  - intro. destruct x. simpl. admit.
Admitted.