Set Implicit Arguments.

Record eqv (A B : Type) := Eqv {
                               fn1 : A -> B;
                               fn2 : B -> A;
                               bij1 : forall a, fn2 (fn1 a) = a;
                               bij2 : forall b, fn1 (fn2 b) = b;
                             }.
Notation "A ~ B" := (eqv A B) (at level 50).

Section SIGEQ.

  Variable A : Type.
  Variable P : A -> Type.

  Lemma sig_eq1 (x1 x2 : sigT P) (EQ : x1 = x2) :
    sigT (fun e : projT1 x1 = projT1 x2 =>
                   eq_rect (projT1 x1) _ (projT2 x1) (projT1 x2) e = projT2 x2).
  Proof.
    destruct EQ. exists eq_refl. reflexivity.
  Defined.

  Lemma sig_eq2 (x1 x2 : sigT P)
        (SEQ : sigT (fun e : projT1 x1 = projT1 x2 =>
            eq_rect (projT1 x1) _ (projT2 x1) (projT1 x2) e = projT2 x2)) : x1 = x2.
  Proof.
    destruct SEQ. destruct x1, x2. simpl in *.
    subst. reflexivity.
  Defined.

  Lemma sig_eq (x1 x2 : sigT P) :
    (x1 = x2) ~ (sigT (fun e : projT1 x1 = projT1 x2 =>
                    eq_rect (projT1 x1) _ (projT2 x1) (projT1 x2) e = projT2 x2)).
  Proof.
    apply (Eqv (@sig_eq1 x1 x2) (@sig_eq2 x1 x2)).
    - intro. destruct a. destruct x1. reflexivity.
    - intro. destruct b. destruct x1, x2. simpl in *. destruct x.
      simpl in e. destruct e. reflexivity.
  Defined.

End SIGEQ.

Section SUMEQ.

  Variable A B : Type.

  Definition code (x : A + B) (y : A + B) : Type :=
    match x with
    | inl a1 =>
      match y with
      | inl a2 => (a1 = a2)
      | inr b2 => False
      end
    | inr b1 =>
      match y with
      | inl a2 => False
      | inr b2 => (b1 = b2)
      end
    end.

  Definition code_inl (a : A) (x : A + B) : Type :=
    match x with
    | inl a0 => (a = a0)
    | inr b0 => False end.

  Lemma sum_eq_inl1 a x : (@eq (sum A B) (inl a) x) -> code_inl a x.
  Proof.
    intro.
    apply (eq_rect (inl a) (code_inl a) eq_refl x H).
  Defined.

  Lemma sum_eq_inl2 a x : code_inl a x -> (@eq (sum A B) (inl a) x).
  Proof.
    intro.
    destruct x.
    - apply (f_equal inl X).
    - destruct X.
  Defined.

  Lemma sum_eq_inl a x : (@eq (sum A B) (inl a) x) ~ (code_inl a x).
  Proof.
    apply (Eqv (@sum_eq_inl1 _ _) (@sum_eq_inl2 _ _));
      unfold sum_eq_inl1, sum_eq_inl2, f_equal.
    - intro. destruct a0. reflexivity.
    - intro. destruct x; destruct b. reflexivity.
  Defined.

  Definition code_inr (b : B) (x : A + B) : Type :=
    match x with
    | inl a0 => False
    | inr b0 => (b = b0) end.

  Lemma sum_eq_inr1 b x : (@eq (sum A B) (inr b) x) -> code_inr b x.
  Proof.
    intro.
    apply (eq_rect (inr b) (code_inr b) eq_refl x H).
  Defined.

  Lemma sum_eq_inr2 b x : code_inr b x -> (@eq (sum A B) (inr b) x).
  Proof.
    intro.
    destruct x.
    - destruct X.
    - apply (f_equal inr X).
  Defined.

  Lemma sum_eq_inr b x : (@eq (sum A B) (inr b) x) ~ (code_inr b x).
  Proof.
    apply (Eqv (@sum_eq_inr1 _ _) (@sum_eq_inr2 _ _));
      unfold sum_eq_inr1, sum_eq_inr2, f_equal.
    - intro. destruct a. reflexivity.
    - intro. destruct x; destruct b0. reflexivity.
  Defined.

End SUMEQ.

Section FUNEXT.

  Variable A : Type.
  Variable B : A -> Type.

  Definition ext (f g : forall x : A, B x) : Type :=
    forall x : A, f x = g x.

  Notation "f == g" := (ext f g) (at level 50).

  Definition eqext (f g : forall x : A, B x) :
    (f = g) -> (f == g).
    intros EQ a.
    destruct EQ. reflexivity.
  Defined.  

  Axiom exteq : forall (f g : forall x : A, B x),
      (f == g) -> (f = g).

  Axiom ext_bij1 : forall (f g : forall x : A, B x) (EQ : f = g),
      exteq (eqext EQ) = EQ.

  Axiom ext_bij2 : forall (f g : forall x : A, B x) (EXT : forall x : A, f x = g x),
      eqext (exteq EXT) = EXT.

  Definition functional_extensionality (f g : forall x : A, B x) :
    (f = g) ~ (forall x : A, f x = g x) :=
    {|
      fn1 := @eqext f g;
      fn2 := @exteq f g;
      bij1 := @ext_bij1 f g;
      bij2 := @ext_bij2 f g;
    |}.

End FUNEXT.

Section EQRECTFACTS.

  Definition eq_rect_fun A X (P : A -> X -> Type) (a b : A) (pa : forall (x: X), P a x)
             (EQ : a = b) :
    eq_rect a (fun (a' : A) => forall (x : X), P a' x) pa b EQ =     
    fun (x : X) => eq_rect a (fun (a' : A) => P a' x) (pa x) b EQ.
    destruct EQ. reflexivity.
  Defined.

  Definition eq_rect_fun2 A (P Q : A -> Type) (a b : A) (EQ : a = b) (f : P a -> Q a) :
    eq_rect a (fun a' => P a' -> Q a') f b EQ =
    fun x : P b => eq_rect a Q (f (eq_rect b P x a (eq_sym EQ))) b EQ.
    destruct EQ. reflexivity.
  Defined.

  Definition eq_rect_fun3 A B (f1 f2 : forall a : A, B a) (EQ : f1 = f2) (a : A)
    (P : forall a, B a -> Type) (p : P a (f1 a)) :
    eq_rect f1 (fun f => P a (f a)) p f2 EQ =
    eq_rect (f1 a) (P a) p (f2 a) (fn1 (functional_extensionality B f1 f2) EQ a).
    destruct EQ. reflexivity.
  Defined.

  Definition eq_rect_const A B (a1 a2 : A) (b : B) (EQ : a1 = a2) :
    eq_rect a1 (fun _ => B) b a2 EQ = b.
    destruct EQ.
    reflexivity.
  Defined.

End EQRECTFACTS.
