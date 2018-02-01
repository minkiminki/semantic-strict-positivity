Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor.

Arguments S {C} F {SPFunctor}.
Arguments P {C} F {SPFunctor}.
Arguments NT {C F G H H0} NatIso {X} f.
Arguments NTinv {C F G H H0} NatIso {X} f.

(* Ident *)

Axiom GIVEUP : forall (A : Type), A.
Ltac giveup := apply GIVEUP.

Section HOTT.


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


  Lemma Hextensionality A (a1 a2 : A) (e : a1 = a2) (P : A -> Type) B
        (f1 : B -> P a1) (f2 : B -> P a2)
        : eq_rect a1 (fun a => B -> P a) f1 a2 e = f2 <->
                        forall b, eq_rect a1 P (f1 b) a2 e = f2 b.
  Proof.
    intros. subst. simpl.
    split; intros.
    - subst. reflexivity.
    - apply functional_extensionality, H.
  Qed.

  Lemma existT_eqeq A U (a b : A) (x : U a) (y : U b) :
      existT U a x = existT U b y <-> exists (e : a = b), (eq_rect a U x b e) = y.
  Proof.
    intros.
    split; intro.
    - inversion H. exists (eq_refl _). reflexivity.
    - destruct H. destruct x0.
      subst. reflexivity.
  Qed.

  Lemma Hextensionality2 A (a1 a2 : A) (e : a1 = a2) (Q : A -> Type)
        (P : A -> Type)
        (f1 : Q a1 -> P a1) (f2 : Q a2 -> P a2)
    : eq_rect a1 (fun a => Q a -> P a) f1 a2 e = f2 <->
      forall q, eq_rect a1 P (f1 q) a2 e =
                f2 (eq_rect a1 Q q a2 e).
  Proof.
    intros. subst. simpl.
    split; intros.
    - subst. reflexivity.
    - apply functional_extensionality, H.
  Qed.

  Definition eq_rect2 A (a1 a2 : A) (e : a1 = a2) (Q : A -> Type)
        (P : forall (a : A), Q a -> Type) q : P a1 q -> P a2 (eq_rect a1 Q q a2 e).
    destruct e. simpl. apply id.
  Defined.

  Lemma Hextensionality3 A (a1 a2 : A) (e : a1 = a2) (Q : A -> Type)
        (P : forall (a : A), Q a -> Type)
        (f1 : forall (q : Q a1), P a1 q) (f2 : forall (q : Q a2), P a2 q)
    : eq_rect a1 (fun a => forall (q : Q a), P a q) f1 a2 e = f2 <->
      forall (q : Q a1), eq_rect2 e Q P q (f1 q) =
                f2 (eq_rect a1 Q q a2 e).
  Proof.
    intros. subst. simpl.
    split; intros.
    - subst. reflexivity.
    - extensionality q. apply H.
  Qed.

  Lemma Hextensionality4 A (a1 a2 : A) (e : a1 = a2) Q
        (P : forall (a : A), Q -> Type)
        (f1 : forall (q : Q), P a1 q) (f2 : forall (q : Q), P a2 q)
    : eq_rect a1 (fun a => forall (q : Q), P a q) f1 a2 e = f2 <->
      forall (q : Q), eq_rect a1 (fun a => P a q) (f1 q) a2 e =
                f2 q.
  Proof.
    intros. subst. simpl.
    split; intros.
    - subst. reflexivity.
    - extensionality q. apply H.
  Qed.

  Lemma eq_rec_lemma A C (P : A -> C -> Type) (Q : C -> Type) (x y : A) (e : x = y)
  (f : forall i : C, P x i -> Q i) :
  eq_rect x (fun a : A => forall i : C, P a i -> Q i) f y e =
  (fun (i : C) (p : P y i) => f i (eq_rect y (fun a : A => P a i) p x (eq_sym e))).
  Proof.
    destruct e. simpl.
    extensionality i. extensionality p. reflexivity.
  Qed.

End HOTT.

Section DEP_FUN.

  Variable C A : Type.
  Variable (B : A -> (C -> Type) -> Type).
  Context `{forall (a : A), SPFunctor (B a)}.

  (*
  Instance FunctorBa (a : A) : Functor (B a) := @Fn _ _ (H a).
*)

  Definition Dep_fun (X : C -> Type) := forall a, B a X.

  Program Definition Dep_fun_Functor : Functor Dep_fun
    := Build_Functor
         Dep_fun
         (fun _ _ f fx a => map f (fx a)) 
         (fun _ fx _ x => ex (fun a => mem (fx a) x))
         (fun _ _ R fx fy => forall (a : A), rel R (fx a) (fy a))
         (fun _ fx =>
            fun a => (map (sigImply _ (fun i x (MEM: mem (fx a) x)
                                       => ex_intro _ a MEM)) (tag _ (fx a)))) _.
  Next Obligation.
    extensionality a.
    rewrite MAP_COMPOSE. rewrite <- TAG. reflexivity.
  Qed.
 
  Program Instance Dep_fun_SPF : SPFunctor Dep_fun
    := @Build_SPFunctor
         _ _ Dep_fun_Functor (forall a : A, S (B a))
         (fun s i => sigT (fun a => P (B a) (s a) i))
         (Build_NatIso
            _ _
            (fun _ fx =>
               (existT _ (fun a => projT1 (NT ISO (fx a)))
                       (fun i fx' => (projT2 (NT ISO (fx (projT1 fx'))))
                                       i (projT2 fx'))))
            (fun X fx =>
               fun a => NTinv ISO (existT _ (projT1 fx a)
                                          (fun i p => projT2 fx i (existT _ a p))))
            _ _ _ _ _).
  Next Obligation.
    unfold sigTimply. simpl.
    set (fn1 := (fun a : A => NT ISO (map f (fx a)))).
    set (fn2 := (fun a : A => map f (NT ISO (fx a)))).

    match goal with
    | [|- ?G] => replace G with
          (existT
    (fun s : forall a : A, S (B a) =>
     forall i : C, {a : A & P (B a) (s a) i} -> X2 i) (fun a : A => projT1 (fn1 a))
    (fun (i : C) (X0 : {a : A & P (B a) (projT1 (fn1 a)) i}) =>
     projT2 (fn1 (projT1 X0)) i (projT2 X0)) =
  existT
    (fun s : forall a : A, S (B a) =>
     forall i : C, {a : A & P (B a) (s a) i} -> X2 i) (fun a : A => projT1 (fn2 a))
    (fun (i : C) (X0 : {a : A & P (B a) (projT1 (fn2 a)) i}) =>
       projT2 (fn2 (projT1 X0)) i (projT2 X0))) end; auto.
    replace fn1 with fn2; auto.
    extensionality a. unfold fn1, fn2. symmetry. apply MAP_COMMUTE.
  Qed.    
  Next Obligation.
    split; intros.
    - destruct H0 as [a H0]. apply MEM_COMMUTE in H0. destruct H0.
      exists (existT _ a x0). apply H0.
    - destruct H0 as [[a p] H0].
      exists a. apply MEM_COMMUTE. exists p. apply H0.
  Qed.
  Next Obligation.
    split; intros.
    - 

      set (fn1 := (fun a : A => projT1 (NT ISO (fy a)))).
      set (fn2 := (fun a : A => projT1 (NT ISO (fx a)))).
      assert (fn1 = fn2). {
        unfold fn1, fn2.
        extensionality a.
        specialize (H0 a). apply REL_COMMUTE in H0. destruct H0. reflexivity.
      }

 match goal with
    | [|- ?G] => replace G with
(container_rel R
    (existT
       (fun s : forall a : A, S (B a) => forall i : C, {a : A & P (B a) (s a) i} -> X i)
       fn2
       (fun (i : C) (fx' : {a : A & P (B a) (fn2 a) i}) =>
        projT2 (NT ISO (fx (projT1 fx'))) i (projT2 fx')))
    (existT
       (fun s : forall a : A, S (B a) => forall i : C, {a : A & P (B a) (s a) i} -> Y i)
       fn1
       (fun (i : C) (fx' : {a : A & P (B a) (fn1 a) i}) =>
        projT2 (NT ISO (fy (projT1 fx'))) i (projT2 fx')))) end; auto.
      giveup. - giveup.
  Qed.
  Next Obligation.
    extensionality a.
    rewrite <- (BIJECTION1 _ (fx a)). f_equal.
    rewrite BIJECTION1.
    destruct (NT _ (fx a)) eqn : EQ.
    simpl. f_equal.
  Qed.
  Next Obligation.
    simpl. destruct gx. simpl.
    
    set (fn1 := fun a (s : {s : S (B a) & forall i : C, P (B a) s i -> X i}) =>
                  (NT ISO (NTinv ISO s))).

    assert (existT (fun s : forall a : A, S (B a) => forall i : C, {a : A & P (B a) (s a) i} -> X i)
    (fun a : A =>
     projT1
       (NT ISO
          (NTinv ISO
             (existT (fun s : S (B a) => forall i : C, P (B a) s i -> X i) (x a)
                (fun (i : C) (p : P (B a) (x a) i) => x0 i (existT (fun a0 : A => P (B a0) (x a0) i) a p))))))
    (fun (i : C)
       (X1 : {a : A &
             P (B a)
               (projT1
                  (NT ISO
                     (NTinv ISO
                        (existT (fun s : S (B a) => forall i0 : C, P (B a) s i0 -> X i0) (x a)
                           (fun (i0 : C) (p : P (B a) (x a) i0) => x0 i0 (existT (fun a0 : A => P (B a0) (x a0) i0) a p)))))) i}) =>
     projT2
       (NT ISO
          (NTinv ISO
             (existT (fun s : S (B (projT1 X1)) => forall i0 : C, P (B (projT1 X1)) s i0 -> X i0) (x (projT1 X1))
                (fun (i0 : C) (p : P (B (projT1 X1)) (x (projT1 X1)) i0) => x0 i0 (existT (fun a : A => P (B a) (x a) i0) (projT1 X1) p)))))
       i (projT2 X1)) = existT (fun s : forall a : A, S (B a) => forall i : C, {a : A & P (B a) (s a) i} -> X i)
    (fun a : A =>
     projT1
       (fn1 _ (existT (fun s : S (B a) => forall i : C, P (B a) s i -> X i) (x a)
                (fun (i : C) (p : P (B a) (x a) i) => x0 i (existT (fun a0 : A => P (B a0) (x a0) i) a p)))))
(fun (i : C)
       (X1 : {a : A &
             P (B a)
               (projT1
                  (fn1 _ (existT (fun s : S (B a) => forall i0 : C, P (B a) s i0 -> X i0) (x a)
                           (fun (i0 : C) (p : P (B a) (x a) i0) => x0 i0 (existT (fun a0 : A => P (B a0) (x a0) i0) a p))))) i}) =>
     projT2
       (fn1 _ (existT (fun s : S (B (projT1 X1)) => forall i0 : C, P (B (projT1 X1)) s i0 -> X i0) (x (projT1 X1))
                (fun (i0 : C) (p : P (B (projT1 X1)) (x (projT1 X1)) i0) => x0 i0 (existT (fun a : A => P (B a) (x a) i0) (projT1 X1) p))))
       i (projT2 X1))). {
      unfold fn1. reflexivity.
    } rewrite H0. clear H0.

    set (fn0 := fun (a : A) (s : {s : S (B a) & forall i : C, P (B a) s i -> X i}) => s).

    assert (fn1 = fn0). {
      extensionality a. extensionality s. unfold fn1, fn0. apply BIJECTION2.
    }

    assert (existT (fun s : forall a : A, S (B a) => forall i : C, {a : A & P (B a) (s a) i} -> X i)
    (fun a : A =>
     projT1
       (fn1 a
          (existT (fun s : S (B a) => forall i : C, P (B a) s i -> X i) (x a)
             (fun (i : C) (p : P (B a) (x a) i) => x0 i (existT (fun a0 : A => P (B a0) (x a0) i) a p)))))
    (fun (i : C)
       (X1 : {a : A &
             P (B a)
               (projT1
                  (fn1 a
                     (existT (fun s : S (B a) => forall i0 : C, P (B a) s i0 -> X i0) (x a)
                        (fun (i0 : C) (p : P (B a) (x a) i0) => x0 i0 (existT (fun a0 : A => P (B a0) (x a0) i0) a p))))) i}) =>
     projT2
       (fn1 (projT1 X1)
          (existT (fun s : S (B (projT1 X1)) => forall i0 : C, P (B (projT1 X1)) s i0 -> X i0) (x (projT1 X1))
             (fun (i0 : C) (p : P (B (projT1 X1)) (x (projT1 X1)) i0) => x0 i0 (existT (fun a : A => P (B a) (x a) i0) (projT1 X1) p))))
       i (projT2 X1)) = 
            existT (fun s : forall a : A, S (B a) => forall i : C, {a : A & P (B a) (s a) i} -> X i)
    (fun a : A =>
     projT1
       (fn0 a
          (existT (fun s : S (B a) => forall i : C, P (B a) s i -> X i) (x a)
             (fun (i : C) (p : P (B a) (x a) i) => x0 i (existT (fun a0 : A => P (B a0) (x a0) i) a p)))))
    (fun (i : C)
       (X1 : {a : A &
             P (B a)
               (projT1
                  (fn0 a
                     (existT (fun s : S (B a) => forall i0 : C, P (B a) s i0 -> X i0) (x a)
                        (fun (i0 : C) (p : P (B a) (x a) i0) => x0 i0 (existT (fun a0 : A => P (B a0) (x a0) i0) a p))))) i}) =>
     projT2
       (fn0 (projT1 X1)
          (existT (fun s : S (B (projT1 X1)) => forall i0 : C, P (B (projT1 X1)) s i0 -> X i0) (x (projT1 X1))
             (fun (i0 : C) (p : P (B (projT1 X1)) (x (projT1 X1)) i0) => x0 i0 (existT (fun a : A => P (B a) (x a) i0) (projT1 X1) p))))
       i (projT2 X1))). {
      destruct H0. reflexivity.
    }
    rewrite H1. clear H1. unfold fn0. simpl. f_equal.
    extensionality i. extensionality p. destruct p. reflexivity.
  Qed.    

End DEP_FUN.

Section COMP.

  Variable C1 C2 : Type.
  Variable F1 : C2 -> (C1 -> Type) -> Type.
  Variable F2 : (C2 -> Type) -> Type.

  Context `{SPFunctor _ F2}.
  Context `{forall (i : C2), SPFunctor (F1 i)}.

  Arguments map {C} F {Functor X Y}.
  Arguments mem {C} F {Functor X} f {i} x.
  Arguments rel {C} F {Functor X Y} R fx fy.

  Definition Comp (X : C1 -> Type) := F2 (fun (i : C2) => F1 i X).

  Goal True. apply I. Qed.

  Program Definition Comp_Functor : Functor Comp
    := Build_Functor
         Comp
         (fun _ _ f fx => map F2 (fun i x => map (F1 i) f x) fx)
         (fun X fxx i x => exists (j : C2) (fx : F1 j X),
              mem F2 fxx fx /\ mem (F1 j) fx x)
         (fun X Y R => rel F2 (fun (i : C2) => rel (F1 i) R)) _ _.
  Next Obligation.
    unfold Comp in *.
    eapply (map _ _ (tag _ fx)). Unshelve.

    intros i X0. 
    apply (map _ (fun i0 x1 => (sigImply _ (fun i1 x MEM => (ex_intro _ i (ex_intro _ (projI1 X0) (conj (projI2 X0) MEM)))) x1)) (tag _ (projI1 X0))). 

  Defined.
  Next Obligation.
    simpl. 
    unfold Comp, Comp_Functor_obligation_1 in *. simpl.
    rewrite MAP_COMPOSE. simpl. rewrite <- TAG. f_equal.
    extensionality i. extensionality x. destruct x.
    simpl. rewrite MAP_COMPOSE. rewrite <- TAG. f_equal.
  Qed.

  Program Instance Comp_SPF : SPFunctor Comp
    := @Build_SPFunctor _ _ Comp_Functor
                        (sigT (fun s : S F2 =>
                                 (forall (i : C2), P F2 s i -> S (F1 i))))
                        (fun s (j : C1) =>
                           sigT (fun (i : C2) => sigT (fun (p : P F2 (projT1 s) i) =>
                                     P (F1 i) ((projT2 s) i p) j)))
                        (Build_NatIso _ _
                                      _
                                      _ _ _ _ _ _).
  Next Obligation.
    apply (existT _ (existT (fun s : S F2 => forall i : C2, P F2 s i -> S (F1 i)) (projT1 (@NT _ F2 _ _ _ ISO _ X0))
                            (fun i p => projT1 (NT ISO ((projT2 (@NT _ F2 _ _ _ ISO _ X0)) i p)))) (fun i x => (projT2 (NT ISO ((projT2 (@NT _ F2 _ _ _ ISO _ X0)) (projT1 x) (projT1 (projT2 x))))) i (projT2 (projT2 x)))).
  Defined.
  Next Obligation.
    apply (@NTinv _ F2 _ _ _ ISO).    
    exists (projT1 (projT1 X0)).
    intros i p.
    apply (NTinv ISO).
    exists ((projT2 (projT1 X0)) i p).
    apply (fun j p' => (projT2 X0) j (existT _ i (existT _ p p'))).
  Defined.
  Next Obligation.
    unfold Comp_SPF_obligation_1. simpl.

    set (f1 := fun x => (NT ISO
                (map F2 (fun (i0 : C2) (x0 : F1 i0 X1) => map (F1 i0) f x0) x))).
    set (f2 := fun (x : F2 (fun i0 : C2 => F1 i0 X1)) => map (Container (P F2)) (fun (i0 : C2) (x0 : F1 i0 X1) => map (F1 i0) f x0) (@NT _ F2 _ _ _ ISO _ x)).
    assert (EQ : f1 = f2). {
      extensionality x. unfold f1, f2. apply MAP_COMMUTE.
    }

    assert (existT
    (fun x : {s : S F2 & forall i : C2, P F2 s i -> S (F1 i)} =>
     forall x0 : C1,
     {i : C2 & {p : P F2 (projT1 x) i & P (F1 i) (projT2 x i p) x0}} -> X2 x0)
    (existT (fun s : S F2 => forall i : C2, P F2 s i -> S (F1 i))
       (projT1 (f1 fx))
       (fun (i : C2) (p : P F2 (projT1 (f1 fx)) i) =>
        projT1 (NT ISO (projT2 (f1 fx) i p))))
    (fun (i : C1)
       (x : {i0 : C2 & {p : P F2 (projT1 (f1 fx)) i0 &
            P (F1 i0) (projT1 (NT ISO (projT2 (f1 fx) i0 p))) i}}) =>
     projT2 (NT ISO (projT2 (f1 fx)
             (projT1 x) (projT1 (projT2 x)))) i (projT2 (projT2 x)))
    =
existT
    (fun x : {s : S F2 & forall i : C2, P F2 s i -> S (F1 i)} =>
     forall x0 : C1,
     {i : C2 & {p : P F2 (projT1 x) i & P (F1 i) (projT2 x i p) x0}} -> X2 x0)
    (existT (fun s : S F2 => forall i : C2, P F2 s i -> S (F1 i))
       (projT1 (f2 fx))
       (fun (i : C2) (p : P F2 (projT1 (f2 fx)) i) =>
        projT1 (NT ISO (projT2 (f2 fx) i p))))
    (fun (i : C1)
       (x : {i0 : C2 & {p : P F2 (projT1 (f2 fx)) i0 &
            P (F1 i0) (projT1 (NT ISO (projT2 (f2 fx) i0 p))) i}}) =>
     projT2 (NT ISO (projT2 (f2 fx)
             (projT1 x) (projT1 (projT2 x)))) i (projT2 (projT2 x)))). {
      destruct EQ. reflexivity.
    }
    unfold f1, f2 in H1. rewrite H1. clear EQ f1 f2 H1. simpl in *.

    set (f3 := fun i x => NT ISO (map (F1 i) f x)).
    set (f4 := fun i (x : F1 i X1) => map _ f (NT ISO x)).
    assert (EQ : f3 = f4). {
      extensionality i. extensionality x. apply MAP_COMMUTE.
    }

    assert (existT
    (fun x : {s : S F2 & forall i : C2, P F2 s i -> S (F1 i)} =>
     forall x0 : C1,
     {i : C2 & {p : P F2 (projT1 x) i & P (F1 i) (projT2 x i p) x0}} -> X2 x0)
    (existT (fun s : S F2 => forall i : C2, P F2 s i -> S (F1 i))
       (projT1 (@NT _ F2 _ _ _ ISO _ fx))
       (fun (i : C2) (p : P F2 (projT1 (@NT _ F2 _ _ _ ISO _ fx)) i) =>
        projT1 (f3 i (projT2 (@NT _ F2 _ _ _ ISO _ fx) i p))))
    (fun (i : C1)
       (x : {i0 : C2 &
            {p : P F2 (projT1 (@NT _ F2 _ _ _ ISO _ fx)) i0 &
            P (F1 i0) (projT1 (f3 _ (projT2 (@NT _ F2 _ _ _ ISO _ fx) i0 p))) i}})
     =>
     projT2
       (f3 _ (projT2 (@NT _ F2 _ _ _ ISO _ fx) (projT1 x) (projT1 (projT2 x)))) i
       (projT2 (projT2 x)))
    =

    existT
    (fun x : {s : S F2 & forall i : C2, P F2 s i -> S (F1 i)} =>
     forall x0 : C1,
     {i : C2 & {p : P F2 (projT1 x) i & P (F1 i) (projT2 x i p) x0}} -> X2 x0)
    (existT (fun s : S F2 => forall i : C2, P F2 s i -> S (F1 i))
       (projT1 (@NT _ F2 _ _ _ ISO _ fx))
       (fun (i : C2) (p : P F2 (projT1 (@NT _ F2 _ _ _ ISO _ fx)) i) =>
        projT1 (f4 i (projT2 (@NT _ F2 _ _ _ ISO _ fx) i p))))
    (fun (i : C1)
       (x : {i0 : C2 &
            {p : P F2 (projT1 (@NT _ F2 _ _ _ ISO _ fx)) i0 &
            P (F1 i0) (projT1 (f4 _ (projT2 (@NT _ F2 _ _ _ ISO _ fx) i0 p))) i}})
     =>
     projT2
       (f4 _ (projT2 (@NT _ F2 _ _ _ ISO _ fx) (projT1 x) (projT1 (projT2 x)))) i
       (projT2 (projT2 x)))). {
      destruct EQ. reflexivity.
    }

    unfold f3, f4 in H1. rewrite H1. clear EQ f3 f3 H1. simpl.
    reflexivity.
  Qed.
  Next Obligation.
    unfold Comp_SPF_obligation_1; split; intros.
    - destruct H1 as [j [fx0 [H1 H2]]].
      apply MEM_COMMUTE in H1.
      apply MEM_COMMUTE in H2. simpl in *.
      destruct H1 as [p1 EQ1].
      destruct H2 as [p2 EQ2]. subst.
      exists (existT _ j (existT _ p1 p2)). reflexivity.
    - destruct H1 as [[i0 [p1 p2]] H1]. simpl in *.
      exists i0. subst. 
      exists (projT2 (@NT _ F2 _ _ _ ISO _ fx) i0 p1). split.
      + apply MEM_COMMUTE. simpl.
        exists p1. reflexivity.
      + apply MEM_COMMUTE. simpl.
        exists p2. reflexivity.
  Qed.
  Next Obligation.
    unfold Comp_SPF_obligation_1; split; intros; simpl in *;
    giveup.
  Qed.
  Next Obligation.
    Arguments NT {C} F {G H H0} NatIso {X} f.
    Arguments NTinv {C} F {G H H0} NatIso {X} f.
    unfold Comp_SPF_obligation_1, Comp_SPF_obligation_2. simpl.
    rewrite <- (@BIJECTION1 _ F2 _ _ _ _ _ fx). f_equal.
    rewrite (sigT_eta (NT F2 ISO fx)) at 2.

    set (f1 := fun (x : Comp X) => NTinv F2 ISO (NT F2 ISO x)).
    set (f2 := @id (Comp X)).
    assert (EQ : f1 = f2). {
      extensionality x.
      unfold f1, f2. rewrite BIJECTION1. reflexivity.
    }

    assert (existT (fun s : S F2 => forall i : C2, P F2 s i -> F1 i X)
    (projT1 (NT F2 ISO (f1 fx)))
    (fun (i : C2) (p : P F2 (projT1 (NT F2 ISO (f1 fx))) i)
     =>
     NTinv (F1 i) ISO
       (existT (fun s : S (F1 i) => forall i0 : C1, P (F1 i) s i0 -> X i0)
          (projT1
             (NT (F1 i) ISO (projT2 (NT F2 ISO (f1 fx)) i p)))
          (fun (j : C1)
             (p' : P (F1 i)
                     (projT1
                        (NT (F1 i) ISO
                           (projT2 (NT F2 ISO (f1 fx)) i p)))
                     j) =>
           projT2
             (NT (F1 i) ISO (projT2 (NT F2 ISO (f1 fx)) i p))
             j p'))) = existT (fun a : S F2 => forall i : C2, P F2 a i -> F1 i X)
    (projT1 (NT F2 ISO (f2 fx)))
    (fun (i : C2) (p : P F2 (projT1 (NT F2 ISO (f2 fx))) i)
     =>
     NTinv (F1 i) ISO
       (existT (fun s : S (F1 i) => forall i0 : C1, P (F1 i) s i0 -> X i0)
          (projT1
             (NT (F1 i) ISO (projT2 (NT F2 ISO (f2 fx)) i p)))
          (fun (j : C1)
             (p' : P (F1 i)
                     (projT1
                        (NT (F1 i) ISO
                           (projT2 (NT F2 ISO (f2 fx)) i p)))
                     j) =>
           projT2
             (NT (F1 i) ISO (projT2 (NT F2 ISO (f2 fx)) i p))
             j p')))
           ). {
      destruct EQ. reflexivity.
    }
    clear EQ. unfold f1, f2, id in H1. rewrite H1. clear H1.
    f_equal. extensionality i. extensionality p.

    rewrite <- (BIJECTION1 _ (projT2 (NT F2 ISO fx) i p)) at 2. f_equal.
    symmetry.
    apply (sigT_eta (NT (F1 i) ISO (projT2 (NT F2 ISO fx) i p))). 
  Qed.
  Next Obligation.
    unfold Comp_SPF_obligation_1, Comp_SPF_obligation_2. simpl. destruct gx. simpl.
    destruct x. simpl.

    set (f1 := fun (x : sigT (fun s0 : S F2 => forall i : C2, P F2 s0 i -> F1 i X))
                   => NT F2 ISO (NTinv F2 ISO x)).
    set (f2 := @id (sigT (fun s0 : S F2 => forall i : C2, P F2 s0 i -> F1 i X))).
    assert (EQ : f1 = f2). {
      extensionality p. unfold f1, f2.
      apply BIJECTION2.
    }

    assert (existT
    (fun x1 : {s0 : S F2 & forall i : C2, P F2 s0 i -> S (F1 i)} =>
     forall x2 : C1,
     {i : C2 & {p : P F2 (projT1 x1) i & P (F1 i) (projT2 x1 i p) x2}} -> X x2)
    (existT (fun s0 : S F2 => forall i : C2, P F2 s0 i -> S (F1 i))
       (projT1
          (f1 (existT (fun s0 : S F2 => forall i : C2, P F2 s0 i -> F1 i X) x
                   (fun (i : C2) (p : P F2 x i) =>
                    NTinv (F1 i) ISO
                      (existT
                         (fun s0 : S (F1 i) =>
                          forall i0 : C1, P (F1 i) s0 i0 -> X i0) 
                         (s i p)
                         (fun (j : C1) (p' : P (F1 i) (s i p) j) =>
                          x0 j
                            (existT
                               (fun i0 : C2 =>
                                {p0 : P F2 x i0 & P (F1 i0) (s i0 p0) j}) i
                               (existT (fun p0 : P F2 x i => P (F1 i) (s i p0) j) p
                                  p'))))))))
       (fun (i : C2)
          (p : P F2
                 (projT1
                    (f1 (existT
                             (fun s0 : S F2 =>
                              forall i0 : C2, P F2 s0 i0 -> F1 i0 X) x
                             (fun (i0 : C2) (p : P F2 x i0) =>
                              NTinv (F1 i0) ISO
                                (existT
                                   (fun s0 : S (F1 i0) =>
                                    forall i1 : C1, P (F1 i0) s0 i1 -> X i1)
                                   (s i0 p)
                                   (fun (j : C1) (p' : P (F1 i0) (s i0 p) j) =>
                                    x0 j
                                      (existT
                                         (fun i1 : C2 =>
                                          {p0 : P F2 x i1 & P (F1 i1) (s i1 p0) j})
                                         i0
                                         (existT
                                            (fun p0 : P F2 x i0 =>
                                             P (F1 i0) (s i0 p0) j) p p')))))))) i)
        =>
        projT1
          (NT (F1 i) ISO
             (projT2
                (f1 (existT
                         (fun s0 : S F2 => forall i0 : C2, P F2 s0 i0 -> F1 i0 X) x
                         (fun (i0 : C2) (p0 : P F2 x i0) =>
                          NTinv (F1 i0) ISO
                            (existT
                               (fun s0 : S (F1 i0) =>
                                forall i1 : C1, P (F1 i0) s0 i1 -> X i1) 
                               (s i0 p0)
                               (fun (j : C1) (p' : P (F1 i0) (s i0 p0) j) =>
                                x0 j
                                  (existT
                                     (fun i1 : C2 =>
                                      {p1 : P F2 x i1 & P (F1 i1) (s i1 p1) j}) i0
                                     (existT
                                        (fun p1 : P F2 x i0 =>
                                         P (F1 i0) (s i0 p1) j) p0 p'))))))) i p))))
    (fun (i : C1)
       (x1 : {i0 : C2 &
             {p
             : P F2
                 (projT1
                    (f1 (existT
                             (fun s0 : S F2 =>
                              forall i1 : C2, P F2 s0 i1 -> F1 i1 X) x
                             (fun (i1 : C2) (p : P F2 x i1) =>
                              NTinv (F1 i1) ISO
                                (existT
                                   (fun s0 : S (F1 i1) =>
                                    forall i2 : C1, P (F1 i1) s0 i2 -> X i2)
                                   (s i1 p)
                                   (fun (j : C1) (p' : P (F1 i1) (s i1 p) j) =>
                                    x0 j
                                      (existT
                                         (fun i2 : C2 =>
                                          {p0 : P F2 x i2 & P (F1 i2) (s i2 p0) j})
                                         i1
                                         (existT
                                            (fun p0 : P F2 x i1 =>
                                             P (F1 i1) (s i1 p0) j) p p'))))))))
                 i0 &
             P (F1 i0)
               (projT1
                  (NT (F1 i0) ISO
                     (projT2
                        (f1 (existT
                                 (fun s0 : S F2 =>
                                  forall i1 : C2, P F2 s0 i1 -> F1 i1 X) x
                                 (fun (i1 : C2) (p0 : P F2 x i1) =>
                                  NTinv (F1 i1) ISO
                                    (existT
                                       (fun s0 : S (F1 i1) =>
                                        forall i2 : C1, P (F1 i1) s0 i2 -> X i2)
                                       (s i1 p0)
                                       (fun (j : C1) (p' : P (F1 i1) (s i1 p0) j)
                                        =>
                                        x0 j
                                          (existT
                                             (fun i2 : C2 =>
                                              {p1 : P F2 x i2 &
                                              P (F1 i2) (s i2 p1) j}) i1
                                             (existT
                                                (fun p1 : P F2 x i1 =>
                                                 P (F1 i1) (s i1 p1) j) p0 p')))))))
                        i0 p))) i}}) =>
     projT2
       (NT (F1 (projT1 x1)) ISO
          (projT2
             (f1 (existT (fun s0 : S F2 => forall i0 : C2, P F2 s0 i0 -> F1 i0 X)
                      x
                      (fun (i0 : C2) (p : P F2 x i0) =>
                       NTinv (F1 i0) ISO
                         (existT
                            (fun s0 : S (F1 i0) =>
                             forall i1 : C1, P (F1 i0) s0 i1 -> X i1) 
                            (s i0 p)
                            (fun (j : C1) (p' : P (F1 i0) (s i0 p) j) =>
                             x0 j
                               (existT
                                  (fun i1 : C2 =>
                                   {p0 : P F2 x i1 & P (F1 i1) (s i1 p0) j}) i0
                                  (existT
                                     (fun p0 : P F2 x i0 => P (F1 i0) (s i0 p0) j)
                                     p p'))))))) (projT1 x1) 
             (projT1 (projT2 x1)))) i (projT2 (projT2 x1))) =

            existT
    (fun x1 : {s0 : S F2 & forall i : C2, P F2 s0 i -> S (F1 i)} =>
     forall x2 : C1,
     {i : C2 & {p : P F2 (projT1 x1) i & P (F1 i) (projT2 x1 i p) x2}} -> X x2)
    (existT (fun s0 : S F2 => forall i : C2, P F2 s0 i -> S (F1 i))
       (projT1
          (f2 (existT (fun s0 : S F2 => forall i : C2, P F2 s0 i -> F1 i X) x
                   (fun (i : C2) (p : P F2 x i) =>
                    NTinv (F1 i) ISO
                      (existT
                         (fun s0 : S (F1 i) =>
                          forall i0 : C1, P (F1 i) s0 i0 -> X i0) 
                         (s i p)
                         (fun (j : C1) (p' : P (F1 i) (s i p) j) =>
                          x0 j
                            (existT
                               (fun i0 : C2 =>
                                {p0 : P F2 x i0 & P (F1 i0) (s i0 p0) j}) i
                               (existT (fun p0 : P F2 x i => P (F1 i) (s i p0) j) p
                                  p'))))))))
       (fun (i : C2)
          (p : P F2
                 (projT1
                    (f2 (existT
                             (fun s0 : S F2 =>
                              forall i0 : C2, P F2 s0 i0 -> F1 i0 X) x
                             (fun (i0 : C2) (p : P F2 x i0) =>
                              NTinv (F1 i0) ISO
                                (existT
                                   (fun s0 : S (F1 i0) =>
                                    forall i1 : C1, P (F1 i0) s0 i1 -> X i1)
                                   (s i0 p)
                                   (fun (j : C1) (p' : P (F1 i0) (s i0 p) j) =>
                                    x0 j
                                      (existT
                                         (fun i1 : C2 =>
                                          {p0 : P F2 x i1 & P (F1 i1) (s i1 p0) j})
                                         i0
                                         (existT
                                            (fun p0 : P F2 x i0 =>
                                             P (F1 i0) (s i0 p0) j) p p')))))))) i)
        =>
        projT1
          (NT (F1 i) ISO
             (projT2
                (f2 (existT
                         (fun s0 : S F2 => forall i0 : C2, P F2 s0 i0 -> F1 i0 X) x
                         (fun (i0 : C2) (p0 : P F2 x i0) =>
                          NTinv (F1 i0) ISO
                            (existT
                               (fun s0 : S (F1 i0) =>
                                forall i1 : C1, P (F1 i0) s0 i1 -> X i1) 
                               (s i0 p0)
                               (fun (j : C1) (p' : P (F1 i0) (s i0 p0) j) =>
                                x0 j
                                  (existT
                                     (fun i1 : C2 =>
                                      {p1 : P F2 x i1 & P (F1 i1) (s i1 p1) j}) i0
                                     (existT
                                        (fun p1 : P F2 x i0 =>
                                         P (F1 i0) (s i0 p1) j) p0 p'))))))) i p))))
    (fun (i : C1)
       (x1 : {i0 : C2 &
             {p
             : P F2
                 (projT1
                    (f2 (existT
                             (fun s0 : S F2 =>
                              forall i1 : C2, P F2 s0 i1 -> F1 i1 X) x
                             (fun (i1 : C2) (p : P F2 x i1) =>
                              NTinv (F1 i1) ISO
                                (existT
                                   (fun s0 : S (F1 i1) =>
                                    forall i2 : C1, P (F1 i1) s0 i2 -> X i2)
                                   (s i1 p)
                                   (fun (j : C1) (p' : P (F1 i1) (s i1 p) j) =>
                                    x0 j
                                      (existT
                                         (fun i2 : C2 =>
                                          {p0 : P F2 x i2 & P (F1 i2) (s i2 p0) j})
                                         i1
                                         (existT
                                            (fun p0 : P F2 x i1 =>
                                             P (F1 i1) (s i1 p0) j) p p'))))))))
                 i0 &
             P (F1 i0)
               (projT1
                  (NT (F1 i0) ISO
                     (projT2
                        (f2 (existT
                                 (fun s0 : S F2 =>
                                  forall i1 : C2, P F2 s0 i1 -> F1 i1 X) x
                                 (fun (i1 : C2) (p0 : P F2 x i1) =>
                                  NTinv (F1 i1) ISO
                                    (existT
                                       (fun s0 : S (F1 i1) =>
                                        forall i2 : C1, P (F1 i1) s0 i2 -> X i2)
                                       (s i1 p0)
                                       (fun (j : C1) (p' : P (F1 i1) (s i1 p0) j)
                                        =>
                                        x0 j
                                          (existT
                                             (fun i2 : C2 =>
                                              {p1 : P F2 x i2 &
                                              P (F1 i2) (s i2 p1) j}) i1
                                             (existT
                                                (fun p1 : P F2 x i1 =>
                                                 P (F1 i1) (s i1 p1) j) p0 p')))))))
                        i0 p))) i}}) =>
     projT2
       (NT (F1 (projT1 x1)) ISO
          (projT2
             (f2 (existT (fun s0 : S F2 => forall i0 : C2, P F2 s0 i0 -> F1 i0 X)
                      x
                      (fun (i0 : C2) (p : P F2 x i0) =>
                       NTinv (F1 i0) ISO
                         (existT
                            (fun s0 : S (F1 i0) =>
                             forall i1 : C1, P (F1 i0) s0 i1 -> X i1) 
                            (s i0 p)
                            (fun (j : C1) (p' : P (F1 i0) (s i0 p) j) =>
                             x0 j
                               (existT
                                  (fun i1 : C2 =>
                                   {p0 : P F2 x i1 & P (F1 i1) (s i1 p0) j}) i0
                                  (existT
                                     (fun p0 : P F2 x i0 => P (F1 i0) (s i0 p0) j)
                                     p p'))))))) (projT1 x1) 
             (projT1 (projT2 x1)))) i (projT2 (projT2 x1)))). {
      destruct EQ. reflexivity.
    }

    unfold f1, f2, id in H1. clear EQ f1 f2. simpl in *. rewrite H1. clear H1.
    
    set (f3 := fun i (x : sigT (fun s0 : S (F1 i) => forall i1 : C1, P (F1 i) s0 i1 -> X i1)) => NT (F1 i) ISO (NTinv (F1 i) ISO x)).
    set (f4 := fun i (x : sigT (fun s0 : S (F1 i) => forall i1 : C1, P (F1 i) s0 i1 -> X i1)) => x).
    assert (EQ : f3 = f4). {
      extensionality i. extensionality p.
      unfold f3, f4. apply BIJECTION2.
    }

    assert (existT
    (fun x1 : {s0 : S F2 & forall i : C2, P F2 s0 i -> S (F1 i)} =>
     forall x2 : C1,
     {i : C2 & {p : P F2 (projT1 x1) i & P (F1 i) (projT2 x1 i p) x2}} -> X x2)
    (existT (fun s0 : S F2 => forall i : C2, P F2 s0 i -> S (F1 i)) x
       (fun (i : C2) (p : P F2 x i) =>
        projT1
          (f3 i (existT
                   (fun s0 : S (F1 i) => forall i1 : C1, P (F1 i) s0 i1 -> X i1)
                   (s i p)
                   (fun (j : C1) (p' : P (F1 i) (s i p) j) =>
                    x0 j
                      (existT
                         (fun i1 : C2 => {p1 : P F2 x i1 & P (F1 i1) (s i1 p1) j})
                         i (existT (fun p1 : P F2 x i => P (F1 i) (s i p1) j) p p')))))))
    (fun (i : C1)
       (x1 : {i0 : C2 &
             {p : P F2 x i0 &
             P (F1 i0)
               (projT1
                  (f3 i0 (existT
                           (fun s0 : S (F1 i0) =>
                            forall i2 : C1, P (F1 i0) s0 i2 -> X i2) 
                           (s i0 p)
                           (fun (j : C1) (p' : P (F1 i0) (s i0 p) j) =>
                            x0 j
                              (existT
                                 (fun i2 : C2 =>
                                  {p1 : P F2 x i2 & P (F1 i2) (s i2 p1) j}) i0
                                 (existT
                                    (fun p1 : P F2 x i0 => P (F1 i0) (s i0 p1) j) p
                                    p')))))) i}}) =>
     projT2
       (f3 (projT1 x1) (existT
                (fun s0 : S (F1 (projT1 x1)) =>
                 forall i1 : C1, P (F1 (projT1 x1)) s0 i1 -> X i1)
                (s (projT1 x1) (projT1 (projT2 x1)))
                (fun (j : C1)
                   (p' : P (F1 (projT1 x1)) (s (projT1 x1) (projT1 (projT2 x1))) j)
                 =>
                 x0 j
                   (existT
                      (fun i1 : C2 => {p0 : P F2 x i1 & P (F1 i1) (s i1 p0) j})
                      (projT1 x1)
                      (existT
                         (fun p0 : P F2 x (projT1 x1) =>
                          P (F1 (projT1 x1)) (s (projT1 x1) p0) j)
                         (projT1 (projT2 x1)) p'))))) i 
       (projT2 (projT2 x1)))
    =
    existT
    (fun x1 : {s0 : S F2 & forall i : C2, P F2 s0 i -> S (F1 i)} =>
     forall x2 : C1,
     {i : C2 & {p : P F2 (projT1 x1) i & P (F1 i) (projT2 x1 i p) x2}} -> X x2)
    (existT (fun s0 : S F2 => forall i : C2, P F2 s0 i -> S (F1 i)) x
       (fun (i : C2) (p : P F2 x i) =>
        projT1
          (f4 i (existT
                   (fun s0 : S (F1 i) => forall i1 : C1, P (F1 i) s0 i1 -> X i1)
                   (s i p)
                   (fun (j : C1) (p' : P (F1 i) (s i p) j) =>
                    x0 j
                      (existT
                         (fun i1 : C2 => {p1 : P F2 x i1 & P (F1 i1) (s i1 p1) j})
                         i (existT (fun p1 : P F2 x i => P (F1 i) (s i p1) j) p p')))))))
    (fun (i : C1)
       (x1 : {i0 : C2 &
             {p : P F2 x i0 &
             P (F1 i0)
               (projT1
                  (f4 i0 (existT
                           (fun s0 : S (F1 i0) =>
                            forall i2 : C1, P (F1 i0) s0 i2 -> X i2) 
                           (s i0 p)
                           (fun (j : C1) (p' : P (F1 i0) (s i0 p) j) =>
                            x0 j
                              (existT
                                 (fun i2 : C2 =>
                                  {p1 : P F2 x i2 & P (F1 i2) (s i2 p1) j}) i0
                                 (existT
                                    (fun p1 : P F2 x i0 => P (F1 i0) (s i0 p1) j) p
                                    p')))))) i}}) =>
     projT2
       (f4 (projT1 x1) (existT
                (fun s0 : S (F1 (projT1 x1)) =>
                 forall i1 : C1, P (F1 (projT1 x1)) s0 i1 -> X i1)
                (s (projT1 x1) (projT1 (projT2 x1)))
                (fun (j : C1)
                   (p' : P (F1 (projT1 x1)) (s (projT1 x1) (projT1 (projT2 x1))) j)
                 =>
                 x0 j
                   (existT
                      (fun i1 : C2 => {p0 : P F2 x i1 & P (F1 i1) (s i1 p0) j})
                      (projT1 x1)
                      (existT
                         (fun p0 : P F2 x (projT1 x1) =>
                          P (F1 (projT1 x1)) (s (projT1 x1) p0) j)
                         (projT1 (projT2 x1)) p'))))) i 
       (projT2 (projT2 x1)))). {
      destruct EQ. reflexivity.
    }
    unfold f3, f4 in H1. simpl in *. clear EQ f3 f4. rewrite H1. clear H1.

    f_equal. extensionality i. extensionality p. f_equal.
    rewrite (sigT_eta p) at 7. f_equal.
    symmetry. apply sigT_eta.
  Qed.    

End COMP.
