Set Implicit Arguments.

Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.

Record eqv (A B : Type) := Eqv {
                               fn1 : A -> B;
                               fn2 : B -> A;
                               bij1 : forall a, fn2 (fn1 a) = a;
                               bij2 : forall b, fn1 (fn2 b) = b;
                             }.
Notation "A ~ B" := (eqv A B) (at level 50).

Definition eqeqv1 A B (EQ : A = B) := (fun a => eq_rect A (@id Type) a B EQ).

Definition eqeqv2 A B (EQ : A = B) := (fun b => eq_rect B (@id Type) b A (eq_sym EQ)).

Definition eqeqv_bij1 A B (EQ : A = B) :
  forall a, eqeqv2 EQ (eqeqv1 EQ a) = a.
  destruct EQ. reflexivity.
Defined.

Definition eqeqv_bij2 A B (EQ : A = B) :
  forall b, eqeqv1 EQ (eqeqv2 EQ b) = b.
  destruct EQ. reflexivity.
Defined.

Definition eqeqv A B (EQ : A = B) : A ~ B :=
  {| 
    fn1 := eqeqv1 EQ;
    fn2 := eqeqv2 EQ;
    bij1 := eqeqv_bij1 EQ;
    bij2 := eqeqv_bij2 EQ;
  |}.

Axiom eqveq : forall A B, (A ~ B) -> A = B.

Axiom eqveq_bij1 : forall A B (EQ : A = B), eqveq (eqeqv EQ) = EQ.

Axiom eqveq_bij2 : forall A B (EQV : A ~ B), eqeqv (eqveq EQV) = EQV.

Definition univalence A B : (A = B) ~ (A ~ B) :=
  {|
    fn1 := @eqeqv A B;
    fn2 := @eqveq A B;
    bij1 := @eqveq_bij1 A B;
    bij2 := @eqveq_bij2 A B;
  |}.

Definition eqv_sym A B (EQV : A ~ B) : (B ~ A) :=
  {|
    fn1 := EQV.(fn2);
    fn2 := EQV.(fn1);
    bij1 := EQV.(bij2);
    bij2 := EQV.(bij1);
  |}.

Axiom prop_extensionality : forall P1 P2, (P1 <-> P2) -> (P1 = P2). 

Definition ext A (B : A -> Type) (f g : forall x : A, B x) : Type :=
  forall x : A, f x = g x.

Arguments ext {A B} f g.
Notation "f == g" := (ext f g) (at level 50).

Definition eqext A (B : A -> Type) (f g : forall x : A, B x) :
  (f = g) -> (f == g).
  intros EQ a.
  destruct EQ. reflexivity.
Defined.  

Axiom exteq : forall A (B : A -> Type) (f g : forall x : A, B x),
  (f == g) -> (f = g).

Axiom ext_bij1 : forall A B (f g : forall x : A, B x) (EQ : f = g),
    exteq (eqext _ EQ) = EQ.

Axiom ext_bij2 : forall A B (f g : forall x : A, B x) (EXT : forall x : A, f x = g x),
    eqext _ (exteq EXT) = EXT.

Definition functional_extensionality A B (f g : forall x : A, B x) :
  (f = g) ~ (forall x : A, f x = g x) :=
  {|
    fn1 := @eqext _ B f g;
    fn2 := @exteq _ _ f g;
    bij1 := @ext_bij1 _ B _ _;
    bij2 := ext_bij2 B f g;
  |}.

Ltac extensionality x :=
  match goal with
  | [ |- ?f = ?g ] => apply (functional_extensionality _ f g).(fn2);
                      intro x
  end.

Ltac unival :=
  match goal with
  | [ |- ?f = ?g ] => apply (univalence _ _).(fn2)
  | [ |- ?f ~ ?g ] => apply (univalence _ _).(fn1)
  end.

Record Functor := {
                   Fn : Type -> Type;
                   map : forall X Y (f : X -> Y), Fn X -> Fn Y;
                   mem : forall X, Fn X -> X -> Prop;
                   rel : forall X Y (R : X -> Y -> Type), Fn X -> Fn Y -> Type;
                   tag : forall X (fx : Fn X), Fn (sig (mem fx));
                 }.

Definition TAG (F : Functor) : Prop :=
  forall X (fx : F.(Fn) X), F.(map) (proj1_sig (P:= F.(mem) _)) (F.(tag) _ fx) = fx.

Definition map_injective (F : Functor) : Prop :=
  forall X Y (f : X -> Y) (INJ : forall x y : X, f x = f y -> x = y)
         (fx fy : F.(Fn) X), F.(map) f fx = F.(map) f fy -> fx = fy.

Definition map_injective_tag_unique (F : Functor) :
  TAG F -> map_injective F ->
  forall (f : forall X (fx : F.(Fn) X), F.(Fn) (sig (F.(mem) fx))),
    (forall X (fx : F.(Fn) X), F.(map) (proj1_sig (P:= F.(mem) _)) (f _ fx) = fx)
      -> F.(tag) = f.
  intros TAG0 INJ f TAG1.
  extensionality X. extensionality fx.
  eapply (INJ _ _ (proj1_sig (P:= F.(mem) _))).
  - intros. destruct x, y. simpl in H.
    subst. f_equal. apply proof_irrelevance.
  - rewrite TAG1. apply TAG0.
Defined.

Record NatIso (F1 F2 : Functor) :=
  {
    NT : forall X, F1.(Fn) X -> F2.(Fn) X;
    NTinv : forall X, F2.(Fn) X -> F1.(Fn) X;

    BIJ1 : forall X (x : F1.(Fn) X), NTinv _ (NT _ x) = x;
    BIJ2 : forall X (x : F2.(Fn) X), NT _ (NTinv _ x) = x;

    MAP_COMMUTE : forall X Y (f : X -> Y) (x : F1.(Fn) X),
        NT _ (F1.(map) f x) = F2.(map) f (NT _ x);

    MEM_COMMUTE : forall X (fx : F1.(Fn) X) (x : X),
        F1.(mem) fx x = F2.(mem) (NT _ fx) x;
        
    REL_COMMUTE : forall X Y R (fx : F1.(Fn) X) (fy : F1.(Fn) Y),
        F1.(rel) R fx fy = F2.(rel) R (NT _ fx) (NT _ fy);

    TAG1 : TAG F1;
    TAG2 : TAG F2;
  }.

Section EQ_RECT_FACTS.

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

  Lemma uni_rect X Y (fx : X) (EQ : X = Y) :
    (eq_rect X (fun x : Type => x) fx Y EQ) = (eqeqv EQ).(fn1) fx.
  Proof.
    destruct EQ. reflexivity.
  Defined.

  Lemma eqeqv1_commute X Y (EQV : X ~ Y) : eqeqv1 (eqveq EQV) = EQV.(fn1).
  Proof.
    set (eqveq_bij2 EQV).
    apply f_equal with (f := @fn1 X Y) in e. apply e.
  Defined.

  Lemma eqv_port X Y (P : X ~ Y -> Type) EQV :
        (forall EQ : X = Y, P (eqeqv EQ)) -> P EQV.
  Proof.
    intro. rewrite <- eqveq_bij2. apply X0.
  Defined.

  Lemma port1 X Y (EQV : X ~ Y) (a b : X) : EQV.(fn1) a = EQV.(fn1) b -> a = b. 
  Proof.
    intro. apply f_equal with (f := EQV.(fn2)) in H.
    repeat rewrite bij1 in H. apply H.
  Defined.

  Lemma port2 X Y (EQV : X ~ Y) (a b : Y) : EQV.(fn2) a = EQV.(fn2) b -> a = b. 
  Proof.
    intro. apply f_equal with (f := EQV.(fn1)) in H.
    repeat rewrite bij2 in H. apply H.
  Defined.

  Lemma sym_commute X Y (EQV : X ~ Y) : eq_sym (eqveq EQV) = eqveq (eqv_sym EQV).
  Proof.
    rewrite <- (eqveq_bij2 EQV). destruct (eqveq EQV).
    rewrite eqveq_bij1. simpl.
    unfold eqeqv. unfold eqv_sym. simpl.
    match goal with
    | [|- ?x = eqveq ?y] => replace y with (eqeqv (@eq_refl Type X)) end.
    symmetry. apply eqveq_bij1.
    reflexivity.
  Defined.    

(*
  Lemma sym_ext A B ()

    replace (eq_sym
          (exteq (fun _ : Type => Type) (Fn F1) (Fn F2)
             (fun X0 : Type => eqveq (eqv_FnX X0)))) with (exteq _ _ _ (fun Z => eqveq (eqv_sym (eqv_FnX Z)))).
    rewrite ext_bij2. rewrite eqeqv1_commute. apply BIJ2.
    
    replace (fun Z : Type => eqveq (eqv_sym (eqv_FnX Z))) with
        (fun Z : Type => eq_sym (eqveq (eqv_FnX Z)));
      [| extensionality Z; apply sym_commute].



    replace (eq_sym
          (exteq (fun _ : Type => Type) (Fn F1) (Fn F2)
             (fun X0 : Type => eqveq (eqv_FnX X0)))) with (exteq _ _ _ (fun Z => eqveq (eqv_sym (eqv_FnX Z)))).
    rewrite ext_bij2. rewrite eqeqv1_commute. apply BIJ2.
    
    replace (fun Z : Type => eqveq (eqv_sym (eqv_FnX Z))) with
        (fun Z : Type => eq_sym (eqveq (eqv_FnX Z)));
      [| extensionality Z; apply sym_commute].
*)

End EQ_RECT_FACTS.

Section NATISOEQV.

  Variable F1 F2 : Functor.
  Variable ISO : NatIso F1 F2.

  Definition eqv_FnX X : F1.(Fn) X ~  F2.(Fn) X.
    apply (Eqv (ISO.(NT) X) (ISO.(NTinv) X));
      [apply BIJ1 | apply BIJ2].
  Defined.

  Definition eqv_Fn : F1.(Fn) = F2.(Fn).
    extensionality X. unival.
    apply eqv_FnX.
  Defined.

  Definition eqv_map : eq_rect F1.(Fn) (fun x => forall X Y (f : X -> Y), x X -> x Y)
                                       F1.(map) F2.(Fn) eqv_Fn = F2.(map).
    rewrite eq_rect_fun.
    extensionality X. rewrite eq_rect_fun. extensionality Y.
    rewrite eq_rect_fun. extensionality f. simpl.
    extensionality fx. rewrite eq_rect_fun2.

    rewrite (eq_rect_fun3 (fun x => Type) eqv_Fn Y (fun _ x => x)). simpl in *.
    rewrite (eq_rect_fun3 (fun x => Type) (eq_sym eqv_Fn) X (fun _ x => x)). simpl in *.
    repeat rewrite uni_rect. unfold eqv_Fn at 1. simpl.
    rewrite ext_bij2. rewrite eqeqv1_commute. simpl.
    rewrite MAP_COMMUTE. f_equal.
    unfold eqv_Fn. simpl.

    replace (eq_sym
          (exteq
             (fun X0 : Type => eqveq (eqv_FnX X0)))) with (exteq (fun Z => eqveq (eqv_sym (eqv_FnX Z)))).
    rewrite ext_bij2. rewrite eqeqv1_commute. apply BIJ2.
    
    replace (fun Z : Type => eqveq (eqv_sym (eqv_FnX Z))) with
        (fun Z : Type => eq_sym (eqveq (eqv_FnX Z)));
      [| extensionality Z; apply sym_commute].

    set (fn := fun Z => eqveq (eqv_FnX Z)).
    assert ( exteq 
    (fun Z : Type => eq_sym (fn Z)) =
  eq_sym (exteq fn)); [| apply H].
    apply (port1 (functional_extensionality _ (Fn F2) (Fn F1))).
    simpl. rewrite ext_bij2.
    extensionality Z.
    set (exteq fn). 
    replace fn with (eqext _ e).
    destruct e. reflexivity.
    unfold e. apply ext_bij2.
  Defined.
 
  Definition eqv_mem : eq_rect F1.(Fn) (fun F => forall X, F X -> X -> Prop)
                                      F1.(mem) F2.(Fn) eqv_Fn = F2.(mem).
  Proof.
    rewrite eq_rect_fun. extensionality X.
    rewrite eq_rect_fun2. extensionality fx.
    rewrite eq_rect_fun. simpl. extensionality x.
    rewrite (eq_rect_fun3 (fun x => Type) (eq_sym eqv_Fn) X (fun _ X => X) fx).
    simpl in *. rewrite uni_rect. simpl.
    rewrite (eq_rect_fun3 (fun x => Type) eqv_Fn X (fun _ _ => Prop) (mem F1 (eqeqv1 (eqext (fun _ : Type => Type) (eq_sym eqv_Fn) X) fx) x)). simpl in *. 

    unfold eqv_Fn. simpl. rewrite ext_bij2. simpl.
    replace (eq_sym
                (exteq (fun X0 : Type => eqveq (eqv_FnX X0)))) with
        (exteq 
               (fun X0 : Type => eq_sym (eqveq (eqv_FnX X0)))).

    rewrite ext_bij2. simpl.

    replace (eq_sym (eqveq (eqv_FnX X))) with (eqveq (eqv_sym (eqv_FnX X))).
    simpl. rewrite eqeqv1_commute. simpl.
    
    destruct (eqveq (eqv_FnX X)). simpl.
    replace fx with (NT ISO X (NTinv ISO X fx)).
    rewrite BIJ1. apply MEM_COMMUTE.
    apply BIJ2.
    - admit.
    - admit.
  Admitted.

  Definition eqv_rel : eq_rect F1.(Fn) (fun F => forall X Y (R : X -> Y -> Type),
                                       F X -> F Y -> Type)
                                       F1.(rel) F2.(Fn) eqv_Fn = F2.(rel).
  Proof.
    rewrite eq_rect_fun. extensionality X.
    rewrite eq_rect_fun. extensionality Y.
    rewrite eq_rect_fun. extensionality R.
    rewrite eq_rect_fun2. extensionality fx.
    rewrite eq_rect_fun2. extensionality fy.

    rewrite (eq_rect_fun3 (fun x => Type) (eq_sym eqv_Fn) X (fun _ X => X) fx).
    rewrite (eq_rect_fun3 (fun x => Type) (eq_sym eqv_Fn) Y (fun _ Y => Y) fy).
    repeat rewrite uni_rect. simpl.
    
    unfold eqv_Fn. simpl.
    replace (eq_sym
                (exteq (fun X0 : Type => eqveq (eqv_FnX X0)))) with
        (exteq 
               (fun X0 : Type => eq_sym (eqveq (eqv_FnX X0)))).

    rewrite ext_bij2. simpl.
    replace (eq_sym (eqveq (eqv_FnX X))) with (eqveq (eqv_sym (eqv_FnX X))).
    replace (eq_sym (eqveq (eqv_FnX Y))) with (eqveq (eqv_sym (eqv_FnX Y))).
    repeat rewrite eqeqv1_commute. simpl.
    destruct (exteq 
       (fun X0 : Type => eqveq (eqv_FnX X0))). simpl.

    replace fx with (NT ISO X (NTinv ISO X fx)).
    replace fy with (NT ISO Y (NTinv ISO Y fy)).
    rewrite BIJ1. rewrite BIJ1.
    apply REL_COMMUTE.
    apply BIJ2. apply BIJ2.
  Admitted.

  Definition eq_rect2 X (P : forall x1 x2 : X, x1 = x2 -> Type)
             (F : forall x1, P x1 x1 eq_refl)
    : forall (x1 x2 : X) (EQ : x1 = x2), P x1 x2 EQ .
  Proof.
    intros.
    destruct EQ. apply F.
  Defined.

  Definition tag_port : forall X (fx : F2.(Fn) X), F2.(Fn) (sig (F2.(mem) fx)).
(*
    set (P := fun F => forall X (fx : Fn F X), Fn F {x : X | mem F fx x}).
    assert (P F1). unfold P. apply F1.(tag).
  *)
    apply (eq_rect (eq_rect F1.(Fn) (fun F => forall X, F X -> X -> Prop) F1.(mem) F2.(Fn) eqv_Fn) (fun m => forall (X : Type) (fx : Fn F2 X), Fn F2 {x : X | m X fx x})).
    
    rewrite <- eqv_Fn.
    apply F1.(tag).
    apply eqv_mem.
  Defined.

End NATISOEQV.

Section CONTAINER.

  Variable S : Type.
  Variable P : S -> Type.

  Definition container X := sigT (fun s => P s -> X).

  Inductive container_rel X Y (R : X -> Y -> Type) : container X -> container Y -> Type :=
  | _container_rel s f1 f2 : (forall p : P s, R (f1 p) (f2 p)) ->
                             container_rel R (existT _ s f1) (existT _ s f2).

  Lemma container_eq : forall X (x y : container X),
      (x = y) ~ (sigT (fun (EQ : projT1 x = projT1 y) => forall p : P (projT1 x),
                           (projT2 x) p = (projT2 y) (eq_rect (projT1 x) _ p (projT1 y) EQ))).
  Proof.
    auto.
  Admitted.

  Lemma container_eq1 : forall X (x y : container X),
      (sigT (fun (EQ : projT1 x = projT1 y) => forall p : P (projT1 x),
                           (projT2 x) p = (projT2 y) (eq_rect (projT1 x) _ p (projT1 y) EQ))) -> (container_rel eq x y).
  Proof.
    intros. destruct H. destruct x, y. simpl in *. destruct x0.
    simpl in *. apply _container_rel.
    apply e.
  Defined.    

  Lemma container_eq2 : forall X (x y : container X),
      (container_rel eq x y) -> (sigT (fun (EQ : projT1 x = projT1 y) =>
                                         forall p : P (projT1 x), (projT2 x) p = (projT2 y) (eq_rect (projT1 x) _ p (projT1 y) EQ))).
  Proof.
    intros. destruct X0. simpl.
    exists eq_refl. simpl. apply e.
  Defined.

  Lemma container_eq3 : forall X (x y : container X),
      (sigT (fun (EQ : projT1 x = projT1 y) => forall p : P (projT1 x),
                           (projT2 x) p = (projT2 y) (eq_rect (projT1 x) _ p (projT1 y) EQ))) ~ (container_rel eq x y).
  Proof.
    intros.
    apply (Eqv (@container_eq1 X x y) (@container_eq2 X x y)).
    - intro EQ. 
      destruct EQ. destruct x, y. simpl in *. destruct x0. reflexivity.
    - intros.
      destruct b. reflexivity.
  Defined.

  Lemma eqv_trans : forall X Y Z, X ~ Y -> Y ~ Z -> X ~ Z. 
  Proof.
    intros X Y Z EQ1 EQ2.
    apply (Eqv (fun x => EQ2.(fn1) (EQ1.(fn1) x)) (fun z => EQ1.(fn2) (EQ2.(fn2) z))).
    - intro x.
      rewrite bij1. apply bij1.
    - intro z.
      rewrite bij2. apply bij2.
  Defined.

  Lemma sigma_eq1 : forall A (B : A -> Type) (x y : sigT B),
      (x = y) -> (sigT (fun (EQ : projT1 x = projT1 y) => projT2 y = eq_rect (projT1 x) B (projT2 x) (projT1 y) EQ)).
  Proof.
    intros A B x y EQ.
    destruct EQ. exists eq_refl. reflexivity.
  Defined.

   Lemma sigma_eq2 : forall A (B : A -> Type) (x y : sigT B),
      (sigT (fun (EQ : projT1 x = projT1 y) => projT2 y = eq_rect (projT1 x) B (projT2 x) (projT1 y) EQ)) -> (x = y).
  Proof.
    intros A B x y EQ. destruct EQ, x, y. simpl in *. destruct x0. simpl in e.
    destruct e. reflexivity.
  Defined.

  Lemma sigma_eq : forall A (B : A -> Type) (x y : sigT B),
      (x = y) ~ (sigT (fun (EQ : projT1 x = projT1 y) => projT2 y = eq_rect (projT1 x) B (projT2 x) (projT1 y) EQ)).
  Proof.
    intros A B x y. 
    apply (Eqv (@sigma_eq1 A B x y) (@sigma_eq2 A B x y)).
    - intro EQ. destruct EQ. destruct x. reflexivity.
    - intro EQ. destruct EQ, x, y. simpl in *. destruct x0. simpl in e.
      destruct e. reflexivity.
  Defined.

  Lemma container_eq_rel : forall X (x y : container X),
      (x = y) ~ (container_rel eq x y).
  Admitted.

  Inductive mu : Type :=
  | Con : container mu -> mu.

  Inductive mu_equal : mu -> mu -> Type :=
  | _mu_refl x y : container_rel mu_equal x y -> mu_equal (Con x) (Con y).

  Definition Des : mu -> container mu :=
    fun x => match x with
             | Con m => m end.

  Lemma mu_bij : (container mu) ~ mu.                                           
  Proof.
    apply (Eqv Con Des).
    - intro. reflexivity.
    - intro. destruct b. reflexivity.
  Defined.
    
  Lemma mu_eq_bij : forall (x y : mu), (x = y) -> mu_equal x y.
    fix 1.
    intros. destruct x. destruct y.
    inversion H. apply _mu_refl.
    destruct c0. apply _container_rel.
    intros. apply mu_eq_bij. apply eq_refl.
  Defined.




