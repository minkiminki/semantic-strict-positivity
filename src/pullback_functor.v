Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import Functor hott.

Class PB_Functor (F : Type -> Type) `{Fn : Functor F} :=
  {
    MAP_COMPOSE X Y Z (f: X -> Y) (g: Y -> Z) (fx : F X) :
      map g (map f fx) = map (fun x => g (f x)) fx;
    MAP_ID X (fx : F X) :
      map id fx = fx;
    pullback A (X : A -> Type) C (fx : forall a, F (X a)) (fc : F C)
             (f : forall a, X a -> C) (EQ : forall a, fc = map (f a) (fx a)) :
      F (sig (fun x => forall a1 a2, f a1 (x a1) = f a2 (x a2)));
    PULLBACK A (X : A -> Type) C (fx : forall a, F (X a)) (fc : F C)
             (f : forall a, X a -> C) (EQ : forall a, fc = map (f a) (fx a)) :
      forall a, map (fun x => proj1_sig x a) (pullback _ fx f EQ) = fx a;
    FUN_UNIQUE A (a0 : A) (X : A -> Type) (fp1 fp2 : F (forall a, X a))
               (EQ : forall a, map (fun f => f a) fp1 = map (fun f => f a) fp2) :
      fp1 = fp2;

(*
    MAP_COMPOSE_ASSOC_C (X Y Z W: Type) (f: X -> Y)
             (g: Y -> Z) (h: Z -> W) (fx : F X) :
    eq_trans (f_equal (map h) (MAP_COMPOSE f g fx))
             (MAP_COMPOSE (fun (x : X) => g (f x)) h fx)
    = 
    eq_trans (MAP_COMPOSE g h (map f fx))
             (MAP_COMPOSE f (fun (y : Y) => h (g y)) fx);
    MAP_COMPOSE_ASSOC X Y Z (f: X -> Y) (g: Y -> Z) (fx : F X) :
      map g (map f fx) = map (fun x => g (f x)) fx;
    MAP_ID_UNIT1 X Y (f: X -> Y) (fx : F X) :
      MAP_COMPOSE id f fx = f_equal (map f) (MAP_ID fx);
    MAP_ID_UNIT2_C X Y (f: X -> Y) (fx : F X) :
      MAP_COMPOSE f id fx = MAP_ID (map f fx);
*)
  }.

Arguments MAP_ID {_ _ _} [_].
Arguments PB_Functor F {_}.

Section PULLBACK_FUNCTOR_FACTS.

  Variable F : Type -> Type.
  Context `{PBF: PB_Functor F}.

  Local Definition T X fx := sigT (fun (Pr : X -> Prop) => sig (fun fx' : F (sig Pr) => map (proj1_sig (P := Pr)) fx' = fx)).

  Local Lemma TEQ X fx : forall a : T fx, fx = map (projT1 (P:=projT1 a)) (map (fun X0 : {x : X | projT1 a x} => existT _ (` X0) (proj2_sig X0)) (proj1_sig (projT2 a))).
  Proof.
    intro t. rewrite MAP_COMPOSE. destruct t as [pr [fx' []]]. reflexivity.
  Qed.

  Local Definition Ttop X fx : T fx := 
    (existT _ (fun _ : X => True)
            (exist
               (fun fx' : F {_ : X | True} =>
                  map (proj1_sig (P:=fun _ : X => True)) fx' = fx)
               (map (fun x0 : X => exist (fun _ : X => True) x0 I) fx)
               (eq_trans
                  (MAP_COMPOSE (fun x0 : X => exist (fun _ : X => True) x0 I)
                               (proj1_sig (P:=fun _ : X => True)) fx) 
                  (MAP_ID fx)))).
  
  Arguments TEQ [X] fx.

  Opaque Ttop.

  Lemma default_tag X (fx : F X) : F (sig (default_mem fx)).
  Proof.
    eapply (map _ (@pullback _ _ _ _ (fun t : T fx => sigT (projT1 t)) X
                     (fun t : T fx => map (fun X0 => existT _ (proj1_sig X0) (proj2_sig X0)) (proj1_sig (projT2 t))) fx (fun t => projT1 (P:=projT1 t)) (TEQ fx))). Unshelve.
    intro x.
    exists (projT1 (proj1_sig x (Ttop fx))). intros Pr ALLP.
    destruct ALLP as [pr e].
    apply (eq_ind_r Pr (projT2 (proj1_sig x (existT _ Pr (exist _ pr e)))) (proj2_sig x _ (existT _ Pr (exist _ pr e)))).
  Defined.

  Lemma DEFAULT_TAG X (fx : F X) :
    map (proj1_sig (P:=default_mem fx)) (default_tag fx) = fx.
  Proof.
    unfold default_tag. rewrite MAP_COMPOSE. simpl.
    apply eq_trans with 
        (y := map (projT1 (P:=projT1 (Ttop fx)))
       (map
          (fun
             x : {x : forall a : T fx, {x : X & projT1 a x} |
                 forall a1 a2 : T fx, projT1 (x a1) = projT1 (x a2)} => 
           (` x) (Ttop fx))
          (pullback (fun t : T fx => {x : X & projT1 t x})
             (fun t : T fx =>
              map (fun X0 : {x : X | projT1 t x} => existT _ (` X0) (proj2_sig X0))
                (` (projT2 t))) (fun t : T fx => projT1 (P:=projT1 t)) 
             (TEQ fx)))).
    - symmetry. apply MAP_COMPOSE.
    - apply eq_trans with (y := map (projT1 (P:=projT1 (Ttop fx)))
        (map (fun X0 : {x : X | projT1 (Ttop fx) x} => existT _ (` X0) (proj2_sig X0))
           (` (projT2 (Ttop fx))))).
      + f_equal. apply (PULLBACK (fun t : T fx => {x : X & projT1 t x})
       (fun t : T fx =>
        map (fun X0 : {x : X | projT1 t x} => existT _ (` X0) (proj2_sig X0))
          (` (projT2 t))) (fun t : T fx => projT1 (P:=projT1 t))). 
      + rewrite MAP_COMPOSE. Transparent Ttop. simpl.
        apply eq_trans with (y := map id fx).
        * apply MAP_COMPOSE.
        * apply MAP_ID.
  Qed.

  Lemma ALLP_EQ X (Pr : X -> Prop) :
    forall (fx: F X), allP Pr fx <-> (forall x, default_mem fx x -> Pr x).
  Proof.
    intro; split.
    - intros H x MEM. destruct H as [fp EQ]. destruct EQ.
      apply (MEM Pr). 
      exists fp. reflexivity.
    - intro H. exists (map (fun x => exist _ (proj1_sig x) (H _ (proj2_sig x))) (default_tag fx)).
      rewrite MAP_COMPOSE. apply DEFAULT_TAG.
  Qed.

  Lemma REL_EQ_EQ X (fx fy : F X) :
    fx = fy <-> allR eq fx fy.
  Proof.
    split; intros.
    - destruct H.
      exists (map (fun x => exist (fun xx => fst xx = snd xx) (x, x) eq_refl) fx).
      split; (apply eq_trans with
                  (y := map (fun x => fst (` (exist (fun xy => fst xy = snd xy) (x, x) eq_refl))) fx);
              [apply MAP_COMPOSE | apply MAP_ID]).
    - destruct H as [fr [[] []]].
      f_equal. extensionality xy. apply (proj2_sig xy).
  Qed.

  Lemma PROD_UNIQUE X Y (fp1 fp2 : F (prod X Y))
        (EQ1 : map fst fp1 = map fst fp2) (EQ2 : map snd fp1 = map snd fp2) :
    fp1 = fp2.
  Proof.
    set (ff1 := map (fun xy => (bool_rect (bool_rect (fun _ => Type) X Y) (fst xy) (snd xy) 
             )) fp1).
    set (ff2 := map (fun xy => (bool_rect (bool_rect (fun _ => Type) X Y) (fst xy) (snd xy) 
             )) fp2).
    assert (ff1 = ff2). {
      apply(FUN_UNIQUE true). intro b.
      destruct b; unfold ff1, ff2; repeat rewrite MAP_COMPOSE; [apply EQ1 | apply EQ2].
    }
    set (f_equal (map (fun f : (forall b : bool, bool_rect (fun _ : bool => Type) X Y b) => (f true, f false) : X*Y)) H).
    unfold ff1, ff2 in e. repeat rewrite MAP_COMPOSE in e. simpl in e.
    replace (fun x : X * Y => (fst x, snd x)) with (@id (prod X Y)) in e.
    - repeat rewrite MAP_ID in e. apply e.
    - extensionality xy. destruct xy. reflexivity.
  Qed.
  
  Definition pullback2 X Y C (fx : F X) (fy : F Y)
             (f : X -> C) (g : Y -> C) (EQ : map f fx = map g fy) :
    F (sig (fun xy => f (fst xy) = g (snd xy))) :=
    map (fun (x : {x : forall a, bool_rect (fun _ => Type) X Y a |
                   forall a1 a2,
                     bool_rect (fun b => bool_rect (fun _ => Type) X Y b -> C) f g a1 (x a1) =
                     bool_rect (fun b => bool_rect (fun _ => Type) X Y b -> C) f g a2 (x a2)})
         => exist _ (proj1_sig x true, proj1_sig x false) (proj2_sig x true false))
        (pullback (bool_rect _ X Y) (bool_rect _ fx fy) (bool_rect _ f g)
                  (bool_rect _ eq_refl EQ)). 

  Arguments pullback2 [_ _ _ _ _ _ _] EQ.

  Lemma PULLBACK2 X Y C (fx : F X) (fy : F Y)
        (f : X -> C) (g : Y -> C) (EQ : map f fx = map g fy):
    map (fun x => fst (proj1_sig x)) (pullback2 EQ) = fx /\
    map (fun x => snd (proj1_sig x)) (pullback2 EQ) = fy.
  Proof.
    split.
    - unfold pullback2. rewrite MAP_COMPOSE.
      apply (PULLBACK _ (bool_rect (fun a => F (bool_rect _ X Y a)) fx fy)
                      (bool_rect _ f g) (bool_rect _ eq_refl EQ) true).
    - unfold pullback2. rewrite MAP_COMPOSE.
      apply (PULLBACK _ (bool_rect (fun a => F (bool_rect _ X Y a)) fx fy)
                      (bool_rect _ f g) (bool_rect _ eq_refl EQ) false).
  Qed.

  Arguments PULLBACK2 [_ _ _ _ _ _ _] EQ.

  Lemma REL_JOIN X Y (R1 R2 : X -> Y -> Prop) (fx : F X) (fy : F Y) :
    allR R1 fx fy -> allR R2 fx fy -> allR (fun x y => R1 x y /\ R2 x y) fx fy.
  Proof.
    intros REL1 REL2.
    destruct REL1 as [fr1 [EQ1 EQ2]]. destruct REL2 as [fr2 [EQ3 EQ4]].    
    assert (EQ : map (@proj1_sig _ _) fr1 = map (@proj1_sig _ _) fr2). {
      apply PROD_UNIQUE.
      - repeat rewrite MAP_COMPOSE. apply (eq_trans EQ1 (eq_sym EQ3)).
      - repeat rewrite MAP_COMPOSE. apply (eq_trans EQ2 (eq_sym EQ4)).
    }
    exists (map
              (fun xy : {xy
                         : {xy : X * Y | R1 (fst xy) (snd xy)} *
                           {xy : X * Y | R2 (fst xy) (snd xy)} |
                         ` (fst xy) = ` (snd xy)} =>
                 exist
                   (fun xy0 : X * Y =>
                      R1 (fst xy0) (snd xy0) /\ R2 (fst xy0) (snd xy0))
                   (` (snd (` xy)))
                   (conj
                      (eq_rect (` (fst (` xy)))
                               (fun xy0 : X * Y => R1 (fst xy0) (snd xy0))
                               (proj2_sig (fst (` xy))) (` (snd (` xy))) 
                               (proj2_sig xy)) (proj2_sig (snd (` xy))))) 
              (pullback2 EQ)).
    destruct (PULLBACK2 EQ) as [EQ5 EQ6].
    split; rewrite MAP_COMPOSE; [rewrite <- EQ1 | rewrite <- EQ2];
      pattern fr1 at 2; rewrite <- EQ5; rewrite MAP_COMPOSE; simpl;
        f_equal; extensionality xy; f_equal;
          symmetry; apply (proj2_sig xy).
  Qed.

  Lemma ALLNR_JOIN A B (T : A -> Type) (fx : forall a, F (T a))
        (R : B -> (forall a, T a) -> Prop) :
    (forall b, allNR _ (R b) fx) -> A -> B -> (allNR _ (fun f => forall b, R b f) fx).
  Proof.
    intros ALLR a0 b0. 
    set (fun b => map (@proj1_sig _ _) (proj1_sig (ALLR b))).
    assert (forall (b : B) (a : A), map (fun f => f a) (f b) = fx a). {
      intros b a. unfold f. rewrite MAP_COMPOSE. 
      apply (proj2_sig (ALLR b)).
    }

    assert (forall b, f b0 = f b). {
      intro b. apply (FUN_UNIQUE a0).
      intro a. apply (eq_trans (H b0 a) (eq_sym (H b a))).
    }

    unfold f in H0. 
    set (PULLBACK (fun b => {x : forall a : A, T a | R b x}) (fun b => ` (ALLR b))
                    (fc := map (proj1_sig (P:=R b0)) (` (ALLR b0))) (fun b => (proj1_sig (P:=R b))) H0). 

    simpl in *.
    
    set (pullback (fun b : B => {x : forall a0 : A, T a0 | R b x})
          (fun b : B => ` (ALLR b)) (fun b : B => proj1_sig (P:=R b)) H0).
    simpl in f0.

    unfold allNR. 

    exists (map (fun
        f : {x : forall a : B, {x : forall a1 : A, T a1 | R a x} |
            forall a1 a2 : B, ` (x a1) = ` (x a2)} =>
      exist (fun f0 : forall a : A, T a => forall b : B, R b f0) 
        (` ((` f) b0))
        (fun b : B =>
         eq_rect (` ((` f) b)) (fun x : forall a1 : A, T a1 => R b x)
           (proj2_sig ((` f) b)) (` ((` f) b0)) (proj2_sig f b b0))) f0).

    intro a. rewrite MAP_COMPOSE. fold f0 in e.
    simpl.

    specialize (e b0).
    apply (f_equal (map (fun x => proj1_sig x a))) in e. rewrite MAP_COMPOSE in e.
    simpl in *.
    
    apply eq_trans with (y := map (fun x : {x : forall x0 : A, T x0 | R b0 x} => (` x) a) (` (ALLR b0))).
    apply e.

    rewrite <- (H b0 a). unfold f.
    rewrite MAP_COMPOSE. reflexivity.
  Qed.

  Lemma PULLBACK_UNIQUE A (X : A -> Type) C (fx : forall a, F (X a))
        (fc : F C) (f : forall a, X a -> C)
        (EQ : forall a, fc = map (f a) (fx a))
        (fp : F (sig (fun x => forall a1 a2, f a1 (x a1) = f a2 (x a2))))
        (PB : forall a, map (fun x => proj1_sig x a) fp = fx a) (a0 : A) :
    allR (fun fx fy => proj1_sig fx = proj1_sig fy) fp (pullback _ fx f EQ).
  Proof.
    assert (map
       (proj1_sig
          (P:=fun x : forall x : A, X x =>
              forall a1 a2 : A, f a1 (x a1) = f a2 (x a2))) fp =
     map
       (proj1_sig
          (P:=fun x : forall a : A, X a =>
              forall a1 a2 : A, f a1 (x a1) = f a2 (x a2))) 
       (pullback X fx f EQ)). { 
      apply (FUN_UNIQUE a0).
      intro a. repeat rewrite MAP_COMPOSE.
      apply (eq_trans (PB a) (eq_sym (PULLBACK _ _ _ EQ a))).
    }
    exists (pullback2 H). apply (PULLBACK2 H).
  Qed.

  Lemma REL_MONOTONE X Y (R R' : X -> Y -> Prop)
        (UPP : forall x y, R x y -> R' x y) fx fy :
    allR R fx fy -> allR R' fx fy.
  Proof.
    intro. destruct H as [fr [EQ1 EQ2]].
    exists (map
              (fun xy : {xy : X * Y | R (fst xy) (snd xy)} =>
                 exist (fun xy0 : X * Y => R' (fst xy0) (snd xy0)) 
                       (` xy) (UPP (fst (` xy)) (snd (` xy)) (proj2_sig xy))) fr).
    split.
    - apply eq_trans with (y := map (fun xy : {xy : X * Y | R (fst xy) (snd xy)} => fst (` xy)) fr).
      + apply MAP_COMPOSE.
      + apply EQ1.
    - apply eq_trans with (y := map (fun xy : {xy : X * Y | R (fst xy) (snd xy)} => snd (` xy)) fr).
      + apply MAP_COMPOSE.
      + apply EQ2.
  Qed.

  Lemma REL_EQ X Y (R R' : X -> Y -> Prop)
        (EQ : forall x y, R x y <-> R' x y)
        (fx : F X) (fy : F Y) :
    allR R fx fy <-> allR R' fx fy.
  Proof.
    split; apply REL_MONOTONE; apply EQ.
  Qed.

  Lemma MAP_POINTWISE X Y (f1 f2 : X -> Y) (fx : F X)
        (PW : forall (x : X), default_mem fx x -> f1 x = f2 x)
    : map f1 fx = map f2 fx.
  Proof.
    apply ALLP_EQ in PW. destruct PW as [fp []].
    repeat rewrite MAP_COMPOSE. f_equal.
    extensionality x. apply (proj2_sig x).
  Qed.

  Lemma MAP_INJECTIVE X Y (f : X -> Y)
        (INJ : forall (x1 x2 : X), f x1 = f x2 -> x1 = x2) :
    forall fx1 fx2, map f fx1 = map f fx2 -> fx1 = fx2.
  Proof.
    intros fx1 fx2 EQ.
    destruct (PULLBACK2 EQ) as [EQ1 EQ2]. destruct EQ1, EQ2.
    f_equal. extensionality xy. apply (INJ _ _ (proj2_sig xy)).
  Qed.

  Lemma MAP_MEM_INJECTIVE X Y (f : X -> Y) (fx : F X)
        (INJ : forall (x : X), default_mem fx x -> forall x', f x = f x' -> x = x')
    : forall fx', map f fx = map f fx' -> fx = fx'.
  Proof.
    apply ALLP_EQ in INJ. destruct INJ as [fp []].
    intros fx' EQ. rewrite MAP_COMPOSE in EQ.
    destruct (PULLBACK2 EQ) as [EQ1 EQ2]. destruct EQ1, EQ2.
    rewrite MAP_COMPOSE. f_equal.
    extensionality x. apply (proj2_sig (fst (proj1_sig x)) _ (proj2_sig x)). 
  Qed.

  Lemma MEM_MAP (X Y : Type) (f: X -> Y) (fx : F X) (x : X) :
    default_mem fx x -> default_mem (map f fx) (f x).
  Proof.
    intros MEM Pr ALLP. destruct ALLP as [fp EQ]. 
    apply (MEM (fun x => Pr (f x))).
    exists (map
            (fun xy : {xy : {x : Y | Pr x} * X | ` (fst xy) = f (snd xy)} =>
             exist (fun x0 : X => Pr (f x0)) (snd (` xy))
               (eq_rect (` (fst (` xy))) Pr (proj2_sig (fst (` xy)))
                  (f (snd (` xy))) (proj2_sig xy))) (pullback2 EQ)).
    rewrite MAP_COMPOSE.
    apply (proj2 (PULLBACK2 EQ)).
  Qed.


  Lemma MEM_MAP_INJECTIVE (X Y : Type) (f: X -> Y)
        (INJ : forall (x1 x2 : X), f x1 = f x2 -> x1 = x2)
        (fx : F X) (x : X) :
    default_mem (map f fx) (f x) -> default_mem fx x.
  Proof.
    intros MEM Pr ALLP.
    destruct ALLP as [fp EQ].
    specialize (MEM (fun y => exists x, f x = y /\ Pr x)). simpl in MEM.
    assert (H : allP (fun y : Y => exists x : X, f x = y /\ Pr x) (map f fx)). {
      exists (map (fun x' : {x : X | Pr x} =>
                     exist (fun y : Y => exists x0 : X, f x0 = y /\ Pr x0) 
                           (f (` x'))
                           (ex_intro (fun x0 : X => f x0 = f (` x') /\ Pr x0) 
                                     (` x') (conj eq_refl (proj2_sig x')))) fp).
      rewrite <- EQ. repeat rewrite MAP_COMPOSE. reflexivity.
    }
    destruct (MEM H) as [x' [EQ' PR]].
    destruct (INJ _ _ EQ'). apply PR.
  Qed.

  Lemma MAP_REL X1 Y1 X2 Y2 (f: X1 -> X2) (g: Y1 -> Y2)
        (R : X2 -> Y2 -> Prop) (fx : F X1) (fy : F Y1) 
    : allR (fun (x : X1) (y : Y1) => R (f x) (g y)) fx fy <->
      allR R (map f fx) (map g fy).
  Proof.
    split; intro.
    - destruct H as [fr [EQ1 EQ2]]. 
      rewrite <- EQ1. rewrite <- EQ2. rewrite MAP_COMPOSE. rewrite MAP_COMPOSE.
      exists (map (fun xy : {xy : X1 * Y1 | R (f (fst xy)) (g (snd xy))} => exist (fun xy0 => R (fst xy0) (snd xy0))
                                   (f (fst (` xy)), g (snd (` xy))) 
                                   (proj2_sig xy)) fr).
      split; apply MAP_COMPOSE.
    - destruct H as [fr [EQ1 EQ2]]. unfold allR.
      destruct (PULLBACK2 EQ1) as [PEQ1 PEQ2].
      destruct (PULLBACK2 EQ2) as [PEQ3 PEQ4].
      destruct (PULLBACK2 (eq_trans PEQ1 (eq_sym PEQ3))) as [PEQ5 PEQ6].
      exists (map (fun
                      xy : {xy
                            : {xy : {xy : X2 * Y2 | R (fst xy) (snd xy)} * X1
                              | fst (` (fst xy)) = f (snd xy)} *
                              {xy : {xy : X2 * Y2 | R (fst xy) (snd xy)} * Y1
                              | snd (` (fst xy)) = g (snd xy)} |
                            (fun
                                x : {xy0
                                     : {xy0 : X2 * Y2 | R (fst xy0) (snd xy0)} *
                                       X1 | fst (` (fst xy0)) = f (snd xy0)} =>
                                fst (` x)) (fst xy) =
                            (fun
                                x : {xy0
                                     : {xy0 : X2 * Y2 | R (fst xy0) (snd xy0)} *
                                       Y1 | snd (` (fst xy0)) = g (snd xy0)} =>
                                fst (` x)) (snd xy)} =>
                      exist
                        (fun xy0 : X1 * Y1 => R (f (fst xy0)) (g (snd xy0)))
                        (snd (` (fst (` xy))), snd (` (snd (` xy))))
                        (eq_ind (fst (` (fst (` (fst (` xy))))))
                                (fun x : X2 => R x (g (snd (` (snd (` xy))))))
                                (eq_ind (snd (` (fst (` (snd (` xy))))))
                                        (R (fst (` (fst (` (fst (` xy)))))))
                                        (eq_ind (fst (` (fst (` xy))))
                                                (fun
                                                    x : {xy0 : X2 * Y2 | R (fst xy0) (snd xy0)}
                                                  =>
                                                    R (fst (` (fst (` (fst (` xy))))))
                                                      (snd (` x)))
                                                (proj2_sig (fst (` (fst (` xy)))))
                                                (fst (` (snd (` xy)))) 
                                                (proj2_sig xy)) (g (snd (` (snd (` xy)))))
                                        (proj2_sig (snd (` xy))))
                                (f (snd (` (fst (` xy))))) 
                                (proj2_sig (fst (` xy)))))
                  (pullback2 (eq_trans PEQ1 (eq_sym PEQ3)))).
      repeat rewrite MAP_COMPOSE. Opaque pullback2 map. simpl. split.
      + rewrite <- PEQ2. pattern (pullback2 EQ1) at 3.
        rewrite <- PEQ5. rewrite MAP_COMPOSE. reflexivity.
      + rewrite <- PEQ4. pattern (pullback2 EQ2) at 4.
        rewrite <- PEQ6. rewrite MAP_COMPOSE. reflexivity.
  Qed.

(*
  Definition eq_fun1 X (fx fy : F X) :
    fx = fy ->
    sigT (fun fe : F (sigT (fun x : X * X => fst x = snd x)) =>
             prod (map (fun x => fst (projT1 x)) fe = fx)
                  (map (fun x => snd (projT1 x)) fe = fy)).
  Proof.
    intro e.
    exists (map (fun x => existT (fun xx => fst xx = snd xx) (x, x) eq_refl) fx).
    split.
    - apply eq_trans with (y := map id fx).
      + apply MAP_COMPOSE.
      + apply MAP_ID.
    - apply eq_trans with (y := map id fx).
      + apply MAP_COMPOSE.
      + apply (eq_trans (MAP_ID fx) e).
  Defined.

  Definition eq_fun2 X (fx fy : F X) :
    sigT (fun fe : F (sigT (fun x : X * X => fst x = snd x)) =>
            prod (map (fun x => fst (projT1 x)) fe = fx)
                 (map (fun x => snd (projT1 x)) fe = fy)) ->
    fx = fy.
  Proof.
    intro R.
    apply (eq_trans (eq_trans (eq_sym (fst (projT2 R))) (f_equal (fun f => f (projT1 R)) (f_equal map (functional_extensionality
        (fun x : {x : X * X & fst x = snd x} => fst (projT1 x))
        (fun x : {x : X * X & fst x = snd x} => snd (projT1 x))
        (@projT2 _ _))))) (snd (projT2 R))). 
  Defined.

  Definition eq_bij1 X (fx fy : F X) (e : fx = fy) :
    eq_fun2 (eq_fun1 e) = e.
  Proof.
    unfold eq_fun2, eq_fun1. simpl.
    
    set (f1 := (fun x : {x : X * X & fst x = snd x} => fst (projT1 x))).
    set (f2 := (fun x : {x : X * X & fst x = snd x} => snd (projT1 x))).
    
    set (i := fun x : X =>
              @existT (prod X X)
                (fun xx : prod X X => @eq X (@fst X X xx) (@snd X X xx))
                (@pair X X x x) (@eq_refl X x)).

    assert
      (eq_trans
       (f_equal (fun f : F {x : X * X & fst x = snd x} -> F X => f (map i fx))
          (f_equal map
             (functional_extensionality f1 f2
                (projT2 (P:=fun x : X * X => fst x = snd x)))))
           (MAP_COMPOSE i f2 fx) = (MAP_COMPOSE i f1 fx)).





    assert (eq_trans (f_equal (fun f : F {x : X * X & fst x = snd x} -> F X => f (map i fx))
          (f_equal map e)) (MAP_COMPOSE i f2 fx) = MAP_COMPOSE i f1 fx). {

      replace (eq_trans
    (f_equal (fun f : F {x : X * X & fst x = snd x} -> F X => f (map i fx))
       (f_equal map e)) (MAP_COMPOSE i f2 fx)) with
    (f_equal (fun f : F {x : X * X & fst x = snd x} -> F X => f (map i fx))
       (f_equal map e)) (MAP_COMPOSE i f2 fx)).


  Definition eq_bij1 X (fx fy : F X) (e : fx = fy) :
    eq_fun2 (eq_fun1 e) = e.
  Proof.
    destruct e. simpl. unfold eq_fun2. simpl.

    set (f1 := (fun x : {x : X * X & fst x = snd x} => fst (projT1 x))).
    set (f2 := (fun x : {x : X * X & fst x = snd x} => snd (projT1 x))).
    
    set (i := fun x : X =>
              @existT (prod X X)
                (fun xx : prod X X => @eq X (@fst X X xx) (@snd X X xx))
                (@pair X X x x) (@eq_refl X x)).

    set (functional_extensionality f1 f2 (@projT2 _ _)).

    assert (eq_trans (f_equal (fun f : F {x : X * X & fst x = snd x} -> F X => f (map i fx))
          (f_equal map e)) (MAP_COMPOSE i f2 fx) = MAP_COMPOSE i f1 fx). {

      replace (eq_trans
    (f_equal (fun f : F {x : X * X & fst x = snd x} -> F X => f (map i fx))
       (f_equal map e)) (MAP_COMPOSE i f2 fx)) with
    (f_equal (fun f : F {x : X * X & fst x = snd x} -> F X => f (map i fx))
       (f_equal map e)) (MAP_COMPOSE i f2 fx)).

  Definition eq_bij2 X (fx fy : F X) (e : sigT (fun fe : F (sigT (fun x : X * X => fst x = snd x)) =>
            prod (map (fun x => fst (projT1 x)) fe = fx)
                 (map (fun x => snd (projT1 x)) fe = fy))) :
    eq_fun1 (eq_fun2 e) = e.
  Proof.
    destruct e. destruct p. destruct e. destruct e0. unfold eq_fun2. simpl.
    unfold eq_fun1. simpl.
  Admitted.

*)

End PULLBACK_FUNCTOR_FACTS.
