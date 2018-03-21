Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import Functor hott pullback_functor.

Class PB_SFunctor (F : Type -> Type) `{Fn : SFunctor F} :=
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

    TAG X (fx : F X) :
      map (@proj1_sig _ _) (tag _ fx) = fx;
    ALLP_EQ X (Pr : X -> Prop) :
      forall (fx: F X), allP Pr fx <-> (forall x, mem fx x -> Pr x);
    ALLR_EQ X Y (R : X -> Y -> Prop) :
      forall (fx : F X) (fy : F Y),
        allR R fx fy <-> rel R fx fy;

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

Arguments MAP_ID {_ _} [_].

Arguments PB_SFunctor F {_}.

Section PULLBACK_SFUNCTOR_FACTS.

  Variable F : Type -> Type.
  Context `{PBSF: PB_SFunctor F}.

  Global Instance PBF : PB_Functor F :=
    Build_PB_Functor _ MAP_COMPOSE (@MAP_ID _ _ _) pullback PULLBACK FUN_UNIQUE.

  Lemma MEM_EQ X (fx : F X) (x : X) :
      mem fx x <-> default_mem fx x.
  Proof.
    split; intro.
    - intros Pr ALLP. apply (proj1 (@ALLP_EQ _ _ _ _ Pr fx) ALLP _ H).
    - apply (H (mem fx)).
      exists (tag _ fx). apply TAG.
  Qed.

  Definition default_tag X (fx : F X) : F (sig (mem fx)) :=
    map (fun x => exist (mem fx) (` x) (proj2 (MEM_EQ fx (` x)) (proj2_sig x))) (default_tag X fx).

  Lemma DEFAULT_TAG X (fx : F X) :
    map (proj1_sig (P:=mem fx)) (default_tag fx) = fx.
  Proof.
    unfold default_tag. rewrite MAP_COMPOSE.
    simpl. apply DEFAULT_TAG.
  Qed.

  Lemma REL_EQ_EQ X (fx fy : F X) :
    fx = fy <-> rel eq fx fy.
  Proof.
    split; intro.
    - apply ALLR_EQ. apply (REL_EQ_EQ (PBF := PBF)). apply H.
    - apply ALLR_EQ in H. apply (REL_EQ_EQ (PBF := PBF)). apply H.
  Qed.

  Lemma PROD_UNIQUE X Y (fp1 fp2 : F (prod X Y))
        (EQ1 : map fst fp1 = map fst fp2) (EQ2 : map snd fp1 = map snd fp2) :
    fp1 = fp2.
  Proof.
    apply (PROD_UNIQUE (PBF := PBF) _ _ _ _ EQ1 EQ2). 
  Qed.
  
  Definition pullback2 X Y C (fx : F X) (fy : F Y)
             (f : X -> C) (g : Y -> C) (EQ : map f fx = map g fy) :
    F (sig (fun xy => f (fst xy) = g (snd xy))) := pullback2 (PBF:=PBF) _ _ _ _ EQ.

  Arguments pullback2 [_ _ _ _ _ _ _] EQ.

  Lemma PULLBACK2 X Y C (fx : F X) (fy : F Y)
        (f : X -> C) (g : Y -> C) (EQ : map f fx = map g fy):
    map (fun x => fst (proj1_sig x)) (pullback2 EQ) = fx /\
    map (fun x => snd (proj1_sig x)) (pullback2 EQ) = fy.
  Proof.
    unfold pullback. apply PULLBACK2.
  Qed.

  Arguments PULLBACK2 [_ _ _ _ _ _ _] EQ.

  Lemma REL_JOIN X Y (R1 R2 : X -> Y -> Prop) (fx : F X) (fy : F Y) :
    rel R1 fx fy -> rel R2 fx fy -> rel (fun x y => R1 x y /\ R2 x y) fx fy.
  Proof.
    intros REL1 REL2.
    apply ALLR_EQ in REL1. apply ALLR_EQ in REL2. apply ALLR_EQ.
    apply (REL_JOIN (PBF:=PBF)); [apply REL1 | apply REL2].
  Qed.

  Lemma ALLNR_JOIN A B (T : A -> Type) (fx : forall a, F (T a))
        (R : B -> (forall a, T a) -> Prop) :
    (forall b, allNR _ (R b) fx) -> A -> B -> (allNR _ (fun f => forall b, R b f) fx).
  Proof.
    apply (ALLNR_JOIN (PBF:=PBF)).
  Qed.

  Lemma PULLBACK_UNIQUE A (X : A -> Type) C (fx : forall a, F (X a))
        (fc : F C) (f : forall a, X a -> C)
        (EQ : forall a, fc = map (f a) (fx a))
        (fp : F (sig (fun x => forall a1 a2, f a1 (x a1) = f a2 (x a2))))
        (PB : forall a, map (fun x => proj1_sig x a) fp = fx a) (a0 : A) :
    rel (fun fx fy => proj1_sig fx = proj1_sig fy) fp (pullback _ fx f EQ).
  Proof.
    apply ALLR_EQ.
    apply (PULLBACK_UNIQUE (PBF:=PBF) X _ _ EQ fp PB a0).
  Qed.

  Lemma REL_MONOTONE X Y (R R' : X -> Y -> Prop)
        (UPP : forall x y, R x y -> R' x y) fx fy :
    rel R fx fy -> rel R' fx fy.
  Proof.
    intro. apply ALLR_EQ in H. apply ALLR_EQ.
    apply (REL_MONOTONE _ UPP H).
  Qed.

  Lemma REL_EQ X Y (R R' : X -> Y -> Prop)
        (EQ : forall x y, R x y <-> R' x y)
        (fx : F X) (fy : F Y) :
    rel R fx fy <-> rel R' fx fy.
  Proof.
    split; apply REL_MONOTONE; apply EQ.
  Qed.

  Lemma MAP_POINTWISE X Y (f1 f2 : X -> Y) (fx : F X)
        (PW : forall (x : X), mem fx x -> f1 x = f2 x)
    : map f1 fx = map f2 fx.
  Proof.
    apply (MAP_POINTWISE (PBF:=PBF)).
    intros x MEM. apply PW. apply MEM_EQ. apply MEM.
  Qed.

  Lemma MAP_INJECTIVE X Y (f : X -> Y)
        (INJ : forall (x1 x2 : X), f x1 = f x2 -> x1 = x2) :
    forall fx1 fx2, map f fx1 = map f fx2 -> fx1 = fx2.
  Proof.
    apply (MAP_INJECTIVE (PBF:=PBF) _ INJ).
  Qed.

  Lemma MAP_MEM_INJECTIVE X Y (f : X -> Y) (fx : F X)
        (INJ : forall (x : X), mem fx x -> forall x', f x = f x' -> x = x')
    : forall fx', map f fx = map f fx' -> fx = fx'.
  Proof.
    apply (MAP_MEM_INJECTIVE (PBF:=PBF)).
    intros x MEM. apply INJ. apply MEM_EQ. apply MEM.
  Qed.

  Lemma MEM_MAP (X Y : Type) (f: X -> Y) (fx : F X) (x : X) :
    mem fx x -> mem (map f fx) (f x).
  Proof.
    intro MEM. apply MEM_EQ. apply MEM_EQ in MEM.
    apply (MEM_MAP (PBF:=PBF) f MEM).
  Qed.

  Lemma MEM_MAP_INJECTIVE (X Y : Type) (f: X -> Y)
        (INJ : forall (x1 x2 : X), f x1 = f x2 -> x1 = x2)
        (fx : F X) (x : X) :
    mem (map f fx) (f x) -> mem fx x.
  Proof.
    intro MEM. apply MEM_EQ. apply MEM_EQ in MEM.
    apply (MEM_MAP_INJECTIVE (PBF:=PBF) f INJ _ MEM).
  Qed.

  Lemma MAP_REL X1 Y1 X2 Y2 (f: X1 -> X2) (g: Y1 -> Y2)
        (R : X2 -> Y2 -> Prop) (fx : F X1) (fy : F Y1) 
    : rel (fun (x : X1) (y : Y1) => R (f x) (g y)) fx fy <->
      rel R (map f fx) (map g fy).
  Proof.
    split; intro; apply ALLR_EQ in H; apply ALLR_EQ;
      apply (MAP_REL (PBF:=PBF) f g), H.
  Qed.

End PULLBACK_SFUNCTOR_FACTS.
