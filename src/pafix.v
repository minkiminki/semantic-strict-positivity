Require Import FunctionalExtensionality.
Require Import Program.
Require Import paco.

Set Implicit Arguments.
Set Primitive Projections.

Require Import index wf IFunctor ISPFunctor iinductive iso icombinator1.

Section PAIN.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.

  Definition pa_Mu (R : O -> Type) : O -> Type :=
    Mu (fun o => Comp (fun o1 => Prod (Ident o1) (Const (R o1))) (F o)).

  Notation "A /+\ B" := (fun o => prod (A o) (B o)) (at level 50, left associativity)
                        : ssp_scope. 

  Open Scope ssp_scope.

  Definition painup (A B : O -> Type)
             (FIX : forall o, pa_Mu (A /+\ B) o -> A o) :
    forall o, pa_Mu B o -> pa_Mu (A /+\ B) o :=
    prim_rec (pa_Mu (A /+\ B))
             (fun o (fx : Comp (fun o1 : O => Prod (Ident o1) (Const (B o1))) 
                               (F o) (pa_Mu (A /+\ B))) =>
                Con (fun o0 => Comp (fun o1 => Prod (Ident o1)
                                                    (Const (A o1 * B o1))) (F o0))
                    o (map (fun i x => (fst x, (FIX i (fst x), snd x))) fx)).

  Definition parec (A B : O -> Type) (FIX : forall o, pa_Mu (A /+\ B) o -> A o) :
    forall o, pa_Mu B o -> A o :=
    fun o (m : pa_Mu B o) => FIX o (painup A FIX m).

  Goal True. apply I. Qed.

  Definition value (R : O -> Type) : forall o, pa_Mu R o -> Mu F o :=
    prim_rec (Mu F)
             (fun o (fx : F o (Mu F /+\ R)) => Con F o (map (fun _ => fst) fx)).

  Definition add_null : forall o, Mu F o -> pa_Mu (fun _ => unit) o :=
    prim_rec (pa_Mu (fun _ => unit))
             (fun o fx =>
                Con (fun o0 => Comp (fun o1 => Prod (Ident o1) (Const ())) (F o0)) o
                    (map (fun i x => (x, ())) fx)).

  Goal True. apply I. Qed.

  Lemma value_retraction :
    forall o (fx : Mu F o), value (add_null fx) = fx.
  Proof.
    apply fun_unique with (FIX := @Con _ _ _).
    - intros. unfold add_null, value. repeat rewrite prim_rec_red. simpl.
      repeat rewrite MAP_COMPOSE. reflexivity.
    - intros. f_equal. symmetry. apply MAP_ID.
  Qed.

  Lemma add_retraction :
    forall o (fx : pa_Mu (fun _ => unit) o), add_null (value fx) = fx. 
  Proof.
    apply fun_unique with (FIX := @Con _ _ _).
    - intros. unfold add_null, value. repeat rewrite prim_rec_red. simpl.
      repeat rewrite MAP_COMPOSE. simpl. f_equal. f_equal.
      extensionality i. extensionality x. destruct x as [x []]. reflexivity.
    - intros. symmetry. f_equal. apply MAP_ID.
  Qed.

  Definition paindown A B : forall o, pa_Mu (A /+\ B) o -> pa_Mu B o :=
    prim_rec (pa_Mu B)
             (fun o (fx : F o (fun i : O => (pa_Mu B i * (A i * B i))%type)) =>
                Con (fun o0 => Comp (fun o1=> Prod (Ident o1) (Const (B o1))) (F o0))
                    o (map (fun i x => (fst x, snd (snd x))) fx)).

  Lemma down_retraction A B (FIX : forall o, pa_Mu (A /+\ B) o -> A o) :
    forall o (m : pa_Mu B o), paindown A B (painup A FIX m) = m.
  Proof.
    apply fun_unique with (FIX := @Con _ _ _).
    - intros. unfold paindown, painup. repeat rewrite prim_rec_red. simpl.
      repeat rewrite MAP_COMPOSE. reflexivity.
    - intros. f_equal. symmetry. apply MAP_ID.
  Qed.

  Lemma pacorec_red A B (FIX : forall o, pa_Mu (A /+\ B) o -> A o)
        o m :
    parec A FIX (Con _ o m) = parec A FIX (Con _ o m). 

    unfold parec, painup at 1. rewrite prim_rec_red. simpl.
    repeat rewrite MAP_COMPOSE. simpl.

    set (painup A FIX). unfold painup in p.

    set (FIX o
    (Con
       (fun o0 : O =>
        Comp (fun o1 : O => Prod (Ident o1) (Const (A o1 * B o1))) (F o0)) o
       (map
          (fun (i : O)
             (x : Prod (Ident i) (Const (B i))
                    (Mu
                       (fun o0 : O =>
                        Comp (fun o1 : O => Prod (Ident o1) (Const (B o1))) (F o0))))
           =>
           (prim_rec (pa_Mu (A /+\ B))
              (fun (o0 : O)
                 (fx : Comp (fun o1 : O => Prod (Ident o1) (Const (B o1))) 
                         (F o0) (pa_Mu (A /+\ B))) =>
               Con
                 (fun o1 : O =>
                  Comp (fun o2 : O => Prod (Ident o2) (Const (A o2 * B o2))) (F o1))
                 o0
                 (map
                    (fun (i0 : O)
                       (x0 : pa_Mu (A /+\ B) i0 * Const (B i0) (pa_Mu (A /+\ B)))
                     => (fst x0, (FIX i0 (fst x0), snd x0))) fx)) 
              (fst x),
           (FIX i
              (prim_rec (pa_Mu (A /+\ B))
                 (fun (o0 : O)
                    (fx : Comp (fun o1 : O => Prod (Ident o1) (Const (B o1)))
                            (F o0) (pa_Mu (A /+\ B))) =>
                  Con
                    (fun o1 : O =>
                     Comp (fun o2 : O => Prod (Ident o2) (Const (A o2 * B o2)))
                       (F o1)) o0
                    (map
                       (fun (i0 : O)
                          (x0 : pa_Mu (A /+\ B) i0 * Const (B i0) (pa_Mu (A /+\ B)))
                        => (fst x0, (FIX i0 (fst x0), snd x0))) fx)) 
                 (fst x)), id (snd x)))) m))).

rewrite prim_rec_red.
    

    assert (A o). -

      
    

    simpl in *. 
    

    set (parec A FIX
    (Con (fun o0 : O => Comp (fun o1 : O => Prod (Ident o1) (Const (B o1))) (F o0))
       o m)).
     simpl in *.


  Lemma pacorec_red A B (FIX : forall o, pa_Mu (A /+\ B) o -> A o)
        o m :
    parec A FIX (Con _ o m) = parec A FIX (Con _ o m). 
    set (parec A FIX
    (Con (fun o0 : O => Comp (fun o1 : O => Prod (Ident o1) (Const (B o1))) (F o0))
       o m)).
     simpl in *.

parec A B FIX o (Con m).
    Des (pacorec A B FIX o a) = 
    map (fun i (x : pa_Nu (A \+/ B) i + (A i + B i)) =>
           match x with
           | inl n => inl (pacodown A B FIX n)
           | inr (inl a) => inl (pacorec A B FIX i a)
           | inr (inr b) => inr b
           end) (Des (FIX o a)).
  Proof.
    unfold pacorec, pacodown at 1. rewrite corec_red. simpl.
    rewrite MAP_COMPOSE. simpl.
    f_equal. extensionality i. extensionality x.
    destruct x as [x | [ax | bx]]; reflexivity.
  Qed.

  Lemma pacodown_red A B (FIX : forall o, A o -> pa_Nu (A \+/ B) o) o
        (fx : pa_Nu (A \+/ B) o) :
    Des (pacodown A B FIX fx) =
    map (fun i (x : pa_Nu (A \+/ B) i + (A i + B i)) =>
           match x with
           | inl n => inl (pacodown A B FIX n)
           | inr (inl a) => inl (pacorec A B FIX i a)
           | inr (inr b) => inr b
           end) (Des fx).
  Proof.
    unfold pacodown, pacorec at 1. rewrite corec_red. simpl.
    rewrite MAP_COMPOSE. simpl.
    f_equal. extensionality i. extensionality x.
    destruct x as [x | [ax | bx]]; reflexivity.
  Qed.

End PACO.
