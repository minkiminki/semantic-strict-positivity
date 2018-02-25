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

  Lemma painup_red A B (FIX : forall o, pa_Mu (A /+\ B) o -> A o)
        o m :
    painup A FIX (Con _ o m) =
    Con
      (fun o0 => Comp (fun o1 => Prod (Ident o1) (Const (A o1 * B o1))) (F o0)) o
      (map (fun i x => (painup A FIX (fst x), (parec A FIX (fst x), (snd x)))) m).
  Proof.
    unfold painup at 1. rewrite prim_rec_red. simpl. rewrite MAP_COMPOSE.
    reflexivity.
  Qed.

  Lemma parec_red A B (FIX : forall o, pa_Mu (A /+\ B) o -> A o)
        o m :
    parec A FIX (Con _ o m) =
    FIX o (Con
             (fun o0 => Comp (fun o1 => Prod (Ident o1) (Const (A o1 * B o1))) (F o0)) o
             (map (fun i x => (painup A FIX (fst x), (parec A FIX (fst x), (snd x)))) m)).
  Proof.
    unfold parec at 1. f_equal. apply painup_red.
  Qed.

End PAIN.
