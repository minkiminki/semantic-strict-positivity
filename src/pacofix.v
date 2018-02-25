Require Import FunctionalExtensionality.
Require Import Program.
Require Import paco.

Set Implicit Arguments.
Set Primitive Projections.

Require Import index wf IFunctor ISPFunctor icoinductive iso icombinator1.

Section PACO.

  Variable O : Type.
  Variable F : O -> (O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.

  Definition pa_Nu (R : O -> Type) : O -> Type :=
    Nu (fun o => Comp (fun o1 => Coprod (Ident o1) (Const (R o1))) (F o)).

  Notation "A \+/ B" := (fun o => sum (A o) (B o)) (at level 50, left associativity)
                        : ssp_scope. 

  Open Scope ssp_scope.

  Definition pacodown (A B : O -> Type) (FIX : forall o, A o -> pa_Nu (A \+/ B) o) :
    forall o, pa_Nu (A \+/ B) o -> pa_Nu B o :=
    corec (fun o => Comp (fun o1 => Coprod (Ident o1) (Const (B o1))) (F o)) (pa_Nu (A \+/ B))
          (fun o fx => map (fun i x =>
                              match x with
                              | inl n => inl n
                              | inr (inl a) => inl (FIX i a)
                              | inr (inr b) => inr b
                              end) (cDes fx)).

  Definition pacorec (A B : O -> Type) (FIX : forall o, A o -> pa_Nu (A \+/ B) o) :
    forall o, A o -> pa_Nu B o :=
    fun o (a : A o) => pacodown A B FIX (FIX o a).

  Definition just (R : O -> Type) : forall o, Nu F o -> pa_Nu R o :=
     corec (fun o => Comp (fun o1 => Coprod (Ident o1) (Const (R o1))) (F o)) (Nu F)
           (fun o (n : Nu F o) => map (fun _ => inl) (cDes n)).

  Definition erase_false : forall o, pa_Nu (fun _ => False) o -> Nu F o :=
    corec F (pa_Nu (fun _ => False))
          (fun o fx => map (fun i x => match x with
                                       | inl n => n
                                       | inr f => False_rect _ f
                                       end) (cDes fx)).

  Goal True. apply I. Qed.

  Lemma just_section :
    forall o (fx : Nu F o), erase_false (just (fun _ => False) fx) = fx.
  Proof.  
    apply cofun_eq_unique with (FIX := @cDes _ _ _).
    - intros. unfold erase_false, just. repeat rewrite corec_red. simpl.
      repeat rewrite MAP_COMPOSE. reflexivity.
    - intros. symmetry. apply MAP_ID.
  Qed.

  Lemma erase_section :
    forall o (fx : pa_Nu (fun _ => False) o), just _ (erase_false fx) = fx. 
  Proof.
    apply cofun_eq_unique with (FIX := @cDes _ _ _).
    - intros. unfold erase_false, just. repeat rewrite corec_red. simpl.
      repeat rewrite MAP_COMPOSE. f_equal.
      extensionality i. extensionality x. destruct x as [x | []]. reflexivity.
    - intros. symmetry. apply MAP_ID.
  Qed.

  Definition pacoup A B : forall o, pa_Nu B o -> pa_Nu (A \+/ B) o := 
    corec (fun o => Comp (fun o1 => Coprod (Ident o1) (Const (A o1 + B o1))) (F o)) (pa_Nu B)
          (fun o fx => map (fun i x => match x with
                                       | inl n => inl n
                                       | inr b => inr (inr b)
                                       end) (cDes fx)).

  Lemma up_section A B (FIX : forall o, A o -> pa_Nu (A \+/ B) o) :
    forall o (fx : pa_Nu B o), pacodown A B FIX (pacoup A fx) = fx.
  Proof.
    apply cofun_eq_unique with (FIX := @cDes _ _ _).
    - intros. unfold pacodown, pacoup. repeat rewrite corec_red. simpl.
      repeat rewrite MAP_COMPOSE. f_equal.
      extensionality i. extensionality x. destruct x; reflexivity.
    - intros. symmetry. apply MAP_ID.
  Qed.

  Lemma pacodown_red A B (FIX : forall o, A o -> pa_Nu (A \+/ B) o) o
        (fx : pa_Nu (A \+/ B) o) :
    cDes (pacodown A B FIX fx) =
    map (fun i (x : pa_Nu (A \+/ B) i + (A i + B i)) =>
           match x with
           | inl n => inl (pacodown A B FIX n)
           | inr (inl a) => inl (pacorec A B FIX i a)
           | inr (inr b) => inr b
           end) (cDes fx).
  Proof.
    unfold pacodown, pacorec at 1. rewrite corec_red. simpl.
    rewrite MAP_COMPOSE. simpl.
    f_equal. extensionality i. extensionality x.
    destruct x as [x | [ax | bx]]; reflexivity.
  Qed.

  Lemma pacorec_red A B (FIX : forall o, A o -> pa_Nu (A \+/ B) o) o (a : A o) :
    cDes (pacorec A B FIX o a) = 
    map (fun i (x : pa_Nu (A \+/ B) i + (A i + B i)) =>
           match x with
           | inl n => inl (pacodown A B FIX n)
           | inr (inl a) => inl (pacorec A B FIX i a)
           | inr (inr b) => inr b
           end) (cDes (FIX o a)).
  Proof.
    unfold pacorec at 1. apply pacodown_red.
  Qed.

End PACO.
