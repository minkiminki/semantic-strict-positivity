Require Import FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor.

Section COINDUCTIVE.

  Variable I O : Type.
  Variable F : O -> (I + O -> Type) -> Type.

  Context `{H : forall c, SPFunctor (F c)}.
  Variable X : (iType I).

  Definition X_ (T : O -> Type) : I + O -> Type :=
    fun io : I + O => match io with
                      | inl i => X i
                      | inr o1 => T o1
                      end.

  Goal True. Proof. constructor. Qed.

  Definition X_fun (T1 T2 : O -> Type) (f : forall o, T1 o -> T2 o) io :
    X_ T1 io -> X_ T2 io :=
    match io as io' return (X_ T1 io' -> X_ T2 io') with
    | inl i => (fun x' => x')
    | inr o => (fun x' => f o x')
    end.

  CoInductive Nu : O -> Type :=
  | Con' o : sigT (fun (s : S) =>
                    ((forall (i : I), (@P _ _ (H o) s (inl i)) -> X i) *
                     (forall (o1 : O), (@P _ _ (H o) s (inr o1)) -> Nu o1))%type)
            -> Nu o.

  (* I wanna define Mu as below *)
  Fail Inductive Nu' : O -> Type :=
  | Con'' o : sigT (fun (s : S) =>
                     (forall (io : I + O), (@P _ _ (H o) s io) -> 
                                           match io with
                                           | inl i => X i
                                           | inr o1 => Nu' o1
                                           end)) ->Nu' o.
   (* but this definition can't pass the coq's strict positivity checker *)

  Definition c_Con o (fx : F o (X_ Nu)) : Nu o :=
    match (NT _ fx) with
    | existT _ s f => Con' o (existT _ s
                                     ((fun i (p : P s (inl i)) => f (inl i) p),
                                      (fun o1 (p : P s (inr o1)) => f (inr o1) p))) end.

  Definition c_Des o (n : Nu o) : F o (X_ Nu) :=
    match n with
    | Con' _ (existT _ s (f1, f2)) =>
      NTinv _
            (existT (fun s' => forall i, P s' i -> (X_ Nu) i) s
                    (fun (io : I + O) (p : P s io) =>
                       match io as io' return (P s io' -> (X_ Nu) io') with
                       | inl i => fun p' : P s (inl i) => f1 i p'
                       | inr o1 => fun p' : P s (inr o1) => f2 o1 p'
                       end p)) end.

  Goal True.
    auto.
  Qed.

  Lemma eta_expand2 : forall o (x : Nu o), c_Con (c_Des x) = x.
  Proof.
    intros. unfold c_Des, c_Con. destruct x as [o m].
    destruct m as [s [f1 f2]]. rewrite BIJECTION2.
    f_equal.
  Qed.

  Lemma eta_expand1 : forall o (x : F o (X_ Nu)), c_Des (c_Con x) = x.
  Proof.
    intros. unfold c_Des, c_Con.
    destruct (NT _ x) eqn : EQ.
    rewrite <- BIJECTION1. f_equal. rewrite EQ. f_equal.
    extensionality io. extensionality p.
    destruct io; reflexivity.
  Qed.
  (* if we define Mu as Mu', extensionality isn't necessary *)

  Definition corec (P : O -> Type)
             (FIX : forall o, P o -> F o (X_ P)) :
    forall o, P o -> Nu o.
  Admitted.

  Lemma corec_red (P : O -> Type)
             (FIX : forall o, P o -> F o (X_ P)) :
    forall o (x : P o),
      c_Des (corec FIX _ x) = map (X_fun _ _ (corec FIX)) (FIX o x).
  Admitted.

End COINDUCTIVE.