Require Import Program.
Set Implicit Arguments.
Require Import spec Functor SPFunctor inductive coinductive combinator paco tactics.

Section MENDLER.
  
  Variable PF : Type -> Type.
  Context `{SPF : SPFunctor PF}.

  Definition pafcofix (A : Type) := fcofix (PF ∘ (Coprod Ident (Const A))).
 
  Definition just A : fcofix PF -> pafcofix A.
    apply fcorec_p.
    intro x.
    apply fcofix_des in x.
    unfold compose.
    apply (map inl x).
  Defined.    

  Definition pacor' A B (f : (A -> pafcofix (A + B))) : (pafcofix (A + B) -> pafcofix B).
    apply fcorec_p.
    intro x.
    apply fcofix_des in x.
    apply (map (fun y =>
               match y with
               | inl y' => inl y'
               | inr (inl a) => inl (f a)
               | inr (inr b) => inr b end               
               ) x).
  Defined.

  Definition pacor (A B : Type) : (A -> pafcofix (A + B)) -> (A -> pafcofix B).
    intros f a.
    apply (pacor' f (f a)).
  Defined.

  Definition erase_false' A : (A + False) -> A. 
    intro x.
    destruct x.
    - apply a.
    - destruct f.
  Defined.

  Definition erase_false : pafcofix False -> fcofix PF.
    apply fcorec_p.
    intro x.
    apply fcofix_des in x. 
    unfold compose in *.
    eapply (map _ x).
    Unshelve.
    intro. destruct x1.
    - apply i.
    - destruct c.
  Defined.

  Definition paffix (A : Type) := ffix (PF ∘ (Prod Ident (Const A))).
 
  Definition value A : paffix A -> ffix PF.
    apply frec_p.
    intro x.
    apply Ffix.
    unfold compose in x.
    apply (map fst x).
  Defined.    

  Definition par' A B (f : paffix (A*B) -> A) : paffix B -> paffix (A*B).
    apply frec_p.
    intro x.
    apply Ffix.
    apply (map (fun y =>
               match y with
               | (y', b) => (y', (f y', b))              
               end) x).
  Defined.

  Definition par (A B : Type) : (paffix (A*B) -> A)-> (paffix B -> A).
    intros f x.
    apply (f (par' f x)).
  Defined.

  Definition erase_true : ffix PF -> paffix unit.
    apply frec_p.
    intro x.
    apply Ffix. unfold compose.
    eapply (map _ x).
    Unshelve.
    intro.
    apply (x1, tt).
  Defined.

End MENDLER.

Arguments pafcofix PF {H} {H0} {SPF} A.
Arguments paffix PF {H} {H0} {SPF} A.

(*
CoInductive stream :=
| Cons : nat -> stream -> stream.

CoFixpoint map (f : nat -> nat) s :=
match s with
| Cons n s' => Cons (f n) (map f s') end.

CoInductive stream' :=
| Cons' : nat -> stream -> stream'.



Inductive stream' : nat -> Type :=
| Just : stream -> stream' 0
| Cons' n : stream' n -> stream' (S n)
.

CoFixpoint enumerate := Cons

Inductive stream := 

CoFixpoint enumerate := Cons 0 (map S enumerate).
*)

Section STREAM.

  Definition stream_gen := Prod (Const nat) Ident.

  Global Instance stream_gen_SPF : SPFunctor stream_gen.
  Proof.
    unfold stream_gen. apply prod_SPFunctor.
    apply const_SPFunctor. apply id_SPFunctor.
  Qed.  

  Definition stream := fcofix stream_gen.

  Definition stream_map A (f : nat -> nat) : pafcofix stream_gen A -> pafcofix stream_gen A.
    apply fcorec_p. intro x. apply fcofix_des in x.
    unfold compose, stream_gen, Prod, Const, Ident, Coprod in *.
    destruct x.
    apply (f n, s).
  Defined.

End STREAM.    
   
 