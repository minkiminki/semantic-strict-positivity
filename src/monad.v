Require Import FunctionalExtensionality.
Require Import Program.
Require Import ClassicalDescription.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.
Set Automatic Coercions Import.

Require Import Functor SPFunctor combinator spec inductive.

Class Monad {F : Type -> Type} (Fn : FunctorData F) :=
  { 
    ret : NatTrans id_functorData Fn;
    mult : NatTrans (compose_functorData Fn Fn) Fn;
    monad_law_1 : forall X (x : F (F (F X))), 
        (mult X) (mult (F X) x) = (mult X) (@map _ Fn _ _ (mult X) x);
    monad_law_2 : forall X (x : F X),
        (mult X) (Fn.(map) (ret X) x) = x;
    monad_law_3 : forall X (x : F X), (mult X) (ret (F X) x) = x;
  }.

Section monad.

  Variable M : Type -> Type.
  Context `{Fn : SPFunctor M}.
  Context `{Monad M Fn}.

  Definition bind {X Y} (f: X -> M Y) (x: M X) :=
    mult Y (Fn.(map) f x).
  Hint Unfold bind.

  Lemma bind_law_1 X Y (f: X -> M Y) x : bind f (ret X x) = f x.
  Proof.
    intros. unfold bind. rewrite <- MAP_COMMUTE. apply monad_law_3.
  Qed.

  Lemma bind_law_2 X x : bind (ret X) x = x.
  Proof.
    apply monad_law_2.
  Qed.

  Lemma bind_law_3 X Y Z (f : X -> M Y) (g : Y -> M Z) x :
    (bind g) ((bind f) x) = bind (fun x0 => bind g (f x0)) x.
  Proof.
    unfold bind.
    rewrite <- MAP_COMMUTE. rewrite monad_law_1. simplify.
    repeat rewrite (@MAP_COMPOSE _ _ (@toFunctorProp _ Fn)). auto.     
  Qed.

  Lemma bind_lemma_1 X (x : M (M X)) : mult X x = bind id x.
  Proof.
    unfold bind.
    rewrite (@MAP_ID _ _ (@toFunctorProp _ Fn)). auto.
  Qed.

  Lemma bind_lemma_2 X Y (f: X -> Y) x :
    Fn.(map) f x = bind (fun y => ret _ (f y)) x.
  Proof.
    unfold bind. simplify.
    setoid_rewrite <- (@MAP_COMPOSE _ _ (@toFunctorProp _ Fn)).
    setoid_rewrite monad_law_2. rewrite (@MAP_ID _ _ (@toFunctorProp _ Fn)). auto.
  Qed.

  Variable X : Type.

  Definition F := Coprod (Const unit) (Prod (Const (M X)) M).

  Definition Mlist := ffix F.

  Definition Mnil := Ffix F (inl tt).
  Definition Mcons (hd : M X) (tl : M Mlist) := Ffix F (inr (hd, tl)).

  Lemma Mcons_inj h1 t1 h2 t2
        (EQ: Mcons h1 t1 = Mcons h2 t2):
    h1 = h2 /\ t1 = t2.
  Proof.
    unfold Mcons in *. apply Ffix_inj in EQ. inversion EQ. auto.
  Qed.

  Lemma Mcons_inj2 hd tl (EQ: Mcons hd tl = Mnil):
    False.
  Proof.
    unfold Mcons, Mnil in *. apply Ffix_inj in EQ. inversion EQ.
  Qed.

  Lemma Mlist_ind l (P: Mlist -> Prop)
        (BASE: P Mnil)
        (STEP: forall hd tl 
                      (IND: forall x, Fn.(mem) tl x -> P x), 
            P (Mcons hd tl)):
    P l.
  Proof.
    apply ffix_mem_induction. intros. destruct m.
    - unfold Mnil in BASE. destruct c. apply BASE.
    - destruct p. unfold Mcons in STEP. apply STEP.
      intros. apply IND. right. auto.
  Qed.

  Definition mfix T (tnil: T) (tcons: M X -> M T -> T) (l: Mlist) : T :=
    frec_p (fun m => 
              match m with
              | inl tt => tnil
              | inr (mx, mt) => tcons mx mt end) l.

  Lemma mfix_correct_cons T (tnil: T) (tcons: M X -> M T -> T) hd tl : 
    mfix tnil tcons (Mcons hd tl) = tcons hd (Fn.(map) (mfix tnil tcons) tl).
  Proof.
    unfold mfix, Mcons.
    msimpl. auto.
  Qed.

  Lemma mfix_correct_nil T (tnil: T) (tcons: M X -> M T -> T) :
    mfix tnil tcons Mnil = tnil.
  Proof.
    unfold mfix, Mnil.
    msimpl. auto.
  Qed.

  Definition app' (mys : M Mlist) : Mlist -> M Mlist.
    apply mfix. apply mys.
    intros xsh mv.
    apply ret.
    apply Mcons. apply xsh.
    apply mult. apply mv.
  Defined.

    (*
Definition app' M `{SMonad M} {X} (mys : M (Mlist M X))
 :=
  mfix mys (fun (xsh : M X) (mv : M (Mlist M X)) => ret (Mlist M X) (Mcons X xsh (mult _ mv))).
     *)

  Definition app (mxs mys : M Mlist) :=
    bind (app' mys) mxs.

  Lemma app'_bind (mys : M Mlist) hd tl :
    app' mys (Mcons hd tl) =
    ret Mlist (Mcons hd (bind (app' mys) tl)).
  Proof.
    unfold app'. apply mfix_correct_cons.
  Qed.

  Theorem app'_assoc : forall (mys mzs : M Mlist) xs,
      app (app' mys xs) mzs = app' (app mys mzs) xs.
  Proof.
    intros. apply (Mlist_ind xs).
    - unfold app'. repeat rewrite mfix_correct_nil. auto.
    - intros. unfold app. rewrite app'_bind. rewrite app'_bind.
      rewrite bind_law_1. rewrite app'_bind.
      f_equal. f_equal.
      rewrite bind_law_3.
      unfold bind. f_equal. 
      apply map_pointwise. apply IND. 
  Qed.

  Theorem app_assoc : forall (mys mzs mxs : M Mlist),
      app (app mxs mys) mzs = app mxs (app mys mzs).
  Proof.
    intros. unfold app.
    rewrite bind_law_3. f_equal.
    extensionality x. apply app'_assoc.
  Qed.

End monad.
