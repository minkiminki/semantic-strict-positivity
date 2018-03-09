Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor iinductive hott iso icombinator1
        icoinductive.

Section MU.

  Variable A B : Type.
  Variable (F : B -> (A + B -> Type)-> Type).

  Context `{SPF : forall b, SPFunctor (F b)}.

  Definition mu b (X : A -> Type) : Type := Mu (fun b => Subst (F b) X) b.
  
  Definition mu_map X Y (f : forall a, X a -> Y a) : forall b, mu b X -> mu b Y :=
    prim_rec (F:=fun b : B => Subst (F b) X) (fun o => mu o Y)
             (fun b (fx : Subst (F b) X (fun o : B => mu o Y)) =>
                Con (fun b0 : B => Subst (F b0) Y) b
                    (map
                       (fun i : A + B =>
                          match
                            i as s
                            return
                            (match s with
                             | inl c0 => fun _ : B -> Type => X c0
                             | inr c => fun X0 : B -> Type => X0 c
                             end (fun o : B => mu o Y) ->
                             match s with
                             | inl c0 => fun _ : B -> Type => Y c0
                             | inr c => fun X0 : B -> Type => X0 c
                             end
                               (Mu
                                  (fun (b0 : B) (X0 : B -> Type) =>
                                     F b0
                                       (fun i0 : A + B =>
                                          match i0 with
                                          | inl c0 => fun _ : B -> Type => Y c0
                                          | inr c => fun X1 : B -> Type => X1 c
                                          end X0))))
                          with
                          | inl a => f a
                          | inr b0 => id
                          end) fx)).

  Definition mu_mem X : forall b, mu b X -> forall a, X a -> Prop.
    apply (@simple_rec _ _ _ (forall a : A, X a -> Prop)).
    intros b fx.
    unfold Subst, Comp, Const, Ident in fx. simpl in *.

    intros a x. apply or.
    - apply (@mem _ _ _ _ fx (inl a) x).
    - apply (@ex B). intro b'.
      apply (@ex (forall a : A, X a -> Prop)). intro MEM. apply and.
      + apply (@mem _ _ _ _ fx (inr b') MEM).
      + apply (MEM a x).
  Defined.

  Definition mu_rel X Y (R : forall a, X a -> Y a -> Prop) :
    forall b, mu b X -> mu b Y -> Prop.
    apply (prim_rec (fun b => mu b Y -> Prop)).
    intros b fx my. 
    unfold Subst, Comp, Const, Ident in *. simpl in *.
    eapply (rel _ fx (Des my)). Unshelve.

    intro i. destruct i.
    - apply (R a).
    - intros r m. apply (r m).
  Defined.

  Definition mu_tag X : forall b, forall (m : mu b X), mu b (sigI (mu_mem m)).
  Proof.
    apply rec.
    intros o1 m1 FIX. apply Con.

    set (Des m1). unfold Subst, Comp, Const, Ident in s.
    set (tag _ s).

    eapply (map _ f). Unshelve. simpl. unfold s. clear s f.

    intro i. destruct i.
    - unfold Subst, Comp, Const, Ident. 

      intro fx. destruct fx as [[fa | fb] p].
      + rewrite <- (eta_expand2 m1). unfold mu_mem.
        rewrite simple_rec_red. giveup.
      + giveup.
    - giveup.
  Qed.

  Global Instance mu_SPFunctor b : SPFunctor (mu b).
    giveup.
  Qed.

End MU.

Section NU.

  Variable A B : Type.
  Variable (F : B -> (A + B -> Type)-> Type).

  Context `{SPF : forall b, SPFunctor (F b)}.

  Definition nu b (X : A -> Type) : Type := Nu (fun b => Subst (F b) X) b.
  
  Global Instance nu_SPFunctor b : SPFunctor (nu b).
    giveup.
  Qed.

End NU.
