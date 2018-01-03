Require Import Program.
Set Implicit Arguments.

Require Import wf.

Class SPF {C} (F : (C -> Type) -> Type) :=
  {
    map X Y : (forall i, X i -> Y i) -> (F X) -> (F Y);
    mem {X} : (F X) -> forall {i}, X i -> Prop;
    rel X Y : (forall i, X i -> Y i -> Prop) -> (F X) -> (F Y) -> Prop;
    ff : False;
  }.

Definition Ident C (i : C) (X : C -> Type) := X i.
Instance Ident_SPF C (i : C) : SPF (Ident i). Admitted.

Definition Const C (D : Type) (X : C -> Type) := D.
Instance Const_SPF (C D : Type) : SPF (@Const C D). Admitted.

Definition Coprod C (F G : (C -> Type) -> Type) (X : C -> Type) := (F X + G X)%type.
Instance Coprod_SPF C (F G : (C -> Type) -> Type) `{SPF _ F} `{SPF _ G}
  : SPF (Coprod F G).
Admitted.

Definition Prod C (F G : (C -> Type) -> Type) (X : C -> Type) := (F X * G X)%type.
Instance Prod_SPF C (F G : (C -> Type) -> Type) `{SPF _ F} `{SPF _ G}
  : SPF (Prod F G). Admitted.

Definition Expn C D (F : (C -> Type) -> Type) (X : C -> Type) := (D -> F X).
Instance Expn_SPF C D (F : (C -> Type) -> Type) `{SPF _ F} : SPF (Expn D F). Admitted.

Definition Dep_sum C A (B : A -> (C -> Type) -> Type) (X : C -> Type) :=
  sigT (fun a => (B a) X).
Instance Dep_sum_SPF C A (B : A -> (C -> Type) -> Type)
        `{H : forall a, SPF (B a)} : SPF (Dep_sum B). Admitted.

Definition Dep_prod C A (B : A -> (C -> Type) -> Type) (X : C -> Type) :=
  forall (a : A), (B a) X.
Instance Dep_prod_SPF C A (B : A -> (C -> Type) -> Type)
        `{H : forall a, SPF (B a)} : SPF (Dep_prod B). Admitted.

Definition Comp C1 C2 (F : C2 -> (C1 -> Type) -> Type) (G : (C2 -> Type) -> Type)
           (X : C1 -> Type) := G (fun i => F i X).
Instance Comp_SPF C1 C2 (F : C2 -> (C1 -> Type) -> Type) (G : (C2 -> Type) -> Type)
        `{HF : forall c, SPF (F c)} `{HG : SPF _ G} : SPF (Comp F G). Admitted.

Definition Mu C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type) `{H : forall c, SPF (F c)} :
  (C2 -> (C1 -> Type) -> Type). Admitted.
Instance Mu_SPF C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type)
        `{H : forall c, SPF (F c)} : forall c, SPF (Mu F c). Admitted.

Definition Nu C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type) `{H : forall c, SPF (F c)} :
  (C2 -> (C1 -> Type) -> Type). Admitted.
Instance Nu_SPF C1 C2 (F : C2 -> (C1 + C2 -> Type) -> Type)
        `{H : forall c, SPF (F c)} : forall c, SPF (Nu F c). Admitted.

Section INDUCTIVE.

  Variable C1 C2 : Type.
  Variable F : C2 -> (C1 + C2 -> Type) -> Type.
  Context `{forall c, SPF (F c)}.
  Variable T : (C1 -> Type).
  
  Definition ffix c := Mu F c T.

  Definition T' : C1 + C2 -> Type := fun c => match c with
                                              | inl c1 => T c1
                                              | inr c2 => ffix c2
                                              end.

  Definition Cons c : F c T' -> ffix c. Admitted.

  Definition Des c : ffix c -> F c T'. Admitted.

  Lemma eta_expand1 : forall c (x : ffix c), Cons (Des x) = x. Admitted.

  Lemma eta_expand2 : forall c (x : F c T'), Des (Cons x) = x. Admitted.

  Definition ord : forall i, ffix i -> forall j, ffix j -> Prop. Admitted.

  Definition ord_c := iclos_transn1 ord.

  Lemma ord_correct : forall i (x : ffix i) j (y : F j T'),
      ord x (Cons y) <-> mem x y. Admitted.

  Lemma ord_wf : iwell_founded ord. Admitted.

  Lemma ord_c_wf : iwell_founded ord_c.
  Proof.
    apply wf_iclos_trans.
    apply ord_wf.
  Qed.

  Lemma ord_transitive i j k (x : ffix i) (y : ffix j) (z : ffix k) :
    ord_c x y -> ord_c y z -> ord_c x z.
  Proof.
    apply iclos_transn1_transitive.
  Qed.

  Definition T'' i (x : ffix i) : C1 + C2 -> Type := 
    fun c => match c with
             | inl c1 => T c1
             | inr c2 => @less_ones _ _ ord _ x  c2
             end.

  Definition Des_ord i (x : ffix i) : F i (T'' x). Admitted.

End INDUCTIVE.
