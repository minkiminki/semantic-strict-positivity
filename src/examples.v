Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor iinductive hott iso icombinator1
        icoinductive icombinator pacofix paco.

Section HLIST.

  Definition Hlist_gen (l : list Type) : (list Type -> Type) -> Type :=
    match l with
    | nil => Const unit
    | cons hd tl => Prod (Const hd) (Ident tl)
    end.

  Instance Hlist_gen_SPF l : SPFunctor (Hlist_gen l).
  Proof.
    destruct l.
    - apply Const_SPF.
    - apply Prod_SPF.
      + apply Const_SPF.
      + apply Ident_SPF.
  Defined.

  Definition Hlist : list Type -> Type := Mu Hlist_gen.

  Definition Hnil : Hlist nil := Con Hlist_gen nil tt.

  Definition Hcons (hdT : Type) (tlT : list Type) (hd : hdT) (tl : Hlist tlT) :
    Hlist (cons hdT tlT) :=
    Con Hlist_gen (cons hdT tlT) (hd, tl).

  (* recursor *)

End HLIST.

Section VECTOR.

  Definition vector_gen : nat -> (unit + nat -> Type) -> Type :=
    fun n : nat =>
      match n with
      | 0 => Const unit
      | Datatypes.S n' => Prod (Ident (inl tt)) (Ident (inr n'))
      end.

  Instance vector_gen_SPF n : SPFunctor (vector_gen n).
  Proof.
    destruct n.
    - apply Const_SPF.
    - apply Prod_SPF.
      + apply Ident_SPF.
      + apply Ident_SPF.
  Defined.

  Definition vector X : nat -> Type :=
    fun n => mu vector_gen n (fun _ => X).

  Definition vnil X : vector X 0 := Con _ 0 tt.

  Definition vcons X n : X -> vector X n -> vector X (Datatypes.S n) :=
    fun x v => Con _ (S n) (x, v).

  Definition app X n2 (ls2 : vector X n2) : forall n, vector X n -> vector X (n + n2) :=
    rec_simpl1 _
               (fun n =>
                  match n as n0
                        return (forall v0 : vector X n0,
                                   (forall o2 m2, ord_c m2 v0 -> vector X (o2 + n2))
                                   -> vector X (n0 + n2))
                  with
                  | 0 => fun _ _ => ls2
                  | S n0 =>
                    fun (v0 : vector X (S n0)) app =>
                      match Des_ord v0 return (vector X (S n0 + n2)) with
                      | (x, i) =>
                        match i with
                        | @existI _ _ _ n0 v' o =>
                          Con _ (S n0 + n2) (x, app _ v' o)
                        end
                      end
                  end).

End VECTOR.

Section STREAM.

  Definition stream_gen X : unit -> (unit -> Type) -> Type :=
    fun u => match u with
             | _ => Prod (Const X) (Ident tt)
             end.

  Instance stream_gen_SPF X : SPFunctor (stream_gen X tt).
  Proof.
    apply Prod_SPF.
    - apply Const_SPF.
    - apply Ident_SPF.
  Defined.

  Definition stream X := Nu (stream_gen X) tt.

  Definition inf_stream (n : nat) : stream nat :=
    pacorec_bot (fun u1 u2 => match u1, u2 with
                              | tt, tt => cCon _ tt (n, inr tt)        
                              end) tt tt.

  Definition inf_stream2 (n : nat) : stream nat :=
    corec (stream_gen nat) (fun _ => unit)
          (fun u1 =>
             match u1 as u return (unit -> stream_gen nat u (fun _ => unit)) with
             | tt => fun _ => (n, tt)
             end) tt tt.
 
  Definition stream_map X Y (f: X -> Y) : stream X -> stream Y :=
    pacorec_bot (fun u (v : Nu (stream_gen X) u) =>
                   cCon _ u (let s := cDes v in (f (fst (cDes v)), inr (snd (cDes v))))) tt.

  Definition stream_map2 X Y (f: X -> Y) : stream X -> stream Y :=
    corec (stream_gen Y) (Nu (stream_gen X))
          (fun u  => match u with
                     | tt => fun v => (f (fst (cDes v)), snd (cDes v))
                     end) tt.

  Lemma inf_stream_correct2 (n : nat) : cDes (inf_stream n) = (n, inf_stream n).
  Proof.
    unfold inf_stream at 1. rewrite pacorec_bot_red. rewrite c_eta_expand1.
    reflexivity.
  Qed.

  Lemma inf_stream_correct (n : nat) : cDes (inf_stream n) = (n, inf_stream n).
  Proof.
    reflexivity.
  Defined.

  Definition enumeration' : nat -> stream nat :=
    pacorec_bot (fun (u : unit) (m : nat) => cCon _ u (m, inr (S m))) tt.

  Definition enumeration'2 : nat -> stream nat :=
    corec (stream_gen nat) (fun _ => nat) (fun u => match u with
                                                    | tt => fun n => (n, S n)
                                                    end) tt.

  Definition enumeration : stream nat := enumeration' 0.

  Lemma enumeration_correct : forall n, bsm (enumeration'2 n)
                                  (cCon _ tt (n, stream_map2 S (enumeration'2 n))).
  Proof.
    set (R := fun u => match u as u0 return (Nu (stream_gen nat) u0 -> Nu (stream_gen nat) u0 -> Prop) with
                       | tt => fun x y => exists n,
                                   (enumeration'2 n = x) /\
                                   (cCon (stream_gen nat) tt (n, stream_map2 S (enumeration'2 n)) = y) end).
    assert (forall o n1 n2, R o n1 n2 -> bsm n1 n2).    
    - apply bsm_prim. intro u. destruct u. intros n1 n2 REL.
      unfold R in REL. destruct REL as [n [[] []]].
      rewrite c_eta_expand1. unfold enumeration'2 at 1. rewrite corec_red.
      simpl. split; auto.
      exists (S n). split.
      + reflexivity.
      + apply cDes_injective. unfold stream_map2 at 2.
        rewrite c_eta_expand1. rewrite corec_red.        
        Opaque cDes. unfold enumeration'2 at 2 3.
        repeat rewrite corec_red. reflexivity.
    - intro n. apply H. exists n; auto.
  Qed.

End STREAM.