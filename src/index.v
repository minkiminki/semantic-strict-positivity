Set Implicit Arguments.

(* Tactics.  FIXME: move it! *)

Ltac inv H := inversion H; subst; clear H.
Ltac simplify := repeat (autounfold in *; unfold id in *; simpl in *).

(* Categories *)

Definition iType C := C -> Type.

Inductive sigI {C} {A : iType C} (P : forall i, A i -> Prop) : iType C :=
| existI i (x : A i) : P i x -> sigI P i.
Arguments existI {C} {A} {P} {i} x p.

Inductive sigTI {C} {A : iType C} (P : forall i, A i -> Type) : iType C :=
| existTI i (x : A i) : P i x -> sigTI P i.
Arguments existTI {C} {A} {P} {i} x p.

Definition projI1 {C} {A : iType C} (P : forall i, A i -> Prop) i
           (x : sigI P i) : A i :=
  match x with
  | existI x p => x
  end.

Definition projI2 {C} {A : iType C} (P : forall i, A i -> Prop) i
           (x : sigI P i) : P i (projI1 x) :=
  match x with
  | existI x p => p
  end.

Definition projTI1 {C} {A : iType C} (P : forall i, A i -> Type) i
           (x : sigTI P i) : A i :=
  match x with
  | existTI x p => x
  end.

Definition projTI2 {C} {A : iType C} (P : forall i, A i -> Type) i
           (x : sigTI P i) : P i (projTI1 x) :=
  match x with
  | existTI x p => p
  end.

Definition sigImply {C} {A : iType C} (P Q : forall i, A i -> Prop)
           (H : forall i x, P i x -> Q i x) i (x : sigI P i) : sigI Q i :=
  match x with
  | existI x p => existI x (H _ _ p)
  end.

Definition sigTImply {C} {A : iType C} (P Q : forall i, A i -> Type)
           (H : forall i x, P i x -> Q i x) i (x : sigTI P i) : sigTI Q i :=
  match x with
  | existTI x p => existTI x (H _ _ p)
  end.

Definition sigImply_proj1 {C} {A : iType C} (P Q : forall i, A i -> Prop)
           (H : forall i x, P i x -> Q i x) i (x : sigI P i) :
  projI1 x = projI1 (sigImply _ H x).
Proof.
  destruct x. reflexivity.
Qed.

Definition sigImply_proj2 {C} {A : iType C} (P Q : forall i, A i -> Prop)
           (H : forall i x, P i x -> Q i x) i (x : sigI P i) :
  projI2 (sigImply _ H x) = projI2 (sigImply _ H x).
Proof.
  destruct x. reflexivity.
Qed.

Definition sigTImply_proj1 {C} {A : iType C} (P Q : forall i, A i -> Type)
           (H : forall i x, P i x -> Q i x) i (x : sigTI P i) :
  projTI1 x = projTI1 (sigTImply _ H x).
Proof.
  destruct x. reflexivity.
Qed.

Definition sigTImply_proj2 {C} {A : iType C} (P Q : forall i, A i -> Type)
           (H : forall i x, P i x -> Q i x) i (x : sigTI P i) :
  projTI2 (sigTImply _ H x) = projTI2 (sigTImply _ H x).
Proof.
  destruct x. reflexivity.
Qed.