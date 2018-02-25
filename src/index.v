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
  existI (projI1 x) (H _ _ (projI2 x)).

Definition sigTImply {C} {A : iType C} (P Q : forall i, A i -> Type)
           (H : forall i x, P i x -> Q i x) i (x : sigTI P i) : sigTI Q i :=
  existTI (projTI1 x) (H _ _ (projTI2 x)).

Definition sigImply_proj1 {C} {A : iType C} (P Q : forall i, A i -> Prop)
           (H : forall i x, P i x -> Q i x) i (x : sigI P i) :
  projI1 x = projI1 (sigImply _ H x).
Proof.
  reflexivity.
Qed.

Definition sigImply_proj2 {C} {A : iType C} (P Q : forall i, A i -> Prop)
           (H : forall i x, P i x -> Q i x) i (x : sigI P i) :
  projI2 (sigImply _ H x) = projI2 (sigImply _ H x).
Proof.
  reflexivity.
Qed.

Definition sigTImply_proj1 {C} {A : iType C} (P Q : forall i, A i -> Type)
           (H : forall i x, P i x -> Q i x) i (x : sigTI P i) :
  projTI1 x = projTI1 (sigTImply _ H x).
Proof.
  reflexivity.
Qed.

Definition sigTImply_proj2 {C} {A : iType C} (P Q : forall i, A i -> Type)
           (H : forall i x, P i x -> Q i x) i (x : sigTI P i) :
  projTI2 (sigTImply _ H x) = projTI2 (sigTImply _ H x).
Proof.
  reflexivity.
Qed.

Definition sigTimply A (P Q : A -> Type)
           (H : forall a, P a -> Q a) (x : sigT P) : sigT Q :=
  existT _ _ (H _ (projT2 x)).

Definition sigTimply_proj1 A (P Q : A -> Type)
           (H : forall a, P a -> Q a) (x : sigT P) :
  projT1 x = projT1 (sigTimply _ H x).
Proof.
  reflexivity.
Qed.

Definition sigTimply_proj2 A (P Q : A -> Type)
           (H : forall a, P a -> Q a) (x : sigT P) :
  H _ (projT2 x) = projT2 (sigTimply _ H x).
Proof.
  reflexivity.
Qed.

Definition sig2I {C} (X Y : iType C) (R : forall i, X i -> Y i -> Prop) : iType C :=
  sigTI (fun i x => sig (fun y => R i x y)).

Definition exist2I {C} (X Y : iType C) (R : forall i, X i -> Y i -> Prop) :
  forall i (x : X i) (y : Y i), R i x y -> sig2I _ _ R i :=
  fun i x y r => existTI x (exist _ y r).

Definition proj2I1 {C} (X Y : iType C) (R : forall i, X i -> Y i -> Prop) :
  forall i, sig2I _ _ R i -> X i :=
  fun i => @projTI1 _ _ _ _.

Definition proj2I2 {C} (X Y : iType C) (R : forall i, X i -> Y i -> Prop) :
  forall i, sig2I _ _ R i -> Y i :=
  fun i x => proj1_sig (projTI2 x).

Definition proj2I3 {C} (X Y : iType C) (R : forall i, X i -> Y i -> Prop) :
  forall i (x : sig2I _ _ R i), R i (proj2I1 x) (proj2I2 x) :=
  fun i x => proj2_sig (projTI2 x).
