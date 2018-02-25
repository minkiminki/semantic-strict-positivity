Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor iinductive hott.

Section Mu.

  Variable A B : Type.
  Variable (F : (A -> Type) -> B -> (B -> Type)-> Type).

  Context `{SPF1 : forall b X, SPFunctor (F X b)}.
  Context `{SPF2 : forall b Y, SPFunctor (fun X => F X b Y)}.
