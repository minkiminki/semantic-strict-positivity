Require Import FunctionalExtensionality.
Require Import Program.
Require Import JMeq.

Set Implicit Arguments.

Require Import index wf IFunctor ISPFunctor iinductive hott.

Arguments map {C} F {Functor X Y} f x.

Section BISPF.

  Class BISPFunctor C1 C2 (F : iType C1 -> iType C2 -> Type) : Type :=
    {
      SPF1 :> forall X, SPFunctor (F X);
      SPF2 :> forall Y, SPFunctor (fun X => F X Y);
      BIMAP_COMMUTE : forall X1 X2 Y1 Y2 (f : forall i, X1 i -> X2 i)
                             (g : forall i, Y1 i -> Y2 i) (fx : F X1 Y1),
          map (fun X => F X Y2) f (map (F X1) g fx) = map (F X2) g (map (fun X => F X Y1) f fx);
    }.

  Definition bimap C1 C2 (F : iType C1 -> iType C2 -> Type) `{BISPFunctor _ _ F} :
    forall X1 X2 Y1 Y2, (forall i, X1 i -> X2 i) -> (forall i, Y1 i -> Y2 i) -> F X1 Y1 -> F X2 Y2 :=
    fun X1 X2 Y1 Y2 f g fx => map (fun X => F X Y2) f (map (F X1) g fx).

End BISPF.