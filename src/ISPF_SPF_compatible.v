Set Implicit Arguments.
Require Import Program.

Require Import Functor pullback_sfunctor SPFunctor IFunctor ISPFunctor.

Section INDEXING.

  Definition indexing_functor F `{Functor.Functor F} :
    IFunctor.Functor (fun (T : unit -> Type) => F (T ())) :=
    {|
      map X Y f := Functor.map (f tt);
    |}.

  Arguments indexing_functor F {_}.

  Definition indexing_sfunctor F `{Functor.SFunctor F} :
    IFunctor.SFunctor (fun (T : unit -> Type) => F (T ())) :=
    Build_SFunctor (indexing_functor F)
                   (fun X fx => unit_rect _ (Functor.mem fx))
                   (fun X Y R => Functor.rel (R tt))
                   (fun X fx =>
                      Functor.map
                        (fun x => @index.existI _ _
                                                (unit_rect (fun u => X u -> Prop) 
                                                           (Functor.mem fx))
                                                _ (` x) (proj2_sig x))
                        (Functor.tag (X ()) fx)).

  Arguments indexing_sfunctor F {_}.

  Program Definition indexing_spfunctor F `{SPFunctor.SPFunctor F} :
    ISPFunctor.SPFunctor (fun (T : unit -> Type) => F (T ())) :=
    @Build_SPFunctor 
      _ _ (indexing_sfunctor F)
      (@SPFunctor.shape F _) (fun s _ => @SPFunctor.degree F _ s)
      (Build_NatIso
         (Build_NatTr _ _ (fun X fx
                           => index.sigTimply _
                                              (fun s => unit_rect (fun u => SPFunctor.degree s -> X u))
                                              (Functor.NT (X ()) fx)) _ _ _)                                
         (fun X fx => Functor.NTinv _
                                    (index.sigTimply _
      (fun s (f : forall i, SPFunctor.degree s -> X i) => f tt) fx)) _ _) _.
  Next Obligation.
    rewrite (Functor.MAP_COMMUTE (f tt) fx).
    unfold index.sigTimply. simpl. f_equal.
    extensionality u. destruct u. reflexivity.
  Qed.
  Next Obligation.
    destruct i. simpl. rewrite Functor.MEM_COMMUTE.
    simpl. reflexivity.
  Qed.
  Next Obligation.
    rewrite Functor.REL_COMMUTE. simpl.
    split; intro REL.
    - destruct REL. unfold index.sigTimply. simpl. constructor.
      intros []. apply H0.
    - destruct (Functor.NT _ fx), (Functor.NT _ fy).
      unfold index.sigTimply in REL.
      apply CONTAINER_REL2 in REL. simpl in *. destruct REL.
      destruct x2. simpl in *. constructor. apply H0.
  Qed.
  Next Obligation.
    rewrite <- Functor.BIJECTION1. f_equal.
    unfold index.sigTimply. simpl.
    symmetry. apply sigT_eta.
  Qed.
  Next Obligation.
    rewrite Functor.BIJECTION2. unfold index.sigTimply. simpl.
    rewrite sigT_eta. f_equal.
    extensionality u. destruct u. reflexivity.
  Qed.
  Next Obligation.
    rewrite pullback_sfunctor.MAP_COMPOSE.
    apply SPFunctor.TAG.
  Qed.
  
End INDEXING.

Section UNINDEXING.

  Definition unindexing_functor (F : (unit -> Type) -> Type) `{Functor _ F} :
    Functor.Functor (fun X => F (fun _ => X)) :=
    {|
      Functor.map X Y f := map (fun _ => f);
    |}.

  Arguments unindexing_functor F {_}.

  Program Definition unindexing_sfunctor (F : (unit -> Type) -> Type) `{SFunctor _ F} :
    Functor.SFunctor (fun X => F (fun _ => X)) :=
    Functor.Build_SFunctor (unindexing_functor F)
                           (fun X fx => mem fx (i:=tt))
                           (fun X Y R => rel (fun _ => R))
                           (fun X fx =>
                              map (unit_rect
                                     (fun u => index.sigI (@mem () F H (fun _ => X) fx) u -> {x | mem fx x})
                                     (fun x => exist _ (index.projI1 x) (index.projI2 x))) (tag _ fx)).
  Arguments unindexing_sfunctor F {_}.

  Program Definition unindexing_spfunctor (F : (unit -> Type) -> Type)
          `{SPFunctor _ F} :
    SPFunctor.SPFunctor (fun X => F (fun _ => X)) :=
    @SPFunctor.Build_SPFunctor 
      _ (unindexing_sfunctor F) (@shape _ F _) (fun s => @degree _ F _ s tt)
      (@Functor.Build_NatIso _ _ _ _
                             (@Functor.Build_NatTr _ _ _ _  (fun X fx =>
 existT _ _
   (projT2 (NT _ fx : Container degree (fun _ => X)) tt))
                                                   _ _ _)
                             (fun X fx => NTinv _ (existT _ _
                                              (unit_rect _ (projT2 fx)))) _ _
      ) _.
  Next Obligation.
    rewrite MAP_COMMUTE. reflexivity.
  Qed.
  Next Obligation.
    rewrite MEM_COMMUTE. apply iff_refl.
  Qed.
  Next Obligation.
    rewrite REL_COMMUTE. simpl. split; intro REL.
    - destruct REL. simpl. constructor. apply H0.
    - destruct (NT _ fx) as [s1 f1], (NT _ fy) as [s2 f2].
      rewrite SPFunctor.CONTAINER_REL2 in REL. simpl in *.
      destruct REL as [e REL]. destruct e.
      constructor. intros []. apply REL.
  Qed.
  Next Obligation.
    pattern fx at 4. rewrite <- (BIJECTION1 _ fx).
    f_equal. rewrite sigT_eta. f_equal.
    extensionality u. destruct u. reflexivity.
  Qed.
  Next Obligation.
    rewrite BIJECTION2. simpl. symmetry. apply sigT_eta.
  Qed.
  Next Obligation.
    rewrite MAP_COMPOSE. pattern fx at 11. rewrite <- (TAG _ fx).
    f_equal. extensionality u. destruct u. reflexivity.
  Qed.

End UNINDEXING.