Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.Monads.PointedEndofunctors.

Local Open Scope Cat.
Local Open Scope cat.

Definition ω_graph : graph.
Proof. 
  use make_graph.
  - exact nat.
  - intros m n.
    (* only arrows m -> m + 1 *)
    exact (n = S m).
Defined.

(*
  Inspired by lecture notes by Egbert Rijke linked at
  https://ncatlab.org/nlab/show/sequential+limit, then
  just removed it when I saw what was already in UniMath *)

(* Definition increasing_cat_sequence (C : category) : UU :=
    ∑ (ob : nat -> C), ∏ (n : nat), ob n --> ob (n + 1). *)
(* this definition is the same as diagram ω_graph C. *)

Section ptd_endo_colim.

(* We will end up requiring that C is cocomplete anyway *)
Context {C : category}.
Context (CL : Colims C).
Context (T : pointed_endofunctor C).

Local Definition CLF := ColimsFunctorCategory C C CL.
Local Definition CE := Coequalizers_from_Colims _ CL.
Local Definition CEF := Coequalizers_from_Colims _ CLF.

Definition ptd_endo_coeq_sequence :
  nat -> arrow (functor_category C C).
Proof.
  intro n.
  induction n as [|β xβ].
  - (* initial arrow is I ⟹ T *)
    use tpair.
    * split.
      + exact (functor_identity _).
      + exact (ptd_endo_functor T).
    * exact (ptd_endo_unit T).
  - destruct xβ as [[Xβ Xβ1] xβ].
    simpl in xβ.

    set (TXβ := (ptd_endo_functor T) □ Xβ).
    
    set (Tt := pre_whisker T (ptd_endo_unit T)).
    set (tT := post_whisker (ptd_endo_unit T) T).
    (* admit. *)
    (* this is just for testing, we want to add the coequalizers here *)
    (* Looking at the nLab page 
       (https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras)  
       I think what we will want to do is instead define a function of diagrams
                      TXn
       n -->           |
                       v
              Xn ---> Xn+1
       then from the previous section, we should be able to create the
       coequalizer that we need (?)
    *)
    use tpair.
    * split.
      + exact (Xβ1).
      + exact (Xβ1).
    * exact (identity _).
    
    (* this is wrong: *)
    (* set (xn1 : functor_composite T tncod).

    set (coeq := CE (ptd_endo_functor T) (functor_composite T T) Tt tT).
    use tpair.
    * split.
      + exact tncod.
      + exact (CoequalizerObject coeq).
    * simpl.
      set (arr := CoequalizerArrow coeq).
      set (test := nat_trans_comp _ _ _ (ptd_endo_unit T) (CoequalizerArrow coeq)). 
      exact (nat_trans_comp (ptd_endo_unit T) (CoequalizerArrow coeq)). *)
Defined.

Definition ptd_endo_coeq_sequence_diagram :
    diagram ω_graph (functor_category C C).
Proof.
  set (seq := ptd_endo_coeq_sequence).
  use tpair.
  - intro n.
    exact (arrow_dom (seq n)).
  - simpl.
    intros m n H.
    rewrite H.
    exact (arrow_mor (seq m)).
Defined.

Definition ptd_endo_coeq_sequence_colim : 
  ColimCocone ptd_endo_coeq_sequence_diagram :=
    CLF _ ptd_endo_coeq_sequence_diagram.

End ptd_endo_colim.
