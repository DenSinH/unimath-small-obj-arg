(* Can be found on nlab:
    https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras
Or in G. M. Kelly. A unified treatment of transfinite constructions for free algebras, free
monoids, colimits, associated sheaves
*)

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

Local Notation "F □ G" := (functor_composite F G) (at level 35).

(* the horizontal map can be constructed from the vertical map:
              TXβ
                |
                | xβ
                v
  Xβ --------> Xβ1
     τXβ · xβ
*)
Local Definition pair_diagram : UU :=
    ∑ (x0 x1 : (functor_category C C)), ([C, C]⟦ T □ x0, x1 ⟧).

Local Definition pair_diagram_lob (X : pair_diagram) : functor_category C C :=
    pr1 X.
Local Definition pair_diagram_rob (X : pair_diagram) : functor_category C C :=
    pr12 X.
Coercion pair_diagram_arr (X : pair_diagram) :=
    pr22 X.

Local Definition pair_diagram_horizontal_arrow (X : pair_diagram) : (pair_diagram_lob X) --> (pair_diagram_rob X).
Proof.
  destruct X as [Xβ [Xβ1 xβ]].
  cbn.
  set (τX := post_whisker (ptd_endo_unit T) Xβ : [C, C]⟦Xβ, T □ Xβ⟧).
  exact (τX · xβ).
Defined.

Definition ptd_endo_coeq_sequence :
    nat -> pair_diagram.
Proof.
  intro n.
  induction n as [|β xβ].
  - (* initial arrow is I ⟹ T *)
    exists (functor_identity _), (ptd_endo_functor T).
    exact (nat_trans_id _).
  - destruct xβ as [Xβ [Xβ1 xβ]].
    (* Part of the sequence that we are considering:
       TXβ-1 --> TXβ ----> TXβ1
         |        |         |
         |     xβ |         | xβ1
         v        v         v
        Xβ ----> Xβ1 ----> Xβ2
             fβ
    *)
    (* the next "left object" is Xβ1 *)
    exists Xβ1.

    set (TXβ := T □ Xβ).
    set (TXβ1 := T □ Xβ1).
    
    set (Tt := pre_whisker T (ptd_endo_unit T) :
                  [C, C]⟦_, (T □ T)⟧).
    set (TtXβ := post_whisker Tt Xβ : 
                  [C, C]⟦T □ Xβ, (T □ T) □ Xβ⟧).
    set (tT := post_whisker (ptd_endo_unit T) T : 
                  [C, C]⟦_, T □ T⟧).
    set (tTXβ := post_whisker tT Xβ : 
                  [C, C]⟦T □ Xβ, (T □ T) □ Xβ⟧).
    set (Txβ := pre_whisker T xβ : 
                  [C, C]⟦T □ (T □ Xβ), T □ Xβ1⟧).
    (* 
    We define xβ1: TXβ1 ---> Xβ2 by the coequalizer of the two
    composites
         tT        Txβ
    TXβ ===> T2 Xβ --> TXβ1
         Tt
    *)
    rewrite <- functor_assoc in Txβ.
    set (coeq := CEF _ _ (tTXβ · Txβ) (TtXβ · Txβ)).
    set (Xβ2 := CoequalizerObject _ coeq).
    exists Xβ2.
    
    set (xβ1 := CoequalizerArrow _ coeq).
    exact xβ1.
Defined.

Definition ptd_endo_coeq_sequence_diagram :
    diagram ω_graph (functor_category C C).
Proof.
  set (seq := ptd_endo_coeq_sequence).
  use tpair.
  - intro n.
    exact (pair_diagram_lob (seq n)).
  - simpl.
    intros m n H.
    rewrite H.
    exact (pair_diagram_horizontal_arrow (seq m)).
Defined.

Definition ptd_endo_coeq_sequence_colim : 
  ColimCocone ptd_endo_coeq_sequence_diagram :=
    CLF _ ptd_endo_coeq_sequence_diagram.

End ptd_endo_colim.
