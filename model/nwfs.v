Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.

Local Open Scope cat.
Local Open Scope mor_disp.

(* This based on an "examples" file, not sure if we want to use
that or just roll our own.
The code in the examples file seems to no longer work... *)
(* UniMath/CategoryTheory/DisplayedCats/Examples.v *)
Section Arrow_Disp.

Context (C:category).

Definition arrow_base := category_binproduct C C.

Definition arrow_disp_ob_mor : disp_cat_ob_mor arrow_base.
Proof.
  use make_disp_cat_ob_mor.
  (* objects are morphisms in original category *)
  - exact (λ xy, pr1 xy --> pr2 xy).
  - (* for every two objects in the base category, and morphism between them,
       a morphism in the displayed category *)
    simpl; intros xx' yy' g h ff'.
    exact (pr1 ff' · h = g · pr2 ff').
Defined.

Definition arrow_id_comp : disp_cat_id_comp _ arrow_disp_ob_mor.
Proof.
  split.
  - (* identity in base category maps to identity in displayed category *)
    simpl; intros.
    etrans. apply id_left. apply pathsinv0, id_right.
  - (* composition in base category maps to composition in displayed category *)
    simpl; intros x y z f g xx yy zz ff gg.
    etrans. apply @pathsinv0, assoc.
    etrans. apply maponpaths, gg.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition, ff.
    apply pathsinv0, assoc.
Qed.

Definition arrow_data : disp_cat_data _
  := (arrow_disp_ob_mor ,, arrow_id_comp).

Lemma arrow_axioms : disp_cat_axioms _ arrow_data.
Proof.
  (* left / right identity / associativity / homsets *)
  repeat apply tpair; intros; try apply homset_property.
  apply isasetaprop, homset_property.
Qed.

Definition arrow_disp : disp_cat _
  := (arrow_data ,, arrow_axioms).

  
Definition arrow : category := total_category arrow_disp.

End Arrow_Disp.

Section Three_disp.

Context (C:category).

Definition three_base := (category_binproduct C (category_binproduct C C)).

(* Can't do it over the arrow category, since this is a displayed category, not 
an actual category *)
Definition three_disp_ob_mor : disp_cat_ob_mor three_base.
Proof.
  use make_disp_cat_ob_mor.
  - exact (λ xyz, pr1 xyz --> pr12 xyz × pr12 xyz --> pr22 xyz).
  - (* double commutative square *)
    simpl; intros xxx yyy gg hh fff.
    exact ((pr1 fff · pr1 hh = pr1 gg · pr12 fff) × (pr12 fff · pr2 hh = pr2 gg · pr22 fff)).
Defined.

Definition three_id_comp : disp_cat_id_comp _ three_disp_ob_mor.
Proof.
  split.
  - (* identity in base category maps to identity in displayed category *)
    simpl; intros.
    split; eapply pathscomp0.
    * apply id_left.
    * apply pathsinv0, id_right.
    * apply id_left.
    * apply pathsinv0, id_right.
  - (* composition in base category maps to composition in displayed category *)
    simpl; intros x y z ff gg xxx yyy zzz fff ggg.
    split; eapply pathscomp0.
    * apply @pathsinv0, assoc.
    * eapply pathscomp0. apply maponpaths, ggg.
      eapply pathscomp0. apply assoc.
      eapply pathscomp0. apply cancel_postcomposition, fff.
      apply pathsinv0, assoc.
    * apply @pathsinv0, assoc.
    * eapply pathscomp0. apply maponpaths, ggg.
      eapply pathscomp0. apply assoc.
      eapply pathscomp0. apply cancel_postcomposition, fff.
      apply pathsinv0, assoc.
Qed.

Definition three_data : disp_cat_data _
  := (three_disp_ob_mor ,, three_id_comp).

Lemma three_axioms : disp_cat_axioms _ three_data.
Proof.
  (* left / right identity / associativity / homsets *)
  repeat apply tpair; intros; try (apply isapropdirprod; apply homset_property).
  apply isasetaprop.
  apply isapropdirprod; apply homset_property.
Qed.

Definition three_disp : disp_cat _
  := (three_data ,, three_axioms).

Definition three : category := total_category three_disp.

End Three_disp.

Section Face_maps.

Context (C : category).

Definition face_map_0_base : three_base C ⟶ arrow_base C.
Proof.
  use make_functor.
  - use make_functor_data.
    * intro xxx.
      exact (make_dirprod (pr1 xxx) (pr12 xxx)).
    * intros xxx yyy fff.
      exact (make_dirprod (pr1 fff) (pr12 fff)).
  - split.
    * intro xxx.
      apply binprod_id.
    * intros xxx yyy zzz ff gg.
      apply binprod_comp.
Defined.

Definition face_map_1_base : three_base C ⟶ arrow_base C.
Proof.
  use make_functor.
  - use make_functor_data.
    * intro xxx.
      exact (make_dirprod (pr1 xxx) (pr22 xxx)).
    * intros xxx yyy fff.
      exact (make_dirprod (pr1 fff) (pr22 fff)).
  - split.
    * intro xxx.
      apply binprod_id.
    * intros xxx yyy zzz ff gg.
      apply binprod_comp.
Defined.

Definition face_map_2_base : three_base C ⟶ arrow_base C.
Proof.
  use make_functor.
  - use make_functor_data.
    * intro xxx.
      exact (make_dirprod (pr12 xxx) (pr22 xxx)).
    * intros xxx yyy fff.
      exact (make_dirprod (pr12 fff) (pr22 fff)).
  - split.
    * intro xxx.
      apply binprod_id.
    * intros xxx yyy zzz ff gg.
      apply binprod_comp.
Defined.

Definition face_map_0_functor_data : disp_functor_data face_map_0_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - (* map on displayed objects *)
    intros xxx xxx'.
    simpl.
    destruct xxx' as [f1 _].
    exact f1.
  - (* map on displayed arrows *)
    simpl.
    intros xxx yyy ff gg F H.
    destruct H as [h1 _].
    symmetry.
    exact (pathsinv0 h1).
Defined.

Definition face_map_1_functor_data : disp_functor_data face_map_1_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - (* map on displayed objects *)
    intros xxx xxx'.
    simpl.
    destruct xxx' as [f1 f2].
    exact (f2 ∘ f1).
  - (* map on displayed arrows *)
    simpl.
    intros xxx yyy ff gg F H.
    destruct H as [h1 h2].
    symmetry.
    rewrite <- assoc.
    etrans.
    apply maponpaths.
    exact (pathsinv0 h2).
    rewrite assoc, assoc.
    apply cancel_postcomposition.
    exact (pathsinv0 h1).
Defined.

Definition face_map_2_functor_data : disp_functor_data face_map_2_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - (* map on displayed objects *)
    intros xxx xxx'.
    simpl.
    destruct xxx' as [_ f2].
    exact f2.
  - (* map on displayed arrows *)
    simpl.
    intros xxx yyy ff gg F H.
    destruct H as [_ h2].
    exact h2.
Defined.

Definition face_map_0_disp : disp_functor face_map_0_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - exact face_map_0_functor_data.
  (* can use homset_property of C to show that the morphisms are indeed equal *)
  - repeat split; intros; apply C.
Defined.

Definition face_map_1_disp : disp_functor face_map_1_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - exact face_map_1_functor_data.
  - repeat split; intros; apply C.
Defined.

Definition face_map_2_disp : disp_functor face_map_2_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - exact face_map_2_functor_data.
  - repeat split; intros; apply C.
Defined.

Definition face_map_0 := total_functor face_map_0_disp.
Definition face_map_1 := total_functor face_map_1_disp.
Definition face_map_2 := total_functor face_map_2_disp.

(* verify that they are indeed compatible *)
Lemma compatibility (fg : three C) : pr2 (face_map_2 fg ) ∘ pr2 (face_map_0 fg) = pr2 (face_map_1 fg).
Proof.
  trivial.
Defined.

End Face_maps.

Definition functorial_factorization (C : category) 
    := ∑ F : (arrow C ⟶ three C), functor_composite F (face_map_1 C) = functor_identity (arrow C).

