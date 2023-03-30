Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
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

Definition arrow_dom {C : category} (f : arrow C) : C := pr11 f.
Definition arrow_cod {C : category} (f : arrow C) : C := pr21 f.

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

Definition three_dom {C : category} (f : three C) : C := pr11 f.
Definition three_mid {C : category} (f : three C) : C := pr121 f.
Definition three_cod {C : category} (f : three C) : C := pr221 f.

Section Face_maps.

Context (C : category).

Definition face_map_0_base : three_base C ⟶ arrow_base C.
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
      exact (make_dirprod (pr1 xxx) (pr12 xxx)).
    * intros xxx yyy fff.
      exact (make_dirprod (pr1 fff) (pr12 fff)).
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
    destruct xxx' as [_ f2].
    exact f2.
  - (* map on displayed arrows *)
    simpl.
    intros xxx yyy ff gg F H.
    destruct H as [_ h2].
    symmetry.
    exact (pathsinv0 h2).
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
    destruct xxx' as [f1 _].
    exact f1.
  - (* map on displayed arrows *)
    simpl.
    intros xxx yyy ff gg F H.
    destruct H as [h1 _].
    exact h1.
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
Lemma face_compatibility (fg : three C) : pr2 (face_map_0 fg) ∘ pr2 (face_map_2 fg) = pr2 (face_map_1 fg).
Proof.
  trivial.
Defined.

Definition c_21 : face_map_2 ⟹ face_map_1.
Proof.
  (* this natural transformation boils down to square
    0 ===== 0
    |       |
    |       |
    1 ----> 2
  *)
  use make_nat_trans.
  - intro xxx.
    destruct xxx as [xxx [f1 f2]].
    simpl.
    exists (make_dirprod (identity _) f2).
    simpl.
    now rewrite id_left.
  - intros xxx yyy ff. 
    cbn.
    (* hot mess again, don't know what to do *)
    admit.
Admitted.

Definition c_10 : face_map_1 ⟹ face_map_0.
Proof.
  (* this natural transformation boils down to square
    0 ----> 1
    |       |
    |       |
    2 ===== 2
  *)
  use make_nat_trans.
  - intro xxx.
    destruct xxx as [xxx [f1 f2]].
    simpl.
    exists (make_dirprod f1 (identity _)).
    simpl.
    now rewrite id_right.
  - intros xxx yyy ff. 
    (* hot mess again, don't know what to do *)
    admit.
Admitted.

End Face_maps.

Arguments face_map_0 {_}.
Arguments face_map_1 {_}.
Arguments face_map_2 {_}.

(* Lemma face_map_1_preserves_dom {C : category} : ∏ g : three C, arrow_dom (face_map_1 g) = three_dom g.
Proof.
  trivial.
Defined.

Lemma face_map_1_preserves_cod {C : category} : ∏ g : three C, arrow_cod (face_map_1 g) = three_cod g.
Proof.
  trivial.
Defined. *)

Definition functorial_factorization (C : category) : UU := 
    ∑ F : (arrow C ⟶ three C), 
        F ∙ face_map_1 = functor_identity (arrow C).

Definition fact_functor {C : category} (F : functorial_factorization C) := pr1 F.
Coercion fact_functor : functorial_factorization >-> functor.
Definition fact_cond {C : category} (F : functorial_factorization C) := pr2 F.

Definition factorization_L {C : category} (F : functorial_factorization C) :=
    F ∙ face_map_2.
Definition factorization_R {C : category} (F : functorial_factorization C) :=
    F ∙ face_map_0.

Lemma fact_preserves_dom {C : category} (F : functorial_factorization C) (f : arrow C) :
    (three_dom (F f)) = arrow_dom f.
Proof.
  (* todo: why do I _have_ to use pr1 here (coercion)? *)
  change (arrow_dom ((functor_composite (pr1 F) face_map_1) f) = arrow_dom f).
  rewrite (fact_cond F).
  trivial.
Defined.

Lemma fact_preserves_cod {C : category} (F : functorial_factorization C) (f : arrow C) :
    (three_cod (F f)) = arrow_cod f.
Proof.
  change (arrow_cod ((functor_composite (pr1 F) face_map_1) f) = arrow_cod f).
  rewrite (fact_cond F).
  trivial.
Defined.

Lemma LR_compatibility {C : category} (F : functorial_factorization C) (f : arrow C) : 
   Type.
(* coq does not deduce that the resulting morphism has the same domain/codomain *)
(* pr2 (factorization_R F f) ∘ pr2 (factorization_L F f) = (pr2 f). *)
Proof.
  (* (factorization_R F f) ∘ (factorization_L F f) = (pr1 F f). *)
  set (lr := pr2 (factorization_R F f) ∘ pr2 (factorization_L F f)).
  set (id := pr2 f).
  simpl in id.
  simpl in lr.
  assert (three_cod (F f) = arrow_cod f).
  {
    apply fact_preserves_cod.
  }
  assert (three_dom (F f) = arrow_dom f).
  {
    apply fact_preserves_dom.
  }

  unfold three_cod in X.
  unfold arrow_cod in X.
  unfold three_dom in X0.
  unfold arrow_dom in X0.
  admit.
Admitted.

(* without any type specified, we get:
  fact_Φ : ∏ F : functorial_factorization ?C,
       functor_composite_data F face_map_2
       ⟹ functor_composite_data F face_map_1 *)
(* but we want:
  (functor_composite_data F face_map_2) ⟹ (functor_identity_data (arrow C)) *)
(* this should be the same by assumption in F *)
(* first definition: *)
(* Definition fact_Φ {C : category} (F : functorial_factorization C) :=
    pre_whisker F (c_21 C). *)
Definition fact_Φ {C : category} (F : functorial_factorization C) :
    (functor_composite F face_map_2) ⟹ (functor_identity (arrow C)).
Proof.
  (* use the condition in the factorization to rewrite the goal type to that
     of pre_whisker F (c_21 C) *)
  set (fact_condition := fact_cond F).
  simpl in fact_condition.
  change (functor_identity _) with (functor_identity (arrow C)) in fact_condition.
  rewrite <- fact_condition.
  exact (pre_whisker F (c_21 C)).
Defined.

(* similar here *)
(* Definition fact_Λ {C : category} (F : functorial_factorization C) :=
    pre_whisker F (c_10 C). *)
Definition fact_Λ {C : category} (F : functorial_factorization C) :
    (functor_identity (arrow C)) ⟹ (functor_composite F face_map_0).
Proof.
  set (fact_condition := fact_cond F).
  simpl in fact_condition.
  change (functor_identity _) with (functor_identity (arrow C)) in fact_condition.
  rewrite <- fact_condition.
  exact (pre_whisker F (c_10 C)).
Defined.

