Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.DisplayedCats.natural_transformation.

Require Import CategoryTheory.limits.coproducts.

Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.Generated.LiftingWithClass.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.OneStepMonad.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSSmallnessReduction.


Local Open Scope Cat.
Local Open Scope cat.

Section OSCSmall.

Context {C : category}.
Context (J : morphism_class C).
Context (CC : Colims C).

Local Definition F1 := one_step_factorization J CC.
Local Definition K := morcls_coprod_functor J CC.

Definition L1_K_colim_mor 
    (f : arrow C) :
  fact_L F1 f --> K f.
Proof.
  (* set (test := CoproductIn (morcls_lp_dom_coprod CC J f) (f,, identity f)). *)
  use mors_to_arrow_mor.
  * set (test := CoproductIn (morcls_lp_dom_coprod CC J f)).
    admit.
  * admit.
    (* use (CoproductIn (morcls_lp_dom_coprod CC J f)).  *)
Admitted.

(* this is just the pushout square *)
Definition colim_K_L1_mor_pointwise
  {g : graph} 
  (d : diagram g (arrow C))
  (v : vertex g) :
    dob (mapdiagram K d) v --> dob (mapdiagram (fact_L F1) d) v.
Proof.
  use mors_to_arrow_mor.
  * exact (arrow_mor00 (morcls_lp_coprod_diagram CC J (dob d v))).
  * exact (PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J (dob d v))).
  * abstract (
      set (pocomm := PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout CC J (dob d v)));
      exact (pathsinv0 pocomm)
    ).
Defined.

(* pushouts and coproducts commute *)
Lemma colim_K_L1_mor_commutes
    {g : graph} (d : diagram g (arrow C)) 
    {u v : vertex g} (e : edge u v) :
  dmor (mapdiagram K d) e · colim_K_L1_mor_pointwise d v
  = colim_K_L1_mor_pointwise d u · dmor (mapdiagram (fact_L F1) d) e.
Proof.
  use arrow_mor_eq.
  - etrans. apply (precompWithCoproductArrowInclusion).
    use CoproductArrow_eq'.
    intro S.
    etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d u))).
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d u))).
    reflexivity.
  - use CoproductArrow_eq'.
    intro S.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d u))).
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply (PushoutArrow_PushoutIn1).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d u))).
    reflexivity.
Qed.

Definition colim_K_L1_mor 
    {g : graph} (d : diagram g (arrow C)) :
  colim (arrow_colims CC g (mapdiagram K d)) 
  --> colim (arrow_colims CC g (mapdiagram (fact_L F1) d)).
Proof.
  use colimOfArrows.
  - intro v.
    exact (colim_K_L1_mor_pointwise d v).
  - abstract (
      exact (@colim_K_L1_mor_commutes g d)
    ).
Defined.

Lemma L1_preserves_colim_if_K_preserves_colim 
    {g : graph} {d : diagram g (arrow C)} 
    {f : arrow C} (ccf : cocone d f) :
  preserves_colimit K _ _ ccf
  -> preserves_colimit (fact_L F1) _ _ ccf.
Proof.
  intros HK isclCC.
  
  set (clCC := make_ColimCocone _ _ _ isclCC).
  set (HKCC := HK isclCC).
  set (K_mor := isColim_is_z_iso _ (arrow_colims CC _ (mapdiagram K d)) _ _ HKCC).
  set (test := pr1 K_mor).

  use (is_z_iso_isColim _ (arrow_colims CC _ (mapdiagram (fact_L F1) d))).
  use tpair.
  - use mors_to_arrow_mor.
    * cbn.
      unfold three_ob0.
      cbn.

    apply (compose (L1_K_colim_mor f)).
    apply (compose (pr1 K_mor)).
    exact (colim_K_L1_mor d).
  - split.
    * use (colimArrowUnique').
      intro v.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply colimArrowCommutes.
      etrans. apply assoc.
      
      
      
      apply (compose (arrow_mor00 (pr1 K_mor))).
      cbn.
      unfold three_ob0.
      cbn.
Admitted.

Lemma L1_small :
    preserves_colimits_of_shape (fact_L F1) nat_graph.
Proof.
  intros d cl cc.
  apply L1_preserves_colim_if_K_preserves_colim.
  
Admitted.

End OSCSmall.