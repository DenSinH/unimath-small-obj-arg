
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
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

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import CategoryTheory.Chains.Chains.

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.NWFS.

Require Import CategoryTheory.ModelCategories.Generated.LiftingWithClass.
Require Import CategoryTheory.ModelCategories.Generated.OneStepMonad.
Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoid.
Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoidSequence.
Require Import CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.
Require Import CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSCocomplete.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSClosed.


Local Open Scope Cat.
Local Open Scope cat.


Section SmallObjectArgument.

Context {C : category}.
Context {J : morphism_class C}.
Context (CC : Colims C).

Local Definition CCoproducts :
  ∏ g, Coproducts (morcls_lp J g) C.
Proof.
  intro g.
  apply Coproducts_from_Colims.
  intro d.
  exact (CC _ d).
Defined.

Local Definition CCoequalizers :
  Coequalizers C := (Coequalizers_from_Colims _ CC).

Local Definition CPushouts : Pushouts C.
Proof.
  apply Pushouts_from_Coequalizers_BinCoproducts.
  - apply BinCoproducts_from_Colims.
    intro d.
    exact (CC _ d).
  - intros H z f g.
    set (coeq := CCoequalizers _ _ f g).
    use tpair.
    * exists (CoequalizerObject _ coeq).
      exact (CoequalizerArrow _ coeq).
    * exists (CoequalizerArrowEq _ coeq).
      intros w h Hw.
      use unique_exists.
      + exact (CoequalizerOut _ coeq _ h Hw).
      + exact (CoequalizerArrowComm _ coeq _ h Hw).
      + intro y; apply homset_property.
      + intros y Hy.
        exact (CoequalizerOutUnique _ _ _ _ _ _ Hy).
Defined.

Definition one_step_comonad_as_LNWFS : total_category (LNWFS C).
Proof.
  exists (one_step_factorization J CCoproducts CPushouts).
  exact (one_step_comonad J CCoproducts CPushouts).
Defined.

Definition LNWFS_pointed (L : total_category (LNWFS C)) :
    pointed (@LNWFS_tot_monoidal C) :=
  (_,, LNWFS_tot_l_point L).

  
Lemma osc_preserves_diagram_on :
  T_preserves_diagram_on  _
    (LNWFS_pointed one_step_comonad_as_LNWFS) 
    (ChainsLNWFS CC)
    (CoequalizersLNWFS CC)
    (monoidal_unit LNWFS_tot_monoidal).
Proof.

Admitted.

Lemma free_monoid_coeq_sequence_converges_for_osc :
  free_monoid_coeq_sequence_converges_on _
    (LNWFS_pointed one_step_comonad_as_LNWFS) 
    (ChainsLNWFS CC)
    (CoequalizersLNWFS CC)
    (monoidal_unit LNWFS_tot_monoidal).
Proof.
  apply T_preserves_diagram_impl_convergence_on.
  exact osc_preserves_diagram_on.
Qed.

Theorem small_object_argument :
    total_category (NWFS C).
Proof.
  set (lnwfs_monoid := 
    Tinf_monoid 
      (@LNWFS_tot_monoidal C)
      (LNWFS_pointed one_step_comonad_as_LNWFS)
      (ChainsLNWFS CC)
      (CoequalizersLNWFS CC)
      free_monoid_coeq_sequence_converges_for_osc
      (LNWFS_rt_coeq CC)
      (LNWFS_rt_chain CC)
  ).

  use tpair; [|exact (LNWFS_tot_monoid_is_NWFS lnwfs_monoid)].
Defined.

End SmallObjectArgument.