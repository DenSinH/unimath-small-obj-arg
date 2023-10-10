Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoid.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.

Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.

Local Open Scope cat.

Section LNWFS_adjunction_gives_NWFS.

Context {C : category}.
Local Definition LNWFSC := total_category (LNWFS C).

Definition LNWFS_pointed (T : LNWFSC) :
    pointed (@LNWFS_tot_monoidal C).
Proof.
  exists T.
  exact (LNWFS_tot_l_point T).
Defined.

Lemma alg_free_monad_exists_if_alg_forgetful_functor_right_action_is_adjoint 
    {T : LNWFSC} (X : Mon_alg _ (LNWFS_pointed T)) :
  alg_forgetful_functor_right_action_is_adjoint _ X -> 
    NWFS C (pr11 X).
Proof.
  intro Adj.
  
  use LNWFS_tot_monoid_is_NWFS.
  use alg_forgetful_functor_right_action_is_adjoint_monoid.
  exact Adj.
  - intro L.
    apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
    apply funextsec.
    intro f.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply cancel_postcomposition.
            use pr1_transportf_const.
    etrans. apply assoc'.
    etrans. apply id_left.
    etrans. apply id_right.

    set (Adjunit := unit_from_are_adjoints Adj LNWFS_tot_lcomp_unit).
    set (Adjunitf := section_nat_trans (pr1 Adjunit) f).
    (* simpl in t. *)
    set (Lf := fact_L (pr11 L) f).
    cbn.
    set (top_square := pr1 (pr22 Adjunitf)).
    set (bottom_square := pr2 (pr22 Adjunitf)).
    do 2 rewrite id_left in top_square.
    rewrite id_right in bottom_square.
    cbn.
    cbn in top_square, bottom_square.
    rewrite id_left in top_square.
    admit.
  - intro L.
    apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
    apply funextsec.
    intro f.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    apply pathsinv0.
    etrans. apply pr1_transportf_const.
    etrans. apply cancel_postcomposition.
            apply pr1_transportf_const.
    etrans. do 2 apply cancel_postcomposition.
            apply pr1_transportf_const.
    etrans. do 2 apply cancel_postcomposition.
            apply id_left.
    etrans. do 2 apply cancel_postcomposition.
    {
      etrans. use (section_disp_on_eq_morphisms (pr11 X) (γ':=identity _)); reflexivity.
      apply maponpaths.
      apply (section_disp_id (pr11 X)).
    }
    etrans. apply cancel_postcomposition, id_left.
    etrans. apply id_right.
    (* need to show L ⊗ (μ I) = μ L *)
    admit.
Defined.

End LNWFS_adjunction_gives_NWFS.