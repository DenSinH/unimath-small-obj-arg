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

Lemma alg_forgetful_functor_right_action_is_adjoint_rnwfs_cond 
    {T : LNWFSC} {X : Mon_alg _ (LNWFS_pointed T)}
    {Adj : alg_forgetful_functor_right_action_is_adjoint _ X}
    (ηr : alg_forgetful_functor_right_action_adjoint_monad_unit_preserves_right_tensor _ Adj)
    (μr : alg_forgetful_functor_right_action_adjoint_monad_mul_preserves_right_tensor _ Adj) :
  let M := alg_forgetful_functor_right_action_is_adjoint_monoid LNWFS_tot_monoidal ηr μr in
  Ff_monoid_RNWFS_condition (LNWFS_tot_monoid_projection M).
Proof.
  apply Ff_monoid_RNWFS_base_condition_iff_cond.
  (* unfold Ff_monoid_RNWFS_base_condition. *)
  (* suffices to show that for f, 
     three_mor11 (unit f) = λ_{pr11 X} f. This follows 
     directly from the way the unit looks:

     X ====== X
     =        |
     =        |
     =        v
     X -----> Ef
     |        |
   f |        |
     v        v
     Y ====== Y
     commutativity of the top square gives the result
  *)
  
  intro f.
  (* cbn. *)
  etrans. use pr1_transportf_const.
  etrans. apply id_right.
  (* cbn. *)
  
  set (Adjunit := unit_from_are_adjoints Adj (monoidal_unit LNWFS_tot_monoidal)).
  set (Adjunitf := section_nat_trans (pr1 Adjunit) f).
  (* simpl in t. *)
  set (Lf := fact_L (pr11 X) f).
  (* change (three_mor11 Adjunitf = Lf). *)
  set (top_square := pr1 (pr22 Adjunitf)).
  rewrite id_left in top_square.
  etrans. exact top_square.
  etrans. apply id_left.
  apply id_right.
Qed.

Lemma alg_free_monad_exists_if_alg_forgetful_functor_right_action_is_adjoint 
    {T : LNWFSC} (X : Mon_alg _ (LNWFS_pointed T)) :
  alg_forgetful_functor_right_action_is_adjoint _ X -> 
    NWFS C (pr11 X).
Proof.
  intro Adj.
  
  use LNWFS_tot_monoid_is_NWFS.
  - use alg_forgetful_functor_right_action_is_adjoint_monoid.
    exact Adj.
    * intro L.
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
      etrans. apply cancel_precomposition.
              use (section_disp_on_eq_morphisms _ (γ' := identity _)); reflexivity.
      etrans. do 2 apply maponpaths.
              apply (section_disp_id (pr1 L)).
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
      rewrite id_right in top_square.
      etrans. use (section_disp_on_eq_morphisms (pr1 L)).
      + use mors_to_arrow_mor.
        -- exact (fact_L (pr11 X) f).
        -- exact (identity _).
        -- rewrite id_right.
           apply (three_comp (fact_functor (pr11 X) f)).
      + exact top_square.
      + reflexivity.
      + admit.
    * intro L.
      apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
      apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
      apply funextsec.
      intro f.
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
      
      apply pathsinv0.
      etrans. use pr1_transportf_const.
      etrans. apply cancel_postcomposition.
              use pr1_transportf_const.
      etrans. do 2 apply cancel_postcomposition.
              use pr1_transportf_const.
      etrans. do 2 apply cancel_postcomposition.
              apply id_left.
      etrans. do 2 apply cancel_postcomposition.
      {
        etrans. apply (section_disp_on_eq_morphisms (pr1 L) (γ' := identity _)); reflexivity.
        apply maponpaths.
        exact (section_disp_id (pr1 L) _).
      }
      etrans. apply cancel_postcomposition, id_left.
      etrans. apply cancel_precomposition.
      {
        etrans. apply (section_disp_on_eq_morphisms (pr1 L) (γ' := identity _)); reflexivity.
        apply maponpaths.
        exact (section_disp_id (pr1 L) _).
      }
      etrans. apply id_right.
      
      admit.
  - apply (alg_forgetful_functor_right_action_is_adjoint_rnwfs_cond).
Defined.

End LNWFS_adjunction_gives_NWFS.