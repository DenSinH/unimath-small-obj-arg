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
    (Adj : alg_forgetful_functor_right_action_is_adjoint _ X) :
  let M := alg_forgetful_functor_right_action_is_adjoint_monoid LNWFS_tot_monoidal Adj in
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
  change (three_mor11 Adjunitf = Lf).
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
  - exact (alg_forgetful_functor_right_action_is_adjoint_rnwfs_cond Adj).
Defined.

End LNWFS_adjunction_gives_NWFS.