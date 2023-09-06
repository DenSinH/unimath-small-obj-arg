Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.

Local Open Scope cat.
Import MonoidalNotations.
Import BifunctorNotations.

Definition pointed_monoidal_object {C : category} (M : monoidal C) : UU :=
    ∑ (T : C), I_{M} --> T.

Coercion ptd_T {C : category} {M : monoidal C} (T : pointed_monoidal_object M) := pr1 T.
Definition ptd_τ {C : category} {M : monoidal C} (T : pointed_monoidal_object M) := pr2 T.

Definition monoidal_alg_disp_ob_mor {C : category} {M : monoidal C} (T : pointed_monoidal_object M) : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    exact (∑ (x : (T) ⊗_{M} X --> X), x · (luinv_{M} _) · ((ptd_τ T) ⊗^{M}_{r} X) = (identity _)).
  - intros X Y XX YY f.
    simpl in XX, YY.
    exact ((pr1 XX) · f = ((T) ⊗^{M}_{l} f) · (pr1 YY)).
Defined.

Definition monoidal_alg_disp_id_comp {C : category} {M : monoidal C} (T : pointed_monoidal_object M) : 
    disp_cat_id_comp _ (monoidal_alg_disp_ob_mor T).
Proof.
  split.
  - intros X XX.
    abstract (
      cbn; now rewrite id_right, (bifunctor_leftid M), id_left
    ).
  - intros X Y Z f g XX YY ZZ ff gg.
    abstract (
      cbn; now rewrite assoc, ff, assoc', gg, assoc, (bifunctor_leftcomp M)
    ).
Defined.

Definition monoidal_alg_data {C : category} {M : monoidal C} (T : pointed_monoidal_object M) : 
    disp_cat_data C := (_,, monoidal_alg_disp_id_comp T).

Definition monoidal_alg_axioms {C : category} {M : monoidal C} (T : pointed_monoidal_object M) :
    disp_cat_axioms _ (monoidal_alg_data T).
Proof.
  repeat split; intros; try apply homset_property.
  apply isasetaprop.
  apply homset_property.
Defined.

Definition monoidal_alg_disp {C : category} {M : monoidal C} (T : pointed_monoidal_object M) : 
    disp_cat C := (_,, monoidal_alg_axioms T).

Definition monoidal_alg {C : category} {M : monoidal C} (T : pointed_monoidal_object M) : 
    category := total_category (monoidal_alg_disp T).

Definition monoidal_alg_left_action_data {C : category} {M : monoidal C} 
    (T : pointed_monoidal_object M) (A : C) :
  functor_data (monoidal_alg T) (monoidal_alg T).
Proof.
  use make_functor_data.
  - intro X.
    destruct X as [X [x xrel]].
    exists (X ⊗_{M} A).
    cbn.
    exists ((αinv_{M} T X A) · ( x ⊗^{M}_{r} A)).
    
    rewrite assoc', assoc'.
Admitted.

(* basically want to formalize Garner / Kelly (generalized) stuff about
   T-Alg (/ T-Mod in Garner)
   and how one obtains a monoid from the free T-algebra
   LNWFS should be a monoidal category (Ff_C) is at least

   
*)