Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.Functors.

Import BifunctorNotations.


Definition monoidal_binprod_tensor (C D : monoidal_cat) : tensor_data (category_binproduct C D).
Proof.
  use make_bifunctor_data.
  * intros a b.
    split.
    + exact ((pr1 a) ⊗_{C} (pr1 b)).
    + exact ((pr2 a) ⊗_{D} (pr2 b)).
  * intros a b1 b2 B.
    split; cbn.
    + exact ((pr1 a) ⊗^{C}_{l} (pr1 B)).
    + exact ((pr2 a) ⊗^{D}_{l} (pr2 B)).
  * intros a b1 b2 B.
    split; cbn.
    + exact ((pr1 B) ⊗^{C}_{r} (pr1 a)).
    + exact ((pr2 B) ⊗^{D}_{r} (pr2 a)).
Defined.

Definition monoidal_binprod_id (C D : monoidal_cat) : category_binproduct C D :=
    make_dirprod (monoidal_unit C) (monoidal_unit D).

Definition monoidal_binprod_data (C D : monoidal_cat) : monoidal_data (category_binproduct C D).
Proof.
  use make_monoidal_data.
  - exact (monoidal_binprod_tensor C D).
  - exact (monoidal_binprod_id C D).
  - intro; split; apply monoidal_leftunitordata.
  - intro; split; apply monoidal_leftunitorinvdata.
  - intro; split; apply monoidal_rightunitordata.
  - intro; split; apply monoidal_rightunitorinvdata.
  - intro; split; apply monoidal_associatordata.
  - intro; split; apply monoidal_associatorinvdata.
Defined.

Definition monoidal_binprod_laws (C D : monoidal_cat) : monoidal_laws (monoidal_binprod_data C D).
Proof.
  repeat split.
  - unfold bifunctor_leftidax.
    intros. apply pathsdirprod; apply (monoidal_tensor _).
  - unfold bifunctor_rightidax. 
    intros. apply pathsdirprod; apply (monoidal_tensor _).
  - unfold bifunctor_leftcompax. 
    intros. apply pathsdirprod; apply (monoidal_tensor _).
  - unfold bifunctor_rightcompax. 
    intros. apply pathsdirprod; apply (monoidal_tensor _).
  - unfold bifunctor_rightcompax. 
    intros.
    unfold functoronmorphisms_are_equal.
    intros.
    apply pathsdirprod; apply (monoidal_tensor _).
  - unfold leftunitor_nat.
    intros. apply pathsdirprod; apply monoidal_leftunitornat.
  - apply pathsdirprod; apply monoidal_leftunitorisolaw.
  - apply pathsdirprod; apply monoidal_leftunitorisolaw.
  - unfold rightunitor_nat.
    intros. apply pathsdirprod; apply monoidal_rightunitornat.
  - apply pathsdirprod; apply monoidal_rightunitorisolaw.
  - apply pathsdirprod; apply monoidal_rightunitorisolaw.
  - unfold associator_nat_leftwhisker.
    intros. apply pathsdirprod; apply monoidal_associatornatleft.
  - unfold associator_nat_rightwhisker.
    intros. apply pathsdirprod; apply monoidal_associatornatright.
  - unfold associator_nat_leftrightwhisker.
    intros. apply pathsdirprod; apply monoidal_associatornatleftright.
  - apply pathsdirprod; apply monoidal_associatorisolaw.
  - apply pathsdirprod; apply monoidal_associatorisolaw.
  - unfold triangle_identity.
    intros. apply pathsdirprod; apply monoidal_triangleidentity.
  - unfold pentagon_identity.
    intros. apply pathsdirprod; apply monoidal_pentagonidentity.
Qed.

Definition monoidal_binprod (C D : monoidal_cat) : monoidal (category_binproduct C D) :=
    (_,, monoidal_binprod_laws C D).

Definition monoidal_binprod_cat (C D : monoidal_cat) : monoidal_cat :=
    (_,, monoidal_binprod C D).
