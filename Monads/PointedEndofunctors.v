Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp.

Section pointed_endofunctor_def.

Definition pointed_functor (C : precategory_data) : UU :=
    ∑ F : functor C C, functor_identity _ ⟹ F.

Coercion functor_from_pointed_functor 
    {C : precategory_data} (F : pointed_functor C) := pr1 F.

Definition ptd_endo_unit 
    {C : precategory_data} (F : pointed_functor C) := pr2 F.

End pointed_endofunctor_def.

Section pointed_endofunctor_algebras.

Definition PtdEndoAlg_disp_ob_mor {C : category} (T : pointed_functor C) : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    exact (∑ (x : (T X) --> X), x · (ptd_endo_unit T X) = identity _).
  - intros X Y x y f.
    simpl in x, y.
    exact ( (#T f)%cat · (pr1 y)= (pr1 x) · f).
Defined.

Definition PtdEndoAlg_disp_id_comp {C : category} (T : pointed_functor C) : 
    disp_cat_id_comp C (PtdEndoAlg_disp_ob_mor T).
Proof.
  split; intros; cbn.
  - now rewrite functor_id, id_left, id_right.
  - rewrite functor_comp, assoc'.
    now rewrite X0, assoc, X, assoc.
Defined.

Definition PtdEndoAlg_disp_data {C : category} (T : pointed_functor C) : 
    disp_cat_data C :=
  (_,, PtdEndoAlg_disp_id_comp T).

Definition PtdEndoAlg_disp {C : category} (T : pointed_functor C) :
    disp_cat C.
Proof.
  use tpair.
  - exact (PtdEndoAlg_disp_data T).
  - repeat split; intros; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
Defined.

End pointed_endofunctor_algebras.