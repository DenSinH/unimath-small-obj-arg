Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.Foundations.HLevels.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Local Open Scope cat.

Section HomSetFunctors.

Context {C : category}.

Definition homSet_functor_data :
  functor_data (category_binproduct (C^op) C) hset_category.
Proof.
  use make_functor_data.
  + intros pair.
    induction pair as (p1, p2).
    use make_hSet.
    - exact (C ⟦ p1, p2 ⟧).
    - use (homset_property C).
  + intros x y fg h.
    induction fg as (fg1, fg2).
    cbn in fg1.
    exact (fg1 · h · fg2).
Defined.

Lemma is_functor_homSet_functor_type : is_functor homSet_functor_data.
Proof.
  use make_dirprod.
  - intro; cbn.
    apply funextsec; intro.
    refine (id_right _ @ _).
    apply id_left.
  - repeat intro.
    apply funextsec; intro; cbn.
    do 3 rewrite assoc.
    reflexivity.
Defined.

Definition homSet_functor : functor (category_binproduct (C^op) C) hset_category :=
  make_functor _ is_functor_homSet_functor_type.

Context (c : C).

Definition cov_homSet_functor : functor C hset_category :=
  functor_fix_fst_arg (C^op) _ _ homSet_functor c.

Definition contra_homSet_functor : functor (C^op) hset_category :=
  functor_fix_snd_arg (C^op) _ _ homSet_functor c.

End HomSetFunctors.