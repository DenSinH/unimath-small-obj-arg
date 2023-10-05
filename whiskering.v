
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Lemma post_whisker_functor_comp {A B : precategory} {C D : category}
    (F : functor B C) (G : functor C D) {a b : functor_data A B}
    (n : nat_trans a b) :
      post_whisker n (functor_composite F G) = post_whisker (post_whisker n F) G.
Proof.
  use nat_trans_eq; [apply homset_property|].
  intro x.
  simpl.
  reflexivity.
Qed.
