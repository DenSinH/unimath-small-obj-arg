Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.Retract.
Require Import CategoryTheory.ModelCategories.Lifting.
Require Import CategoryTheory.ModelCategories.NWFS.

Require Import CategoryTheory.DisplayedCats.algebras.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.


Context {C : category}.

Definition lifting_problem (f g : arrow C) := f --> g.

Definition filler {f g : arrow C} (S : lifting_problem f g) : UU := 
  ∑ l : (arrow_cod f) --> (arrow_dom g), 
    ((arrow_mor f) · l = (arrow_mor00 S)) × (l · (arrow_mor g) = (arrow_mor11 S)).

Definition filler_map {f g : arrow C} {S : lifting_problem f g} (f : filler S) := pr1 f.
Definition filler_comm {f g : arrow C} {S : lifting_problem f g} (f : filler S) := pr2 f.


Context (J : morphism_class C).

(* 
Definition morcls_disp : disp_cat (arrow C).
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ g, J _ _ g).
  - intros g g' d d' m.
    (* todo: only identity maps, unit gives all maps *)
    
    exact (∑ (H : g = g'), m = transportf _ H (identity _)).
  - intros.
    simpl in *.
    apply isaproptotal2.
    * intro. admit.
    * intros.
      admit.
  - intros.

  - intros.
    exact tt.
Defined.
*)

Definition morcls_disp : disp_cat (arrow C) :=
    disp_full_sub (arrow C) (λ g, J _ _ g).

Definition right_lifting_data (g : arrow C) : UU :=
    ∏ (f : arrow C), (J _ _ (arrow_mor f)) -> elp f g.

Definition rlp_morcls_disp : disp_cat (arrow C).
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ g, right_lifting_data g).
  - intros g g' δ δ' mn. 
    simpl in *.
    exact (∏ (f : arrow C) (H : J _ _ (arrow_mor f)) (S : lifting_problem f g),
          (filler_map (δ f H S)) · (arrow_mor00 mn) = 
          (filler_map (δ' f H (S · mn)))).
  - intros.
    do 3 (apply impred; intro).
    apply homset_property.
  - intros x a f H S.
    do 2 rewrite id_right.
    reflexivity.
  - intros g g' g'' δ δ' δ'' S0 S1 mn mn' g2 g2' S2.
    
    assert (arrow_mor00 (S0 · S1) = arrow_mor00 S0 · arrow_mor00 S1) as X.
    {
      trivial.
    }
    rewrite X, assoc.
    rewrite mn, mn', assoc.
    reflexivity.
Defined.

Definition rlp_morcls : category := total_category rlp_morcls_disp.

Context (n : nwfs C).

Definition morcls_L_map_structure : UU := 
  disp_functor (functor_identity _) (op_disp_cat morcls_disp) (nwfs_L_maps n).

(* "this assignation extends to a functor θ:", Garner 2007, p18 *)
Definition rlp_morcls_R_map_structure (η : morcls_L_map_structure) : 
    disp_functor (functor_identity _) (nwfs_R_maps n) (rlp_morcls_disp).
Proof.
  use tpair.
  - use tpair.
    * intros x hx.
      (* destruct h as [hα hlaws]. *)
      intros f hf hk.
      simpl in hk.

      unfold morcls_L_map_structure in η.
      set (test := η f hf).
      (* now just L_map_R_map_llp hx hf from nwfs_is_wfs! *)
      admit.
      (*
      destruct (η f hf) as [fα flaws].
      set (test := η f hf).
      simpl in test.
      *)
    * simpl.
      intros.
Defined.