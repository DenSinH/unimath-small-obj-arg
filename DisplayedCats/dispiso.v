Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Section disp_iso.

Definition is_disp_iso {C C'} {F} {D : disp_cat C} {D' : disp_cat C'} 
    (FF : disp_functor F D D') :=
  (disp_functor_ff FF) × ∏ (x : C), (isweq (λ (xx : D x), disp_functor_on_objects FF xx)).

Definition disp_iso {C C' : category} (F : functor C C') (D : disp_cat C) (D' : disp_cat C') :=
    ∑ FF : disp_functor F D D', is_disp_iso FF.

Context {C C' : category} {F : functor C C'} {D : disp_cat C} {D' : disp_cat C'}.

Definition isaprop_is_disp_iso (FF : disp_functor F D D') : 
    isaprop (is_disp_iso FF).
Proof.
  apply isapropdirprod.
  - do 5 (apply impred; intro).
    apply isapropisweq.
  - apply impred; intro.
    apply isapropisweq.
Qed.

Definition disp_functor_from_disp_iso (FF : disp_iso F D D')
  : disp_functor F D D' := pr1 FF.
Coercion disp_functor_from_disp_iso :
    disp_iso >-> disp_functor.

Definition disp_iso_ob_weq (FF : disp_iso F D D') :
    ∏ (x : C), (D x ≃ D' (F x)) :=
  λ x, make_weq (disp_functor_on_objects FF) (pr2 (pr2 FF) x).

End disp_iso.

Section disp_iso_id_inv.

Definition inv_disp_iso_id {C} {D D' : disp_cat C}
    (FF : disp_iso (functor_identity _) D D') : 
  disp_functor (functor_identity _) D' D.
Proof.
  use tpair.
  - use tpair.
    * intro x.
      exact (invweq (disp_iso_ob_weq FF x)).
    * intros x y xx yy f ff.
      simpl.

Defined.

End disp_iso_id_inv.