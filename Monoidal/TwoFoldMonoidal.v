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
Require Import CategoryTheory.Monoidal.MonoidalBinprod.


(* monoidal C := monoidal data / laws *)
(* monoidal_cat : ∑ category, monoidal *)
(* CategoriesOfMonoids: monoid *)

(* defining this as a category won't work, as it is not
   a category... *)
(* Section StrMonCatlax.

Definition StrMonCatlax_ob_mor : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (∑ C : category, monoidal C).
  - intros [C MC] [D MD].
    exact (∑ F : functor C D, fmonoidal_lax MC MD F).
Defined.

Definition StrMonCatlax_id_comp : precategory_id_comp StrMonCatlax_ob_mor.
Proof.
  split; intros.
  - exists (functor_identity _).
    exact (identity_fmonoidal_lax _).
  - exists (functor_composite (pr1 X) (pr1 X0)).
    exact (comp_fmonoidal_lax (pr2 X) (pr2 X0)).
Qed.

Definition StrMonCatlax_data : precategory_data :=
    (_,, StrMonCatlax_id_comp).

Definition StrMonCatlax_is_precategory : is_precategory StrMonCatlax_data.
Proof.
  use make_is_precategory_one_assoc; intros.
  - use subtypePath.
    * intro.
      unfold fmonoidal_lax.
Qed.

End StrMonCatlax. *)

(* Iterated Monoidal Categories:
  Monoidal Functor: F(0) = 0 (in monoidal_data: preserves_unit)
                    ηA,B : F(A)⊗F(B) => F(A⊗B) (in monoidal_data: preserves_tensordata)
  1 Internal Associativity: (diagram) ~~> preserves_associativity
  2 Internal Unit Conditions: ??
    either preserves_tensor_nat_left or preserves_leftunitality
    (and right)
*)

Definition monoidal_cat_with_functor :=
    ∑ (C : monoidal_cat), functor (category_binproduct C C) C.

Coercion monoidal_cat_with_functor_monoidal_cat (C : monoidal_cat_with_functor) := pr1 C.
Definition monoidal_cat_with_functor_functor (C : monoidal_cat_with_functor) := pr2 C.

Local Notation "x ⊗_{ C }^2 y" := (monoidal_cat_with_functor_functor C (make_dirprod x y)) (at level 31).

Definition twofold_monoidal_extassociator_data 
    (C : monoidal_cat_with_functor) :=
  ∏ (x y z : C), 
    C ⟦(x ⊗_{C}^2 y) ⊗_{C}^2 z, x ⊗_{C}^2 (y ⊗_{C}^2 z)⟧.

Definition twofold_monoidal_extassociatorinv_data 
    (C : monoidal_cat_with_functor) :=
  ∏ (x y z : C), 
    C ⟦x ⊗_{C}^2 (y ⊗_{C}^2 z), (x ⊗_{C}^2 y) ⊗_{C}^2 z⟧.

Definition twofold_monoidal_extrightunitor_data 
    (C : monoidal_cat_with_functor) :=
  ∏ (x : C), 
    C ⟦x ⊗_{C}^2 (monoidal_unit C), x⟧.

Definition twofold_monoidal_extrightunitorinv_data 
    (C : monoidal_cat_with_functor) :=
  ∏ (x : C), 
    C ⟦x, x ⊗_{C}^2 (monoidal_unit C)⟧.

Definition twofold_monoidal_extleftunitor_data 
    (C : monoidal_cat_with_functor) :=
  ∏ (x : C), 
    C ⟦(monoidal_unit C) ⊗_{C}^2 x, x⟧.

Definition twofold_monoidal_extleftunitorinv_data 
    (C : monoidal_cat_with_functor) :=
  ∏ (x : C), 
    C ⟦x, (monoidal_unit C) ⊗_{C}^2 x⟧.

Definition twofold_monoidal_data (C : monoidal_cat_with_functor) :=
    twofold_monoidal_extassociator_data C ×
    twofold_monoidal_extassociatorinv_data C ×
    twofold_monoidal_extrightunitor_data C ×
    twofold_monoidal_extrightunitorinv_data C ×
    twofold_monoidal_extleftunitor_data C ×
    twofold_monoidal_extleftunitorinv_data C.

Definition tf_monoidal_functor
    {C : monoidal_cat_with_functor}
    (TMD : twofold_monoidal_data C) :=
  monoidal_cat_with_functor_functor C.

Coercion tf_monoidal_cat
    {C : monoidal_cat_with_functor}
    (TMD : twofold_monoidal_data C) :=
  monoidal_cat_with_functor_monoidal_cat C.

Definition tf_monoidal_extassociatordata
    {C : monoidal_cat_with_functor}
    (TMD : twofold_monoidal_data C) :=
  pr1 TMD.
Notation "eα_{ TMD }" := (tf_monoidal_extassociatordata TMD).

Definition tf_monoidal_extassociatorinvdata
    {C : monoidal_cat_with_functor}
    (TMD : twofold_monoidal_data C) :=
  pr12 TMD.
Notation "eαinv_{ TMD }" := (tf_monoidal_extassociatorinvdata TMD).

Definition tf_monoidal_extrightunitordata
    {C : monoidal_cat_with_functor}
    (TMD : twofold_monoidal_data C) :=
  pr1 (pr22 TMD).
Notation "eru_{ TMD }" := (tf_monoidal_extrightunitordata TMD).

Definition tf_monoidal_extrightunitorinvdata
    {C : monoidal_cat_with_functor}
    (TMD : twofold_monoidal_data C) :=
  pr12 (pr22 TMD).
Notation "eruinv_{ TMD }" := (tf_monoidal_extrightunitorinvdata TMD).

Definition tf_monoidal_extleftunitordata
    {C : monoidal_cat_with_functor}
    (TMD : twofold_monoidal_data C) :=
  pr1 (pr22 (pr22 TMD)).
Notation "elu_{ TMD }" := (tf_monoidal_extleftunitordata TMD).

Definition tf_monoidal_extleftunitorinvdata
    {C : monoidal_cat_with_functor}
    (TMD : twofold_monoidal_data C) :=
  pr2 (pr22 (pr22 TMD)).
Notation "eluinv_{ TMD }" := (tf_monoidal_extleftunitorinvdata TMD).

(* todo: left unitor / right unitor vs left unit / right unit
   This is also the case in UniMath in general, what do we want? 
   Would it matter?
   
   I feel like it might complicate things a bit... *)
(* Definition  *)


Definition twofold_monoidal_laws (C : twofold_monoidal_data) :=
    fmonoidal_lax (MonoidalBinprod C C) C C.
