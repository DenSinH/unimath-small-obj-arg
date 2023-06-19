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

Definition pointed_endofunctor (C : category) : UU :=
    ∑ F : functor C C, functor_identity _ ⟹ F.

Coercion functor_from_pointed_endofunctor
    {C : category} (F : pointed_endofunctor C) := pr1 F.

Definition ptd_endo_unit 
    {C : category} (F : pointed_endofunctor C) := pr2 F.

Definition ptd_endo_mor_law 
    {C : category} 
    {T T' : pointed_endofunctor C}
    (α : T ⟹ T') :=
  ∏ (a : C), (ptd_endo_unit T a) · α a = (ptd_endo_unit T' a).

Lemma isaprop_ptd_endo_mor_law 
    {C : category} 
    {T T' : pointed_endofunctor C}
    (α : T ⟹ T') : isaprop (ptd_endo_mor_law α).
Proof.
  apply impred; intro.
  apply homset_property.
Qed.

Definition ptd_endo_mor {C : category} (T T' : pointed_endofunctor C) :=
    ∑ α : T ⟹ T', ptd_endo_mor_law α.

Coercion ptd_endo_mor_nt {C : category} 
                         {T T' : pointed_endofunctor C}
                         (α : ptd_endo_mor T T') := pr1 α.
Definition ptd_endo_mor_laws {C : category} 
                             {T T' : pointed_endofunctor C}
                             (α : ptd_endo_mor T T') := pr2 α.

Definition ptd_endo_precat_ob_mor (C : category) : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (pointed_endofunctor C).
  - exact (ptd_endo_mor).
Defined.

Definition ptd_endo_precat_data (C : category) : precategory_data.
Proof.
  use make_precategory_data.
  - exact (ptd_endo_precat_ob_mor C).
  - intro T.
    cbn in T.
    exists (nat_trans_id T).
    abstract (
      intro;
      now rewrite id_right
    ).
- intros T T' T'' α α'.
  cbn in α, α'.
  exists (nat_trans_comp _ _ _ α α').
  abstract (
    intro;
    etrans; [apply assoc|];
    etrans; [apply maponpaths_2; apply (ptd_endo_mor_laws α)|];
    apply (ptd_endo_mor_laws α')
  ).
Defined.

Definition ptd_endo_is_precat (C : category) : is_precategory (ptd_endo_precat_data C).
Proof.
  use make_is_precategory_one_assoc; intros; (apply subtypePath; [intro; apply isaprop_ptd_endo_mor_law|]); simpl.
  - rewrite nat_trans_comp_id_left; [trivial| apply C].
  - rewrite nat_trans_comp_id_right; [trivial| apply C].
  - rewrite nat_trans_comp_assoc; [trivial| apply C].
Qed.

Definition ptd_endo_precat (C : category) : precategory :=
    (_,, ptd_endo_is_precat C).

Definition ptd_endo_has_homsets (C : category) : has_homsets (ptd_endo_precat C).
Proof.
  intros T T'.
  apply isaset_total2.
  - apply isaset_nat_trans.
    apply homset_property.
  - intro.
    apply isasetaprop.
    apply isaprop_ptd_endo_mor_law.
Qed.

Definition ptd_endo_cat (C : category) : category :=
    (ptd_endo_precat C,, ptd_endo_has_homsets C).

End pointed_endofunctor_def.

Section pointed_endofunctor_algebras.

Definition PtdEndoAlg_disp_ob_mor {C : category} (T : pointed_endofunctor C) : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    (* Algebra map *)
    exact (∑ (x : (T X) --> X), x · (ptd_endo_unit T X) = identity _).
  - intros X Y x y f.
    simpl in x, y.
    (*    x
        -----> 
      |       |
   Tf |       | f
      v       v
        -----> 
          y
    *)
    exact ( (#T f)%cat · (pr1 y) = (pr1 x) · f).
Defined.

Definition PtdEndoAlg_disp_id_comp {C : category} (T : pointed_endofunctor C) : 
    disp_cat_id_comp C (PtdEndoAlg_disp_ob_mor T).
Proof.
  split; intros; cbn.
  - now rewrite functor_id, id_left, id_right.
  - rewrite functor_comp, assoc'.
    now rewrite X0, assoc, X, assoc.
Defined.

Definition PtdEndoAlg_disp_data {C : category} (T : pointed_endofunctor C) : 
    disp_cat_data C :=
  (_,, PtdEndoAlg_disp_id_comp T).

Definition PtdEndoAlg_disp {C : category} (T : pointed_endofunctor C) :
    disp_cat C.
Proof.
  use tpair.
  - exact (PtdEndoAlg_disp_data T).
  - repeat split; intros; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
Defined.

End pointed_endofunctor_algebras.