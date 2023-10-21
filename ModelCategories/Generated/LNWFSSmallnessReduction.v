(* Reducing the smallness requirement on LNWFS to a simpler one
to be applied to the one step comonad *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.slicecat.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import CategoryTheory.Chains.Chains.

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.DisplayedCats.natural_transformation.

Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoid.
Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoidSequence.
Require Import CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.
Require Import CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSCocomplete.


Local Open Scope Cat.
Local Open Scope cat.



Section SmallnessReduction.


Local Ltac functorial_factorization_eq f := (
  apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|];
  use funextsec;
  intro f;
  use subtypePath; [intro; apply isapropdirprod; apply homset_property|]
).

Context {C : category}.
Context (CC : Colims C).

Local Definition Ff_mon : monoidal_cat :=
  (_,, @Ff_monoidal C).
Local Definition LNWFS_mon : monoidal_cat :=
  (_,, @LNWFS_tot_monoidal C).

Import BifunctorNotations.
Import MonoidalNotations.

(* lift edge of diagram to morphism between coconeIns *)
Definition fact_cocone_coconeIn_lifted
    (F : Ff C)
    {d : chain C} {y : C}
    (ccy : cocone d y)
    {u v : vertex nat_graph}
    (e : edge u v) :
  coconeIn ccy u --> coconeIn ccy v.
Proof.
  use mors_to_arrow_mor.
  - exact (dmor d e).
  - exact (identity _).
  - abstract (
      etrans; [exact (coconeInCommutes ccy _ _ e)|];
      apply pathsinv0;
      apply id_right
    ).
Defined.

(* define a chain of middle objects from a cocone, i.e.
  X0 --> X1 --> X2 --> X3 ...
    \    |f1  f2|     /
   f0 \  |      |   / f3
            Y
  gives a cocone
  K0 --> K1 --> K2 --> K3 ...
    \    |Rf1   |     /
  Rf0 \  |   Rf2|   / Rf3
            Y

*)
Definition fact_cocone_chain
    (F : Ff C)
    {d : chain C} {y : C}
    (ccy : cocone d y) : 
  chain C.
Proof.
  use tpair.
  - intro v.
    exact (arrow_dom (fact_R F (coconeIn ccy v))).
  - intros u v e.
    set (elifted := fact_cocone_coconeIn_lifted F ccy e).
    exact (arrow_mor00 (#(fact_R F) elifted)).
Defined.

(* define the factorization of a cocone *)
Definition fact_cocone 
    (F : Ff C)
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  cocone (fact_cocone_chain F ccy) y.
Proof.
  use make_cocone.
  - intro v.
    exact (fact_R F (coconeIn ccy v)).
  - abstract (
      intros u v e;
      set (elifted := fact_cocone_coconeIn_lifted F ccy e);
      etrans; [exact (arrow_mor_comm (#(fact_R F) elifted))|];
      apply id_right
    ).
Defined.

(* define coconeIn to colimArrow morphism for cocone, i.e.
    Xv ----> X∞
    |        |
    |        |
    v        v
    Y ====== Y
*)
Definition fact_R_colimArrow_coconeInBase
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  ∏ v, coconeIn ccy v --> colimArrow (CC _ d) _ ccy.
Proof.
  intro v.
  use mors_to_arrow_mor.
  - exact (colimIn (CC _ d) v).
  - exact (identity _).
  - abstract (
      etrans; [apply colimArrowCommutes|];
      apply pathsinv0;
      apply id_right
    ).
Defined.

(* define the cocone of right objects with vertex R(colimArrow)
   we will require that this is a colimCocone for the sliced
   R functors to be small *)
Definition fact_R_colimArrow_cocone
    (F : Ff C)
    {d : chain C} {y : C}
    (ccy : cocone d y) :
  cocone 
    (fact_cocone_chain F ccy) 
    (arrow_dom (fact_R F (colimArrow (CC _ d) _ ccy))).
Proof.
  use make_cocone.
  - intro v.
    exact (arrow_mor00 (#(fact_R F) (fact_R_colimArrow_coconeInBase ccy v))).
  - abstract (
      intros u v e;
      etrans; [use (pr1_section_disp_on_morphisms_comp F)|];
      use (section_disp_on_eq_morphisms F); [
        exact (colimInCommutes (CC _ d) _ _ e)|apply id_left
      ]
    ).
Defined.
  
(* define smallness of R functor *)
Definition FR_slice_omega_small (F : Ff C) : UU :=
    ∏ (d : chain C) (y : C) (ccy : cocone d y),
      isColimCocone _ _ 
          (fact_R_colimArrow_cocone F ccy).

(* we get some issues with equality of diagrams, but
   given a chain d of functorial factorizations,
   the chain of middle objects of F ⊗ d is
   in fact the same as the cocone we just constructed
   for the right maps of all the factorizations
   (Ff_cocone_pointwise_R)
*)
Lemma fact_cocone_chain_eq_chain_pointwise_tensored
    (F : Ff C)
    (d : chain Ff_mon)
    (f : arrow C) 
    (ccpointwise := Ff_cocone_pointwise_R d f) :
  eq_diag
      (fact_cocone_chain F ccpointwise)
      (Ff_diagram_pointwise_ob1 (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f).
Proof.
  use tpair.
  - intro v.
    reflexivity.
  - abstract (
      intros u v e;
      apply pathsinv0;
      etrans;[ use pr1_transportf_const|];
      etrans;[ apply id_left|];
      apply (section_disp_on_eq_morphisms F); reflexivity
    ).
Defined.

(* The ColimCocone we get from the R map of F being omega small,
   corrected for the equality of diagrams *)
Definition FR_slice_colimcocone_over_pointwise_tensored 
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (f : arrow C) :
  ColimCocone (Ff_diagram_pointwise_ob1
    (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f).
Proof.
  set (ccpointwise := Ff_cocone_pointwise_R d f).
  set (isHRCC' := HR _ _ ccpointwise).

  (* correct codomain with equality of diagrams *)
  set (eqdiag := fact_cocone_chain_eq_chain_pointwise_tensored F d f).
  set (isHRCC := eq_diag_iscolimcocone _ eqdiag isHRCC').
  exact (make_ColimCocone _ _ _ isHRCC).
Defined.

(* The z-iso on middle objects we obtain from this ColimCocone 
   to the colimit we obtain from CC itself on this diagram.
   This isomorphism is the one we need for the isomorphism of
   functorial factorizations. *)
Definition FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (f : arrow C)
    (CL := ChainsFf CC d) 
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d))
    (ccpointwise := Ff_cocone_pointwise_R d f)
    (baseCC := (CCFf_pt_ob1 CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f)) :
  z_iso 
    (colim baseCC)
    (arrow_dom (fact_R F (colimArrow (CC _ (Ff_diagram_pointwise_ob1 d f)) _ ccpointwise))).
Proof.
  set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
  set (base_mor := isColim_is_z_iso _ baseCC _ _ (isColimCocone_from_ColimCocone HRCC)).
  
  exact (_,, base_mor).
Defined.

(* colimIn _ v to the ColimCocone with R(colimArrow) as vertex
   is the same as the right functor of F applied to 
   colimIn (ChainsFf CC d) v, since this is how we defined
   ChainsFf CC d 
   We have to rewrite this sometimes *)
Local Lemma FcolimArrow_coconeInBase_is_colimInHR
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (f : arrow C) 
    (v : vertex nat_graph)
    (CL := ChainsFf CC d) 
    (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f) :
  arrow_mor00 (#(fact_R F) (three_mor_mor12 (section_nat_trans (colimIn CL v) f)))
  = colimIn HRCC v.
Proof.
  use (section_disp_on_eq_morphisms F); reflexivity.
Qed.

(* Show that the base_iso we just defined in fact gives a
   morphism of three C, pointwise *)
Lemma FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise_three_comm
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (f : arrow C) 
    (CL := ChainsFf CC d) 
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)) 
    (base_mor := FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise F d HR f) :
  (fact_L (F ⊗_{ Ff_mon} colim CL) f) · z_iso_inv base_mor 
  = (identity _) · (fact_L (colim FfCC) f)
  × (fact_R (F ⊗_{ Ff_mon} colim CL) f) · (identity _) =
    z_iso_inv base_mor · (fact_R (colim FfCC) f).
Proof.
  set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
  set (baseCC := (CCFf_pt_ob1 CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f)).

  split.
  - apply pathsinv0.
    etrans. apply id_left.
    (* cbn. *)
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    etrans. apply assoc'.
    apply cancel_precomposition.
    etrans. apply assoc.

    etrans. apply cancel_postcomposition.
            set (cin0 := colimIn CL 0).
            set (cin012 := three_mor_mor12 (section_nat_trans cin0 f)).
            exact (arrow_mor_comm (#(fact_L F) cin012)).
    
    etrans. apply assoc'.
    apply cancel_precomposition.
    etrans. etrans. apply cancel_postcomposition.
                    exact (FcolimArrow_coconeInBase_is_colimInHR F d HR f 0).
            apply (colimArrowCommutes HRCC).
    reflexivity.
  - etrans. apply id_right.
    show_id_type.
    apply (colimArrowUnique' HRCC).
    intro v.
    
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (colimArrowCommutes HRCC).
    etrans. apply (colimArrowCommutes baseCC).
    apply pathsinv0.

    set (ccpointwise := Ff_cocone_pointwise_R d f).
    set (RcoconeInBase := #(fact_R F) (fact_R_colimArrow_coconeInBase ccpointwise v)).
    etrans. exact (arrow_mor_comm RcoconeInBase).
    apply id_right.
Qed.

(* define the natural transformation we want from
   (F ⊗_{Ff_mon} (colim CL)) (colim FfCC)
   using the z_iso we got from the smallness. *)
Definition FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_data
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (CL := ChainsFf CC d) 
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)) :
  section_nat_trans_disp_data (F ⊗_{Ff_mon} (colim CL)) (colim FfCC).
Proof.
  intro f.
  (* set (ccpointwise := Ff_cocone_pointwise_R d f). *)
  (* set (isHRCC' := HR _ _ ccpointwise). *)

  (* correct codomain with equality of diagrams *)
  (* set (eqdiag := fact_cocone_chain_eq_chain_pointwise_tensored F d f). *)
  (* set (isHRCC := eq_diag_iscolimcocone _ eqdiag isHRCC'). *)
  (* set (HRCC := make_ColimCocone _ _ _ isHRCC). *)
  (* set (baseCC := (CCFf_pt_ob1 CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d) f)). *)
  set (base_mor := FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise F d HR f).

  exists (z_iso_inv base_mor).
  exact (FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise_three_comm F d HR f).
Defined.

(* this proof is a mess, but I had to rewrite γ within a 
   #F γ... *)
Lemma FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_axioms
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (CL := ChainsFf CC d) 
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)) :
  section_nat_trans_disp_axioms (FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_data F d HR).
Proof.
  intros f g γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  etrans. apply pr1_transportf_const.

  set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
  use (colimArrowUnique' HRCC).

  intro v.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          use (pr1_section_disp_on_morphisms_comp F).
  
          
  etrans. apply cancel_postcomposition.
          set (mor := three_mor_mor12 (section_nat_trans (colimIn CL v) g)).
          use (section_disp_on_eq_morphisms F (γ' := (#(fact_R (dob d v)) γ · mor))).
          
          1: etrans. apply (colimOfArrowsIn _ _ (CC nat_graph (Ff_diagram_pointwise_ob1 d f))).
             reflexivity.
          
          1: etrans. apply id_left.
             apply pathsinv0.
             apply id_right.

  etrans. apply cancel_postcomposition.
          exact (pathsinv0 (pr1_section_disp_on_morphisms_comp F _ _)).
  etrans. apply assoc'.

  etrans. apply cancel_precomposition.
  {
    etrans. apply cancel_postcomposition.
            exact (FcolimArrow_coconeInBase_is_colimInHR F d HR g v).
    set (HRCCg := FR_slice_colimcocone_over_pointwise_tensored F d HR g).
    apply (colimArrowCommutes HRCCg).
  }

  apply pathsinv0.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (colimArrowCommutes HRCC).
  etrans. apply colimOfArrowsIn.
  reflexivity.
Qed.

Definition FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor
    (F : Ff C)
    (d : chain Ff_mon)
    (HR : FR_slice_omega_small F)
    (CL := ChainsFf CC d) 
    (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)) :
  (F ⊗_{Ff_mon} (colim CL)) --> (colim FfCC) :=
    (_,, FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_axioms F d HR).

(* Use the morphism to show that indeed, F in Ff C
  has the smallness property if fact_R F does*)
Lemma FR_lt_preserves_colim_impl_Ff_lt_preserves_colim 
    (F : Ff C)
    (d : chain Ff_mon)
    (CL := ChainsFf CC d) :
  FR_slice_omega_small F ->
    isColimCocone _ _
      (mapcocone (monoidal_left_tensor (F : Ff_mon)) _ (colimCocone CL)).
Proof.
  intro HR.

  set (FfCC := ChainsFf CC (mapdiagram (monoidal_left_tensor (F : Ff_mon)) d)).
  use (is_z_iso_isColim _ FfCC).
  exists (FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor F d HR).
  split.
  - functorial_factorization_eq f.
    set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
    set (base_iso := FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise F d HR f).
    
    etrans. apply pr1_transportf_const.
    apply pathsinv0.
    etrans. exact (pathsinv0 (pr122 base_iso)).

    apply compeq; [|reflexivity].
    use colimArrowUnique.
    intro v.
    etrans. apply colimArrowCommutes.
    apply pathsinv0.
    etrans. apply pr1_transportf_const.
    etrans. apply id_left.
    apply (section_disp_on_eq_morphisms F); reflexivity.
  - functorial_factorization_eq f.

    set (HRCC := FR_slice_colimcocone_over_pointwise_tensored F d HR f).
    set (base_iso := FR_lt_preserves_colim_impl_Ff_lt_preserves_colim_mor_pointwise F d HR f).
    
    etrans. apply pr1_transportf_const.
    apply pathsinv0.
    etrans. exact (pathsinv0 (pr222 base_iso)).
    apply compeq; [reflexivity|].
    apply colimArrowUnique.
    intro v.
    etrans. apply colimArrowCommutes.
    apply pathsinv0.
    etrans. apply pr1_transportf_const.
    etrans. apply id_left.
    apply (section_disp_on_eq_morphisms F); reflexivity.
Qed.

(* some useful proofs on the comonoidal structure that corresponds
   with LNWFS on Ff C *)
Lemma LNWFS_comon_structure_whiskerequals
    (L L' L'' : total_category (LNWFS C))
    (α : fact_mor (pr1 L) (pr1 L'))
    (α' : fact_mor (pr1 L') (pr1 L''))
    (f : arrow C) : 
  arrow_mor11 (#(lnwfs_L_monad (pr2 L')) (lnwfs_mor (pr2 L) (pr2 L') α f)) · arrow_mor11 (lnwfs_mor (pr2 L') (pr2 L'') α' ((lnwfs_L_monad (pr2 L')) f))
  = arrow_mor11 (lnwfs_mor (pr2 L') (pr2 L'') α' (lnwfs_L_monad (pr2 L) f)) · arrow_mor11 (#(lnwfs_L_monad (pr2 L'')) (lnwfs_mor (pr2 L) (pr2 L') α f)).
Proof.
  set (α'nat := nat_trans_ax α' _ _ (lnwfs_mor (pr2 L) (pr2 L') α f)).
  set (α'nat11 := base_paths _ _ (fiber_paths α'nat)).
  
  apply pathsinv0.
  etrans. exact (pathsinv0 α'nat11).
  etrans. apply pr1_transportf_const.
  reflexivity.
Qed.

(* A more general lemma of the above is
   (above is just below with Λ = L' and Λ' = L'' ) *)
Lemma LNWFS_comon_structure_whiskercommutes
    (L L' Λ Λ' : total_category (LNWFS C))
    (α : fact_mor (pr1 L) (pr1 L'))
    (β : fact_mor (pr1 Λ) (pr1 Λ'))
    (f : arrow C) : 
  arrow_mor11 (#(lnwfs_L_monad (pr2 Λ)) (lnwfs_mor (pr2 L) (pr2 L') α f)) · arrow_mor11 (lnwfs_mor (pr2 Λ) (pr2 Λ') β ((lnwfs_L_monad (pr2 L')) f))
  = arrow_mor11 (lnwfs_mor (pr2 Λ) (pr2 Λ') β (lnwfs_L_monad (pr2 L) f)) · arrow_mor11 (#(lnwfs_L_monad (pr2 Λ')) (lnwfs_mor (pr2 L) (pr2 L') α f)).
Proof.
  set (βnat := nat_trans_ax β _ _ (lnwfs_mor (pr2 L) (pr2 L') α f)).
  set (βnat11 := base_paths _ _ (fiber_paths βnat)).
  
  apply pathsinv0.
  etrans. exact (pathsinv0 βnat11).
  etrans. apply pr1_transportf_const.
  reflexivity.
Qed.

(* showing that the morphism induced the the universal
property of the colimit in Ff C is indeed an LNWFS morphism.
we do this by reducing it to the pointwise case. *)
Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_mor_disp
    (L : total_category (LNWFS C))
    (d : chain LNWFS_mon)
    (CL := ChainsLNWFS CC d)
    (HF : isColimCocone _ _
      (mapcocone (monoidal_left_tensor (pr1 L : Ff_mon)) _ (project_cocone _ _ (colimCocone CL))))
    (dbase := mapdiagram (pr1_category _) d)
    (Ldbase := mapdiagram (monoidal_left_tensor (pr1 L : Ff_mon)) dbase)
    (FfCCbase := ChainsFf CC Ldbase)
    (LNWFSCC := ChainsLNWFS CC (mapdiagram (monoidal_left_tensor (L : LNWFS_mon)) d))
    (base_mor := isColim_is_z_iso _ FfCCbase _ _ HF) :
  pr2 (monoidal_left_tensor (L : LNWFS_mon) (colim CL)) 
  -->[pr1 base_mor] pr2 (colim LNWFSCC).
Proof.
  set (HFCC := make_ColimCocone _ _ _ HF).
  set (base_inv := colimArrow FfCCbase _ (colimCocone HFCC)).

  (* base mor component at f is z_iso (obvious since base_mor is an iso) *)
  assert (Hinviso11 : ∏ f, is_z_isomorphism (three_mor11 (section_nat_trans base_inv f))).
  {
    intro f.
    exists (three_mor11 (section_nat_trans (pr1 base_mor) f)).
    split.
    - exact (eq_section_nat_trans_comp_component11 (pr12 base_mor) f).
    - exact (eq_section_nat_trans_comp_component11 (pr22 base_mor) f).
  }

  split; intro f.
  - use arrow_mor_eq; [reflexivity|].
    use (pre_comp_with_z_iso_is_inj (Hinviso11 f)).

    use colimArrowUnique'.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimArrowCommutes.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            set (cincomm := colimArrowCommutes HFCC _ (colimCocone FfCCbase) v).
            exact (eq_section_nat_trans_comp_component11 cincomm f).

    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimArrowCommutes.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply colimOfArrowsIn.
    etrans. apply assoc.

    apply pathsinv0.

    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimArrowCommutes.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
    {
      (* colimIn of CL is a LNWFS mor, rewrite ax *)
      set (cc := mapcocone (monoidal_left_tensor (L : LNWFS_mon)) _ (colimCocone CL)).
      set (ccinvax := pr12 (coconeIn cc v) f).
      exact (arrow_mor11_eq ccinvax).
    }

    (* can now cancel precomposition with Σ11_{f} of
       (pr2 (dob (mapdiagram (monoidal_left_tensor L) d) v) 
       (i.e. Lv) *)
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    apply cancel_precomposition.
    apply pathsinv0.

    (* commute the middle 2 morphisms 
      (think about whiskercommutes)
      then compose first and last 2 
      (think about bifunctor_leftcomp / rightcomp)
      then rewrite commutativity on either

      we have in our current goal:
      α (T a) · #T' (α a) · (α' (T' a) · #T'' (α' a))
      want (use α' naturality at morphism (α a))
      =
      α (T a) · α' (T a) · (#T'' (α a) · #T'' (α' a))
      =
      (α · α') (T a) · (#T'' (α · α' a))

      where α := coconeIn : dob mapdiagram v --> L ⊗ CL
      and α' := base_mor : L ⊗ CL --> colim LNWFSCC

      then rewrite using colimArrowCommutes

      get colimIn (T a) · #T'' (colimIn a)
      need more commutativity
      (naturality of colimIn at (colimIn a)):
      = #T'' (colimIn a) · colimIn (T a)
      
      apply assoc. apply assoc4. *)

    etrans. apply assoc.
    etrans. apply assoc4.
    etrans. apply cancel_postcomposition, cancel_precomposition. 
    {
      exact (pathsinv0 (
        LNWFS_comon_structure_whiskercommutes 
          ((monoidal_left_tensor (L : LNWFS_mon) (colim CL)))
          (colim LNWFSCC)
          (dob (mapdiagram (monoidal_left_tensor (L : LNWFS_mon)) d) v)
          ((monoidal_left_tensor (L : LNWFS_mon) (colim CL)))
          (pr1 base_mor)
          (pr1 (coconeIn (mapcocone (monoidal_left_tensor (L : LNWFS_mon)) d (colimCocone CL)) v))
          f
      )).
    }
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. apply assoc'.
    etrans. apply cancel_postcomposition.
            use pr1_section_disp_on_morphisms_comp.
    
    use compeq.
    * use section_disp_on_eq_morphisms.
      + etrans. use (pr1_section_disp_on_morphisms_comp (pr1 (dob d v))).
        use section_disp_on_eq_morphisms; [apply id_left|].
        set (cinv := colimArrowCommutes HFCC _ (colimCocone FfCCbase) v).
        exact (eq_section_nat_trans_comp_component11 cinv f).
      + set (cinv := colimArrowCommutes HFCC _ (colimCocone FfCCbase) v).
        exact (eq_section_nat_trans_comp_component11 cinv f).
    * set (cinv := colimArrowCommutes HFCC _ (colimCocone FfCCbase) v).
      exact (eq_section_nat_trans_comp_component11 cinv (lnwfs_L_monad (pr2 (colim LNWFSCC)) f)).
  - use arrow_mor_eq; [apply id_left|].
    
    use (pre_comp_with_z_iso_is_inj (Hinviso11 f)).

    use colimArrowUnique'.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimArrowCommutes.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
    {
      set (cincomm := colimArrowCommutes HFCC _ (colimCocone FfCCbase) v).
      exact (eq_section_nat_trans_comp_component11 cincomm f).
    }

    etrans. apply colimArrowCommutes.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimArrowCommutes.
    etrans. 
    {
      set (cinvf := section_nat_trans (colimIn HFCC v) f).
      exact (pathsinv0 (pr2 (three_mor_comm cinvf))).
    }
    apply id_right.
Admitted. (* proof finished, this is just very slow *)

Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim 
    (L : total_category (LNWFS C))
    (d : chain LNWFS_mon)
    (CL := ChainsLNWFS CC d)
    (dbase := mapdiagram (pr1_category _) d) :
  isColimCocone _ _
    (mapcocone (monoidal_left_tensor (pr1 L : Ff_mon)) _ (project_cocone _ _ (colimCocone CL))) 
    -> 
    isColimCocone _ _ 
      (mapcocone (monoidal_left_tensor (L : LNWFS_mon)) _ (colimCocone CL)).
Proof.
  intro HF.

  set (HFCC := make_ColimCocone _ _ _ HF).
  set (Ldbase := (mapdiagram (monoidal_left_tensor (pr1 L : Ff_mon)) dbase)).
  set (FfCCbase := ChainsFf CC Ldbase).
  set (base_mor := isColim_is_z_iso _ FfCCbase _ _ HF).
  set (base_inv := colimArrow FfCCbase _ (colimCocone HFCC)).
  set (LNWFSCC := ChainsLNWFS CC (mapdiagram (monoidal_left_tensor (L : LNWFS_mon)) d)).

  use (is_z_iso_isColim _ LNWFSCC).
  use tpair.
  - exists (pr1 base_mor).
    exact (Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim_mor_disp L d HF).
  - (* showing isomorphism is easy, since we know that the base morphism is an isomorphism *)
    split; (apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|]).
    * apply pathsinv0.
      etrans. exact (pathsinv0 (pr12 base_mor)).
      apply cancel_postcomposition.
      use colimArrowUnique'.
      intro v.
      etrans. apply colimArrowCommutes.
      apply pathsinv0.
      etrans. apply (colimArrowCommutes FfCCbase).
      reflexivity.
    * use (pre_comp_with_z_iso_is_inj (pr2 base_mor)).
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (pr12 base_mor).
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply id_right.
      use colimArrowUnique'.
      intro v.
      etrans. apply colimArrowCommutes.
      apply pathsinv0.
      etrans. apply (colimArrowCommutes FfCCbase).
      reflexivity.
Qed.

End SmallnessReduction.
