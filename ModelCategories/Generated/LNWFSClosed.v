Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import CategoryTheory.Monads.Monads.
Require Import CategoryTheory.Monads.MonadAlgebras.
Require Import CategoryTheory.Monads.Comonads.
Require Import CategoryTheory.Monads.ComonadCoalgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import CategoryTheory.Chains.Chains.
Require Import CategoryTheory.limits.colimits.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Helpers.
Require Import CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSHelpers.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSCocomplete.

Local Open Scope cat.
Local Open Scope Cat.

Section Ff_closed.

Import BifunctorNotations.
Import MonoidalNotations.

Lemma monoidal_right_tensor_cocone 
    {C : category}
    (V : monoidal C)
    (A : C)
    {g : graph}
    (d : diagram g _)
    (CC : ColimCocone d)
    (CMon := (C,, V) : monoidal_cat) :
  cocone 
      (mapdiagram (monoidal_right_tensor (A : CMon)) d) 
      (monoidal_right_tensor (A : CMon) (colim CC)).
Proof.
  use tpair.
  - intro v.
    exact (colimIn _ v ⊗^{V}_{r} A).
  - abstract (
      intros u v e;
      etrans; [apply maponpaths_2|];
      [
        etrans; [apply cancel_precomposition;
                apply (bifunctor_leftid V)|];
        apply (id_right (dmor d e ⊗^{V}_{r} A))
      |];
      etrans; [apply (pathsinv0 (bifunctor_rightcomp V _ _ _ _ _ _))|];
      apply maponpaths;
      apply (colimInCommutes _ _ _ e)
    ).
Defined.

Context {C : category}.
Context (CC : Colims C).
Local Definition Ff_mon : monoidal_cat :=
    (_,, @Ff_monoidal C).
    
Context {g : graph}.
Context (H : is_connected g).
Context (v0 : vertex g).
Context (FfCC := λ d, ColimFfCocone CC d H v0).

(* define morphism into colimit pointwise on the middle objects *)
Lemma Ff_right_tensor_preserves_colimit_mor11
    (A : Ff_mon)
    (d : diagram g _)
    (f : arrow C) :
  three_ob1 (fact_functor (monoidal_right_tensor A (colim (FfCC d))) f) -->
    three_ob1 (fact_functor (colim (FfCC (mapdiagram (monoidal_right_tensor A) d))) f).
Proof.
  use colimArrow.
  use tpair.
  - intro v.
    exact (colimIn (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f) v).
  - abstract (
      intros u v e;
      (* cbn. *)
      etrans; [| 
        exact (colimInCommutes ((CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f)) _ _ e)
      ];
      apply cancel_postcomposition;
      apply pathsinv0;
      etrans; [use pr1_transportf_const|];
      etrans; [apply cancel_precomposition|];
      [
        etrans; [use (section_disp_on_eq_morphisms (dob d v) (γ' := identity _)); reflexivity|];
        apply maponpaths;
        apply (section_disp_id (dob d v))
      |];
      apply id_right
    ).
Defined.

Lemma Ff_right_tensor_preserves_colimit_mor
    (A : Ff_mon)
    (d : diagram g _) :
  (monoidal_right_tensor A) (colim (FfCC d)) -->
      colim (FfCC (mapdiagram (monoidal_right_tensor A) d)).
Proof.
  use tpair.
  - intro f.
    exists (Ff_right_tensor_preserves_colimit_mor11 A d f).
    abstract (
      split; [
        etrans; [apply assoc'|];
        apply pathsinv0;
        etrans; [apply id_left|];
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        apply pathsinv0;
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        apply (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f)))
      |
      etrans; [apply id_right|];
      apply pathsinv0;
      use colimArrowUnique;
      intro v;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
               apply (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f)))|];
      apply (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f))
      ]
    ).
  - abstract (
      intros f f' γ;
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|];
      etrans; [use pr1_transportf_const|];
      (* cbn. *)
      etrans; [apply precompWithColimOfArrows|];
      apply pathsinv0;
      etrans; [apply postcompWithColimArrow|];
      apply maponpaths;
      use cocone_paths;
      intro v;
      etrans; [use (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f) _ _ _ v)|];
      reflexivity
    ).
Defined.

Lemma Ff_right_tensor_preserves_colimit_mor_inv
    (A : Ff_mon)
    (d : diagram g _) :
  colim (FfCC (mapdiagram (monoidal_right_tensor A) d)) -->
    (monoidal_right_tensor A) (colim (FfCC d)).
Proof.
  use colimArrow.
  use monoidal_right_tensor_cocone.
Defined.

Lemma Ff_right_tensor_preserves_colimit_mor_are_inverses
    (A : Ff_mon)
    (d : diagram g _) :
  is_inverse_in_precat
    (Ff_right_tensor_preserves_colimit_mor A d)
    (Ff_right_tensor_preserves_colimit_mor_inv A d).
Proof.
  split.
  - functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    apply (colim_endo_is_identity).
    intro v.
    (* cbn. *)
    (* unfold Ff_right_tensor_preserves_colimit_mor11. *)
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f))).
    (* cbn. *)
    etrans. use (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f)).
    reflexivity.
  - functorial_factorization_mor_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    apply (colim_endo_is_identity).
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f)).
    etrans. use (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f))).
    reflexivity.
Qed.

(* Ff_right_closed: *)
Lemma Ff_right_tensor_preserves_colimit_mor_iso
    (A : Ff_mon)
    (d : diagram g _) : 
  z_iso 
    ((monoidal_right_tensor A) (colim (FfCC d)))
    (colim (FfCC (mapdiagram (monoidal_right_tensor A) d))).
Proof.
  exists (Ff_right_tensor_preserves_colimit_mor A d).
  exists (Ff_right_tensor_preserves_colimit_mor_inv A d).
  exact (Ff_right_tensor_preserves_colimit_mor_are_inverses A d).
Defined.

(* the following lemma can be used to get a ColimCocone of
   mapdiagram (monoidal_right_tensor A) d
   to monoidal_right_tensor A (colim (FfCC d)),
   so that we can lift the isomorphism to one in LNWFS,
   given that we know the colimit in LNWFS lies over
   that in Ff C  *)
Lemma Ff_right_tensor_cocone_isColimCocone
    (A : Ff_mon)
    (d : diagram g _) :
  isColimCocone _ _ (monoidal_right_tensor_cocone Ff_mon A d (FfCC d)).
Proof.
  intros cl cc.

  set (mor := colimUnivProp (FfCC (mapdiagram (monoidal_right_tensor A) d)) _ cc).
  destruct mor as [mor uniqueness].

  use unique_exists.
  - apply (compose (Ff_right_tensor_preserves_colimit_mor A d)).
    exact (pr1 mor).
  - intro v.
    etrans; [|exact (pr2 mor v)].
    etrans. apply assoc.
    apply cancel_postcomposition.
    apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
    apply funextsec.
    intro f.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    etrans. apply pr1_transportf_const.
    (* cbn. *)
    (* unfold Ff_right_tensor_preserves_colimit_mor11. *)
    apply (colimArrowCommutes (CCFf_pt_ob1 CC d (fact_R A f))).
  - intro; apply impred; intro; apply homset_property.
  - abstract (
      intros y Hy;
      
      (* unfold is_cocone_mor in Hy. *)
      apply (pre_comp_with_z_iso_is_inj 
        (z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso A d)));
      apply pathsinv0;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
              apply (is_inverse_in_precat2 (Ff_right_tensor_preserves_colimit_mor_are_inverses A d))|];
      etrans; [apply id_left|];
      apply pathsinv0;
      etrans; [|
        use (base_paths _ _ (uniqueness (z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso A d) · y,, _)))
      ]; [reflexivity|];
      
      intro v;
      etrans; [apply assoc|];
      etrans; [|exact (Hy v)];
      apply cancel_postcomposition;
      apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|];
      apply funextsec;
      intro f;
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|];
      etrans; [use pr1_transportf_const|];
      apply (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor A) d) f))
    ).
Defined.

Lemma Ff_rt_all_colimits 
    (A : Ff_mon) :
  preserves_colimits_of_shape (monoidal_right_tensor (A : Ff_mon)) g.
Proof.
  intros d cl cc.
  intros isCC.
  set (isCCAcl := Ff_right_tensor_cocone_isColimCocone A d).
  set (CCAcl := ((_,, (monoidal_right_tensor_cocone Ff_mon A d (FfCC d))),, isCCAcl) : ColimCocone _).
  set (base_iso := isColim_is_z_iso _ (FfCC d) _ _ isCC).
  (* destruct base_iso as [base_iso base_is_iso]. *)


  use (is_z_iso_isColim _ CCAcl).
  exists ((pr1 base_iso) ⊗^{_}_{r} A).
  abstract (
    split; [
      apply pathsinv0;
      use colim_endo_is_identity;
      intro u;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
              apply colimArrowCommutes|];
      etrans; [apply cancel_postcomposition, cancel_precomposition;
              apply (bifunctor_leftid Ff_mon)|];
      etrans; [apply cancel_postcomposition, id_right|];
      etrans; [exact (pathsinv0 (bifunctor_rightcomp Ff_mon _ _ _ _ _ _))|];
      etrans; [apply maponpaths;
              apply (colimArrowCommutes (make_ColimCocone _ _ _ isCC))|];
      reflexivity
    |
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightid Ff_mon _ _))|];
      etrans; [apply maponpaths;
              exact (pathsinv0 (pr22 base_iso))|];
      etrans; [apply (bifunctor_rightcomp Ff_mon)|];
      apply cancel_precomposition;
      use colimArrowUnique;
      intro u;
      apply pathsinv0;
      etrans; [apply cancel_precomposition;
              apply (bifunctor_leftid Ff_mon)|];
      etrans; [apply id_right|];
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightcomp Ff_mon _ _ _ _ _ _))|];
      apply maponpaths;
      apply colimArrowCommutes
    ]
  ).
Defined.

End Ff_closed.

Lemma Ff_rt_chain {C : category} (CC : Colims C): 
    rt_preserves_chains (@Ff_monoidal C).
Proof.
  exact (Ff_rt_all_colimits CC is_connected_nat_graph 0).
Defined.

Lemma Ff_rt_coeq {C : category} (CC : Colims C): 
    rt_preserves_coequalizers (@Ff_monoidal C).
Proof.
  exact (Ff_rt_all_colimits CC is_connected_coequalizer_graph (● 0)%stn).
Defined.

Section LNWFS_closed.

Import BifunctorNotations.
Import MonoidalNotations.

Context {C : category}.
Context (CC : Colims C).
Local Definition LNWFS_mon : monoidal_cat :=
    (_,, @LNWFS_tot_monoidal C).
    
Context {g : graph}.
Context (H : is_connected g).
Context (v0 : vertex g).
Context (LNWFSCC := λ d, ColimLNWFSCocone CC d H v0).


Lemma LNWFS_right_tensor_preserves_colimit_mor_inv_disp
    (A : LNWFS_mon)
    (d : diagram g _) 
    (dbase := mapdiagram (pr1_category _) d) :
  pr2 (colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)) )
  -->[Ff_right_tensor_preserves_colimit_mor_inv CC H v0 (pr1 A) dbase]
    pr2 ((monoidal_right_tensor A) (colim (LNWFSCC d))).
Proof.
  set (colimAL := colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
  set (AcolimL := monoidal_right_tensor A (colim (LNWFSCC d))).
  set (Ffiso := z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso CC H v0 (pr1 A) dbase)).
  set (LNWFSmor := colimArrow (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)) _ (mapcocone (monoidal_right_tensor A) _ (colimCocone (LNWFSCC d)))).

  (* rewrite commutativity of leftwhiskering functor and projection *)
  assert (
    Ff_right_tensor_preserves_colimit_mor_inv CC H v0 (pr1 A) dbase
    = pr1 LNWFSmor
  ) as X.
  {
    functorial_factorization_mor_eq f.
    use colimArrowUnique'.
    intro v.
    etrans. apply (colimArrowCommutes).
    apply pathsinv0.
    etrans. apply (colimArrowCommutes).
    etrans. apply pr1_transportf_const.
    etrans. apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC (mapdiagram (pr1_category (LNWFS C)) d) (fact_R (pr1 A) f))).
    etrans. apply cancel_postcomposition.
    {
      etrans. use (section_disp_on_eq_morphisms (pr1 (dob d v)) (γ' := identity _)); reflexivity.
      apply maponpaths.
      exact (section_disp_id (pr1 (dob d v)) _).
    }
    apply id_left.
  }
  rewrite X.
  exact (pr2 LNWFSmor).
Qed.

Local Lemma LNWFS_right_tensor_preserves_colimit_mor_disp
    (A : LNWFS_mon)
    (d : diagram g _) 
    (dbase := mapdiagram (pr1_category _) d) :
  pr2 ((monoidal_right_tensor A) (colim (LNWFSCC d)))
  -->[Ff_right_tensor_preserves_colimit_mor CC H v0 (pr1 A) dbase]
    pr2 (colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
Proof.
  set (colimAL := colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
  set (AcolimL := monoidal_right_tensor A (colim (LNWFSCC d))).
  set (Ffiso := z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso CC H v0 (pr1 A) dbase)).
  set (inv_disp := LNWFS_right_tensor_preserves_colimit_mor_inv_disp A d);
  exact (Ff_iso_inv_LNWFS_mor colimAL AcolimL Ffiso inv_disp).
Qed.

Lemma LNWFS_right_tensor_cocone_isColimCocone
    (A : LNWFS_mon)
    (d : diagram g _)
    (dbase := mapdiagram (pr1_category _) d) :
  isColimCocone _ _ (monoidal_right_tensor_cocone LNWFS_mon A d (LNWFSCC d)).
Proof.
  set (colimAL := colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
  set (AcolimL := monoidal_right_tensor A (colim (LNWFSCC d))).
  set (Ffiso := z_iso_inv (Ff_right_tensor_preserves_colimit_mor_iso CC H v0 (pr1 A) dbase)).
  
  use (is_z_iso_isColim _ (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
  use tpair.
  - exists (z_iso_inv Ffiso).
    exact (LNWFS_right_tensor_preserves_colimit_mor_disp A d).
  - abstract (
      set (adbase := (mapdiagram (pr1_category (LNWFS C)) (mapdiagram (monoidal_right_tensor A) d)));
      split; (apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|]); [
        etrans; [|exact (pr122 Ffiso)];
        apply cancel_postcomposition
      |
        etrans; [|exact (pr222 Ffiso)];
        apply cancel_precomposition
      ]; (use colimArrowUnique';
        intro v;
        etrans; [apply (colimArrowCommutes (ColimFfCocone CC adbase H v0))|];
        apply pathsinv0;
        etrans; [apply (colimArrowCommutes)|];
        reflexivity)
    ).
Defined.

Lemma LNWFS_rt_all_colimits 
    (A : LNWFS_mon) :
  preserves_colimits_of_shape (monoidal_right_tensor (A : LNWFS_mon)) g.
Proof.
  intros d cl cc.
  intros isCC.
  set (isCCAcl := LNWFS_right_tensor_cocone_isColimCocone A d).
  set (CCAcl := ((_,, (monoidal_right_tensor_cocone LNWFS_mon A d (LNWFSCC d))),, isCCAcl) : ColimCocone _).
  set (base_iso := isColim_is_z_iso _ (LNWFSCC d) _ _ isCC).

  use (is_z_iso_isColim _ CCAcl).
  exists ((pr1 base_iso) ⊗^{ LNWFS_mon}_{r} A).
  abstract (
    split; [
      apply pathsinv0;
      use colim_endo_is_identity;
      intro u;
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
              apply colimArrowCommutes|];
      etrans; [apply cancel_postcomposition, cancel_precomposition;
              apply (bifunctor_leftid LNWFS_mon)|];
      etrans; [apply cancel_postcomposition, id_right|];
      etrans; [exact (pathsinv0 (bifunctor_rightcomp LNWFS_mon _ _ _ _ _ _))|];
      etrans; [apply maponpaths;
              apply (colimArrowCommutes (make_ColimCocone _ _ _ isCC))|];
      reflexivity
    |
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightid LNWFS_mon _ _))|];
      etrans; [apply maponpaths;
              exact (pathsinv0 (pr22 base_iso))|];
      etrans; [apply (bifunctor_rightcomp LNWFS_mon)|];
      apply cancel_precomposition;
      use colimArrowUnique;
      intro u;
      apply pathsinv0;
      etrans; [apply cancel_precomposition;
              apply (bifunctor_leftid LNWFS_mon)|];
      etrans; [apply id_right|];
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightcomp LNWFS_mon _ _ _ _ _ _))|];
      apply maponpaths;
      apply colimArrowCommutes
    ]
  ).
Defined.

End LNWFS_closed.

Lemma LNWFS_rt_chain {C : category} (CC : Colims C): 
    rt_preserves_chains (@LNWFS_tot_monoidal C).
Proof.
  exact (LNWFS_rt_all_colimits CC is_connected_nat_graph 0).
Defined.

Lemma LNWFS_rt_coeq {C : category} (CC : Colims C): 
    rt_preserves_coequalizers (@LNWFS_tot_monoidal C).
Proof.
  exact (LNWFS_rt_all_colimits CC is_connected_coequalizer_graph (● 0)%stn).
Defined.