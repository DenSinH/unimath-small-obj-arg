Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import CategoryTheory.Chains.Chains.
Require Import CategoryTheory.limits.colimits.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSCocomplete.

Local Open Scope cat.
Local Open Scope Cat.

(* todo: move this *)
Local Ltac functorial_factorization_eq f := (
  apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|];
  use funextsec;
  intro f;
  use subtypePath; [intro; apply isapropdirprod; apply homset_property|]
).

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
  - functorial_factorization_eq f.
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
  - functorial_factorization_eq f.
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

End Ff_closed.

Section LNWFS_closed.

Context {C : category}.
Context (CC : Colims C).
Local Definition LNWFS_mon : monoidal_cat :=
    (_,, @LNWFS_tot_monoidal C).
    
Context {g : graph}.
Context (H : is_connected g).
Context (v0 : vertex g).
Context (LNWFSCC := λ d, ColimLNWFSCocone CC d H v0).


Local Lemma LNWFS_right_tensor_preserves_colimit_mor_inv_disp_subproof
    (A : LNWFS_mon)
    (d : diagram g (total_category (LNWFS C)))
    (f : arrow C)
    (v : vertex g)
    (dbase := mapdiagram (pr1_category _) d) :
    fact_L (pr1 (dob d v0)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) f)) v0 =
    fact_L (pr1 (dob d v)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) f)) v.
Proof.
  set (predicate := λ v, fact_L (pr1 (dob d v0)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) f)) v0 =
                fact_L (pr1 (dob d v)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) f)) v).
  use (connected_graph_zig_zag_strong_induction v0 H predicate); [reflexivity|].
  enough (He : ∏ (u u' : vertex g) (e : edge u u'), 
            fact_L (pr1 (dob d u)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) f)) u =
            fact_L (pr1 (dob d u')) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) f)) u').
  {
    intros u u' Hu e.
    destruct e.
    - etrans. exact Hu.
      exact (He _ _ e).
    - etrans. exact Hu.
      apply pathsinv0.
      exact (He _ _ e).
  }
  
  intros u u' e.
  set (cinc := colimInCommutes (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) f))).
  etrans. apply cancel_precomposition.
          exact (pathsinv0 (cinc _ _ e)).
  etrans. apply assoc.
  apply cancel_postcomposition.
  (* cbn. *)
  
  set (comme := pr1 (three_mor_comm (section_nat_trans (pr1 (dmor d e)) (fact_R (pr1 A) f)))).
  etrans. exact comme.
  apply id_left.
Qed.

Lemma LNWFS_right_tensor_preserves_colimit_mor_inv_disp
    (A : LNWFS_mon)
    (d : diagram g _) 
    (dbase := mapdiagram (pr1_category _) d) :
  pr2 (colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)) )
  -->[Ff_right_tensor_preserves_colimit_mor_inv CC H v0 (pr1 A) dbase]
    pr2 ((monoidal_right_tensor A) (colim (LNWFSCC d))).
Proof.
  split; intro.
  - apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [apply pathsinv0, id_left|].
    use colimArrowUnique'.
    intro v.
    
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimArrowCommutes.
    etrans. 
    {
      etrans. apply assoc.
      etrans. 
      {
        apply cancel_postcomposition.
        etrans. apply assoc.
        etrans.
        {
          apply cancel_postcomposition.
          set (ccin := (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) a))).
          apply (colimOfArrowsIn _ _ ccin).
        }
        etrans. apply assoc'.
        apply cancel_precomposition.
        apply (colimOfArrowsIn).
      }
      etrans. apply assoc'.
      apply cancel_precomposition.
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply colimOfArrowsIn.
    }
    etrans. apply assoc.
    etrans. apply assoc.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
    {
      set (ccin := (CCFf_pt_ob1 CC
            (mapdiagram (pr1_category (LNWFS C)) (mapdiagram (monoidal_right_tensor A) d)) a)).
      etrans. apply (assoc (colimIn ccin v)).
      etrans. apply cancel_postcomposition.
              apply (colimOfArrowsIn _ _ ccin).
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply colimOfArrowsIn.
    }
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
    {
      set (ccin := (CCFf_pt_ob1 CC
            (mapdiagram (pr1_category (LNWFS C))
                (mapdiagram (monoidal_right_tensor A) d))
            (fact_L
                (colim
                  (ColimFfCocone CC
                      (mapdiagram (pr1_category (LNWFS C))
                        (mapdiagram (monoidal_right_tensor A) d)) H v0)) a))).
      etrans. apply (assoc (colimIn ccin v)).
      etrans. apply cancel_postcomposition.
              apply (colimArrowCommutes ccin).
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply colimArrowCommutes.
    }
    etrans. apply assoc.
    apply cancel_postcomposition.
    
    etrans. apply assoc'.
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    apply cancel_precomposition.

    etrans. apply (pr1_section_disp_on_morphisms_comp (pr1 (dob d v))).
    apply pathsinv0.
    etrans.
    {
      etrans. apply cancel_precomposition.
              apply (pr1_section_disp_on_morphisms_comp (pr1 (dob d v))).
      apply (pr1_section_disp_on_morphisms_comp (pr1 (dob d v))).
    }
    apply (section_disp_on_eq_morphisms (pr1 (dob d v))).
    * etrans. apply assoc'.
      apply pathsinv0.
      etrans. apply id_left.
      apply cancel_precomposition.
      apply pathsinv0.
      etrans.
      {
        etrans. apply cancel_precomposition.
                apply (pr1_section_disp_on_morphisms_comp (pr1 A)).
        apply (pr1_section_disp_on_morphisms_comp (pr1 A)).
      }
      apply section_disp_on_eq_morphisms.
      + etrans. apply id_left. apply id_left.
      + (* cbn. *)
        etrans. apply cancel_precomposition.
        {
          set (ccin := (CCFf_pt_ob1 CC
            (mapdiagram (pr1_category (LNWFS C)) (mapdiagram (monoidal_right_tensor A) d))
          a)).
          apply (colimArrowCommutes ccin).
        }
        (* cbn. *)
        apply pathsinv0.
        exact (LNWFS_right_tensor_preserves_colimit_mor_inv_disp_subproof A d a v).
    * etrans. apply id_left.
      etrans. 
      {
        set (ccin := (CCFf_pt_ob1 CC
            (mapdiagram (pr1_category (LNWFS C)) (mapdiagram (monoidal_right_tensor A) d))
        a)).
        apply (colimArrowCommutes ccin).
      }
      apply pathsinv0.
      apply id_right.
  - apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [apply id_left|].
    use colimArrowUnique.
    intro v.
    etrans. 
    {
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply colimArrowCommutes.
      (* cbn. *)
      set (ccin := (CCFf_pt_ob1 CC dbase (fact_R (pr1 A) a))).
      apply (colimArrowCommutes ccin).
    }
    reflexivity.
Qed.

Lemma LNWFS_right_tensor_preserves_colimit_mor_inv
    (A : LNWFS_mon)
    (d : diagram g _) 
    (dbase := mapdiagram (pr1_category _) d) :
  colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)) -->
    (monoidal_right_tensor A) (colim (LNWFSCC d)).
Proof.
  exists (Ff_right_tensor_preserves_colimit_mor_inv CC H v0 (pr1 A) dbase).
  exact (LNWFS_right_tensor_preserves_colimit_mor_inv_disp A d).
Defined.

Local Lemma LNWFS_right_tensor_preserves_colimit_mor_disp_subproof
    (A : LNWFS_mon)
    (d : diagram g (total_category (LNWFS C)))
    (f : arrow C)
    (v : vertex g)
    (dbase := mapdiagram (pr1_category _) d) :
    fact_L (pr1 (dob d v0)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f) v0 =
    fact_L (pr1 (dob d v)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f) v.
Proof.
  set (predicate := λ v, fact_L (pr1 (dob d v0)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f) v0 =
                fact_L (pr1 (dob d v)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f) v).
  use (connected_graph_zig_zag_strong_induction v0 H predicate); [reflexivity|].
  enough (He : ∏ (u u' : vertex g) (e : edge u u'), 
            fact_L (pr1 (dob d u)) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f) u =
            fact_L (pr1 (dob d u')) (fact_R (pr1 A) f) · colimIn (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f) u').
  {
    intros u u' Hu e.
    destruct e.
    - etrans. exact Hu.
      exact (He _ _ e).
    - etrans. exact Hu.
      apply pathsinv0.
      exact (He _ _ e).
  }
  
  intros u u' e.
  set (cinc := colimInCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f)).
  etrans. apply cancel_precomposition.
          exact (pathsinv0 (cinc _ _ e)).
  etrans. apply assoc.
  apply cancel_postcomposition.
  etrans. apply cancel_precomposition.
    use pr1_transportf_const.
  (* cbn. *)
  set (mor := (three_mor_mor12 (section_nat_trans_data (Ff_precategory_id (pr1 A)) f))).
  set (dmoreax := nat_trans_ax (section_nat_trans (pr1 (dmor d e))) _ _ mor).
  set (dmoreaxb := base_paths _ _ (fiber_paths dmoreax)).
  etrans. apply cancel_precomposition.
  {
    etrans. exact (pathsinv0 dmoreaxb).
    use pr1_transportf_const.
  }

  (* cbn. *)
  set (commLu := arrow_mor_comm (#(fact_L (pr1 (dob d u))) mor)).
  (* cbn in comm. *)
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
    exact (pathsinv0 commLu).
  etrans. apply assoc'.
  etrans. apply id_left.

  set (comme := pr1 (three_mor_comm (section_nat_trans (pr1 (dmor d e)) (fact_R (pr1 A) f)))).
  etrans. exact comme.
  apply id_left.
Qed.

Lemma LNWFS_right_tensor_preserves_colimit_mor_disp
    (A : LNWFS_mon)
    (d : diagram g _) 
    (dbase := mapdiagram (pr1_category _) d) :
  pr2 ((monoidal_right_tensor A) (colim (LNWFSCC d))) 
  -->[Ff_right_tensor_preserves_colimit_mor CC H v0 (pr1 A) dbase]
      pr2 (colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
Proof.
  split; intro f.
  - apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [apply pathsinv0, id_left|].
    use colimArrowUnique'.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use colimArrowCommutes.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
    {
      apply (colimOfArrowsIn _ _ (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f)).
    }
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
    {
      apply (colimOfArrowsIn).
    }
    etrans. apply assoc.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. do 2 apply cancel_postcomposition.
            apply assoc.
    etrans. do 3 apply cancel_postcomposition.
            apply colimOfArrowsIn.
    etrans. do 2 apply cancel_postcomposition.
            apply assoc'.
    etrans. do 2 apply cancel_postcomposition.
            apply cancel_precomposition.
            apply colimOfArrowsIn.
    etrans. apply cancel_postcomposition.
    {
      etrans. apply assoc'.
      apply cancel_precomposition.
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply colimArrowCommutes.
    }
    etrans. apply assoc.

    etrans. do 2 apply cancel_postcomposition.
            apply assoc.
    etrans. apply assoc'.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
    {
      set (premor := pr1
            (section_disp_on_morphisms (pr11 (dob d v))
              (LNWFS_lcomp_comul_L'_lp (ColimLNWFS_disp CC d H v0) (pr2 A) f))).
      etrans. apply (assoc' premor).
      apply cancel_precomposition.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              set (ccin := CCFf_pt_ob1 CC (mapdiagram (pr1_category (LNWFS C)) d)
                            (fact_R (pr1 A)
                              ((fact_L (pr1 A) f)
                                · fact_L (pr1 (colim (LNWFSCC d))) (fact_R (pr1 A) f)))).
              apply (colimOfArrowsIn _ _ ccin).
      etrans. apply assoc'.
      apply cancel_precomposition.
      set (ccin := (CCFf_pt_ob1 CC (mapdiagram (pr1_category (LNWFS C)) d)
            (fact_R (pr1 A)
              (lnwfs_L_monad
                  (pr2 (colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)))) f)))).
      apply (colimArrowCommutes ccin).
    }
    etrans. apply assoc.
    etrans. apply assoc.
    apply cancel_postcomposition.
    etrans. apply assoc'.
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    apply cancel_precomposition.
    etrans. apply (pr1_section_disp_on_morphisms_comp (pr1 (dob d v))).
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply (pr1_section_disp_on_morphisms_comp (pr1 (dob d v))).
    etrans. apply (pr1_section_disp_on_morphisms_comp (pr1 (dob d v))).
    apply section_disp_on_eq_morphisms.
    * etrans. apply id_left.
      etrans. apply assoc'.
      apply pathsinv0.
      etrans. apply assoc'.
      apply cancel_precomposition.
      
      etrans. apply (pr1_section_disp_on_morphisms_comp (pr1 A)).
      apply pathsinv0.
      etrans. apply (pr1_section_disp_on_morphisms_comp (pr1 A)).
      apply (section_disp_on_eq_morphisms (pr1 A)); [reflexivity|].
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
      {
        set (ccin := (CCFf_pt_ob1 CC (mapdiagram (pr1_category (LNWFS C)) d) (fact_R (pr1 A) f))).
        apply (colimArrowCommutes ccin).
      } 
      (* cbn. *)
      (* path induction on v *)
      exact (LNWFS_right_tensor_preserves_colimit_mor_disp_subproof A d f v).
    * etrans. apply cancel_precomposition.
              apply id_left.
      apply pathsinv0.
      etrans. apply id_left.
      apply pathsinv0.
      etrans. 
      {
        set (ccin := (CCFf_pt_ob1 CC (mapdiagram (pr1_category (LNWFS C)) d) (fact_R (pr1 A) f))).  
        apply (colimArrowCommutes ccin).
      }
      reflexivity.
  - apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [apply id_left|].
    use colimArrowUnique.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use colimArrowCommutes.
    apply (colimArrowCommutes (CCFf_pt_ob1 CC (mapdiagram (monoidal_right_tensor (pr1 A : Ff_mon)) dbase) f)).
Qed.

Lemma LNWFS_right_tensor_preserves_colimit_mor
    (A : LNWFS_mon)
    (d : diagram g _) 
    (dbase := mapdiagram (pr1_category _) d) :
  (monoidal_right_tensor A) (colim (LNWFSCC d)) -->
      colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d)).
Proof.
  exists (Ff_right_tensor_preserves_colimit_mor CC H v0 (pr1 A) dbase).
  exact (LNWFS_right_tensor_preserves_colimit_mor_disp A d).
Defined.

Lemma LNWFS_right_tensor_preserves_colimit_mor_are_inverses
    (A : LNWFS_mon)
    (d : diagram g _) 
    (dbase := mapdiagram (pr1_category _) d) :
  is_inverse_in_precat
    (LNWFS_right_tensor_preserves_colimit_mor A d)
    (LNWFS_right_tensor_preserves_colimit_mor_inv A d).
Proof.
  split.
  - apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    exact (is_inverse_in_precat1 (Ff_right_tensor_preserves_colimit_mor_are_inverses CC H v0 (pr1 A) dbase)).
  - apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    exact (is_inverse_in_precat2 (Ff_right_tensor_preserves_colimit_mor_are_inverses CC H v0 (pr1 A) dbase)).
Qed.

Lemma LNWFS_right_tensor_preserves_colimit_mor_iso
    (A : LNWFS_mon)
    (d : diagram g _) : 
  z_iso 
    ((monoidal_right_tensor A) (colim (LNWFSCC d)))
    (colim (LNWFSCC (mapdiagram (monoidal_right_tensor A) d))).
Proof.
  exists (LNWFS_right_tensor_preserves_colimit_mor A d).
  exists (LNWFS_right_tensor_preserves_colimit_mor_inv A d).
  exact (LNWFS_right_tensor_preserves_colimit_mor_are_inverses A d).
Defined.

End LNWFS_closed.