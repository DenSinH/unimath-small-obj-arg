Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.

Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.DisplayedCats.natural_transformation.

Require Import CategoryTheory.limits.coproducts.
Require Import CategoryTheory.categories.HSET.Core.

Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.LiftingWithClass.
Require Import CategoryTheory.ModelCategories.Generated.OneStepMonad.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.
Require Import CategoryTheory.limits.colimits.


Local Open Scope Cat.
Local Open Scope cat.

Section OSCSmall.

Context {C : category}.
Context (J : morphism_class C).
Context (CC : Colims C).

Local Definition F1 := one_step_factorization J CC.
Local Definition K := morcls_coprod_functor J CC.


Definition presentable (x : C) :=
    preserves_colimits_of_shape 
      (cov_homSet_functor x) 
      nat_graph.

Lemma K_small_if_J_small :
  (∏ (f : arrow C), J _ _ f -> (presentable (arrow_dom f)))
  -> (∏ (f : arrow C), J _ _ f -> (presentable (arrow_cod f)))
  -> preserves_colimits_of_shape K nat_graph.
Proof.
  intros Hdom Hcod.
  intros d cl cc isclCC.

  set (clCC := make_ColimCocone _ _ _ isclCC).
  set (Kd00 := project_diagram00 (mapdiagram K d)).
  set (Kd11 := project_diagram11 (mapdiagram K d)).

  use (is_z_iso_isColim _ (arrow_colims CC _ (mapdiagram K d))).
  use tpair.
  - use (colimArrow (id_Colim nat_graph (K cl) is_connected_nat_graph 0)).
    use make_cocone.
    * intro v.
      use mors_to_arrow_mor.
      + use (CoproductArrow).
        intro S.
        set (test := Hdom (morcls_lp_map S) (pr2 (morcls_lp_map S))).
        set (t := test _ _ _ (pr2 (CC _ (project_diagram00 d)))).
        cbn in t.
        set (tcc := make_ColimCocone _ _ _ t).
        set (dbase := (mapdiagram (cov_homSet_functor (arrow_dom (morcls_lp_map S))) (project_diagram00 d))).

        set (x := isColim_is_z_iso _ (ColimsHSET _ dbase) _ _ t).
        transparent assert (arr : (arrow_dom (morcls_lp_map S) --> colim (CC _ (project_diagram00 d)))).
        {
          apply (compose (arrow_mor00 S)).
          set (isclCC00 := project_colimcocone00 CC isclCC).
          set (clCC00 := make_ColimCocone _ _ _ isclCC00).
          exact (colimArrow clCC00 _ (colimCocone (CC _ (project_diagram00 d)))).
        }
        set (abc := pr1 x arr).
        cbn.
        cbn in abc.
        set (abct := pr1 abc).
      

    use mors_to_arrow_mor.
    * use CoproductArrow.
      intro S.
      set (test := Hdom (morcls_lp_map S) (pr2 (morcls_lp_map S))).
      set (t := test _ _ _ (pr2 (CC _ Kd00))).
      cbn in t.
      set (tcc := make_ColimCocone _ _ _ t).
      cbn.
      set (isclCC00 := project_colimcocone00 CC isclCC).
      set (clCC00 := make_ColimCocone _ _ _ isclCC00).
      set (SdomCC := id_Colim nat_graph (arrow_dom (morcls_lp_map S)) is_connected_nat_graph 0).
      use (colimOfArrows SdomCC).
      + intro v.
        set (x := colimIn tcc v).
        cbn in x.
        cbn.
        apply x.
        assert (lp : morcls_lp J (dob d v)).
        {
          exists (morcls_lp_map S).

          admit.
        }
        set (abc := CoproductIn (morcls_lp_dom_coprod CC J (dob d v)) lp).
        cbn in abc.


      apply (compose (arrow_mor00 S)).
      use (colimOfArrows clCC00).
      + intro v.
        cbn.
      cbn.

      cbn.
      (* smallness *)
      admit.
    * use CoproductArrow.
      intro S.
      cbn.
  

Admitted.

(* no need for information about f here,
   this morphism is just the pushout square *)
Definition K_L1_colim_mor (f : arrow C) :
   K f --> fact_L F1 f.
Proof.
 use mors_to_arrow_mor.
 * exact (arrow_mor00 (morcls_lp_coprod_diagram CC J f)).
 * exact (PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J f)).
 * abstract (
     set (pocomm := PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout CC J f));
     exact (pathsinv0 pocomm)
   ).
Defined.

(* this is just the pushout square again *)
Definition colim_K_L1_mor_pointwise
  {g : graph} 
  (d : diagram g (arrow C))
  (v : vertex g) :
    dob (mapdiagram K d) v 
    --> dob (mapdiagram (fact_L F1) d) v :=
  K_L1_colim_mor (dob d v).

(* pushouts and coproducts commute *)
Lemma colim_K_L1_mor_commutes
    {g : graph} (d : diagram g (arrow C)) 
    {u v : vertex g} (e : edge u v) :
  dmor (mapdiagram K d) e · colim_K_L1_mor_pointwise d v
  = colim_K_L1_mor_pointwise d u · dmor (mapdiagram (fact_L F1) d) e.
Proof.
  use arrow_mor_eq.
  - etrans. apply (precompWithCoproductArrowInclusion).
    use CoproductArrow_eq'.
    intro S.
    etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d u))).
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d u))).
    reflexivity.
  - use CoproductArrow_eq'.
    intro S.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d u))).
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply (PushoutArrow_PushoutIn1).
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (dob d u))).
    reflexivity.
Qed.

(* colim (K fi) --> colim (L1 fi) *)
Definition colim_K_L1_mor 
    {g : graph} (d : diagram g (arrow C)) :
  colim (arrow_colims CC g (mapdiagram K d)) 
  --> colim (arrow_colims CC g (mapdiagram (fact_L F1) d)).
Proof.
  use colimOfArrows.
  - intro v.
    exact (colim_K_L1_mor_pointwise d v).
  - abstract (
      exact (@colim_K_L1_mor_commutes g d)
    ).
Defined.

(* colim (K fi) --> K (colim fi) *)
Definition can_K_mor
    {g : graph} (d : diagram g (arrow C))
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  z_iso 
    (colim (arrow_colims CC g (mapdiagram K d)))
    (K f).
Proof.
  set (HKCC := HK isclCC).
  set (K_mor := isColim_is_z_iso _ (arrow_colims CC _ (mapdiagram K d)) _ _ HKCC).
  exact (_,, K_mor).
Defined.

(* L1 (colim fi) --> colim fi *)
Definition L_colim_id_mor (f : arrow C) :
    fact_L F1 f --> f.
Proof.
  exact (η (lnwfs_L_monad (one_step_comonad J CC)) f).
Defined.

(* colim (L1 fi) --> colim fi *)
Definition colim_L_id_mor 
    {g : graph} (d : diagram g (arrow C))
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf)  :
  colim (arrow_colims CC g (mapdiagram (fact_L F1) d))
  --> f.
Proof.
  use colimArrow.
  set (ccL1f := mapcocone (fact_L F1) _ ccf).
  use make_cocone.
  - intro v.
    use mors_to_arrow_mor.
    * exact (arrow_mor00 (coconeIn ccL1f v)).
    * exact ((arrow_mor11 (coconeIn ccL1f v)) · fact_R F1 f).
    * abstract (
        apply pathsinv0;
        etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                exact (pathsinv0 (arrow_mor_comm (coconeIn ccL1f v)))|];
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        exact (three_comp (fact_functor F1 f))
      ).
  - abstract (
      intros u v e;
      set (ccL1fcomm := coconeInCommutes ccL1f _ _ e);
      use arrow_mor_eq; [
        exact (arrow_mor00_eq ccL1fcomm)
      | etrans; [apply assoc|];
        etrans; [apply cancel_postcomposition;
                 exact (arrow_mor11_eq ccL1fcomm)|];
        reflexivity
      ]
    ).
Defined.

(* we need to know that arrow_dom f is 
   a colimit for (L1 d)00, after all, all morphisms
   are identity. We need an isomorphism *)
Definition dom_colim_dom_L1_cocone
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} (ccf : cocone d f):
  cocone (project_diagram00 (mapdiagram (fact_L F1) d)) (arrow_dom f).
Proof.
  use make_cocone.
  - intro v. exact (arrow_mor00 (coconeIn ccf v)).
  - abstract (intros u v e; exact (arrow_mor00_eq (coconeInCommutes ccf _ _ e))).
Defined.

Definition dom_colim_dom_L1_isColimCocone
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  isColimCocone _ _ (dom_colim_dom_L1_cocone ccf).
Proof.
  set (base_mor := isColim_is_z_iso _ (arrow_colims CC _ d) _ _ isclCC).
  use (is_z_iso_isColim _ (CC _ (project_diagram00 (mapdiagram (fact_L F1) d)))).
  exists (arrow_mor00 (pr1 base_mor)).
  abstract (
    split; [
      etrans; [|exact (arrow_mor00_eq (pr12 base_mor))];
      apply cancel_postcomposition
      | etrans; [|exact (arrow_mor00_eq (pr22 base_mor))];
        apply cancel_precomposition
    ]; (
      use colimArrowUnique;
      intro v;
      etrans; [apply colimArrowCommutes|];
      reflexivity
    )
  ).
Defined.

(* the isomorphism dom f --> colim (L1 d)00 *)
Definition colim_dom_L1_dom_iso 
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  z_iso
    (arrow_dom f)
    (colim (CC _ (project_diagram00 (mapdiagram (fact_L F1) d)))).
Proof.
  set (fCC := dom_colim_dom_L1_isColimCocone isclCC).
  set (baseCC := CC _ (project_diagram00 (mapdiagram (fact_L F1) d))).
  set (mor := isColim_is_z_iso _ baseCC _ _ fCC).
  exact (z_iso_inv (_,, mor)).
Defined.

(* arrow_dom (L1 colim fi) --> arrow_dom (colim (L1 fi)) *)
Definition L1_colim_L1_map00
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  arrow_dom (fact_L F1 f)
  --> arrow_dom (colim (arrow_colims CC g (mapdiagram (fact_L F1) d))). 
Proof. 
  apply (compose (arrow_mor00 (L_colim_id_mor f))).
  exact (colim_dom_L1_dom_iso isclCC).
Defined.

(* K (colim fi) --> colim (L1 fi) *)
(* arrow_mor11 is the bottom pushout map *)
Definition Kcolim_colimL1_mor 
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  K f
  --> colim (arrow_colims CC g (mapdiagram (fact_L F1) d)).
Proof.
  apply (compose (z_iso_inv (can_K_mor d HK isclCC))).
  exact (colim_K_L1_mor d).
Defined.

(* top pushout map *)
Definition L1_colim_L1_map_pushoutOut2
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf) :
  arrow_dom (fact_L F1 f)
  --> arrow_cod (colim (arrow_colims CC g (mapdiagram (fact_L F1) d))).
Proof.
  apply (compose (L1_colim_L1_map00 isclCC)). 
  exact (colim (arrow_colims CC g (mapdiagram (fact_L F1) d))).
Defined.

(* we show that arrow_dom (K f) is a colimCocone,
   given that (K f) is a colim for the mapped diagram,
   i.e. we project the ColimCocone to the 0 ob/arr *)
Definition L1_colim_L1_map_dom_Kf_is_colimCocone
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf)
    (isHKCC := HK isclCC)
    (HKCC := make_ColimCocone _ _ _ isHKCC)
    (HKCC00 := project_cocone00 (colimCocone HKCC)) :
  isColimCocone _ _ HKCC00 :=
    project_colimcocone00 CC isHKCC.

(* we show that arrow_cod (K f) is a colimCocone,
   given that (K f) is a colim for the mapped diagram,
   i.e. we project the ColimCocone to the 1 ob/arr *)
Definition L1_colim_L1_map_cod_Kf_is_colimCocone
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf)
    (isHKCC := HK isclCC)
    (HKCC := make_ColimCocone _ _ _ isHKCC)
    (HKCC11 := project_cocone11 (colimCocone HKCC)) :
  isColimCocone _ _ HKCC11 :=
    project_colimcocone11 CC isHKCC.

(* we show that the canonical iso from 
   K (colim fi) --> colim (K fi)
   projects to the one on the domains *)
Local Lemma colim_iso_inv_projects 
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf)
    (dbase := project_diagram00 (mapdiagram K d))
    (isKfCC := L1_colim_L1_map_dom_Kf_is_colimCocone HK isclCC)
    (KfCC := make_ColimCocone _ _ _ isKfCC) 
    (Kf_mor := isColim_is_z_iso _ (CC _ dbase) _ _ isKfCC) :
  arrow_mor00 (z_iso_inv (can_K_mor d HK isclCC))
  = pr1 Kf_mor.
Proof.
  set (iso := (_,, Kf_mor) : z_iso _ _).
  apply (post_comp_with_z_iso_is_inj iso).
  apply pathsinv0.
  etrans. exact (pr22 Kf_mor).
  
  set (can_K_is_iso := pr222 (can_K_mor d HK isclCC)).
  etrans. exact (pathsinv0 (arrow_mor00_eq can_K_is_iso)).
  apply cancel_precomposition.
  use colimArrowUnique.
  intro v.
  etrans. apply (colimArrowCommutes (CC g dbase)).
  reflexivity.
Qed.

Local Lemma L1_colim_L1_map_ispushoutOut_subproof0
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  arrow_mor00 (Kcolim_colimL1_mor HK isclCC)
  · z_iso_inv (colim_dom_L1_dom_iso isclCC)
  = arrow_mor00 (morcls_lp_coprod_diagram CC J f).
Proof. 
  set (isKfCC := L1_colim_L1_map_dom_Kf_is_colimCocone HK isclCC).
  set (KfCC := make_ColimCocone _ _ _ isKfCC).

  use (colimArrowUnique' KfCC).
  intro v.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply assoc.
  etrans. do 2 apply cancel_postcomposition.
          etrans. apply cancel_precomposition.
                  exact (colim_iso_inv_projects HK isclCC).
          apply (colimArrowCommutes KfCC).
  etrans. apply cancel_postcomposition.
          apply (colimArrowCommutes (CC _ (project_diagram00 (mapdiagram K d)))).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          apply (colimArrowCommutes (CC _ (project_diagram00 (mapdiagram (fact_L F1) d)))).
  
  apply pathsinv0.
  etrans. apply (precompWithCoproductArrowInclusion _ _ (morcls_lp_dom_coprod CC J f)).
  use CoproductArrow_eq'.
  intro S.
  etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d v))).
  etrans. apply id_left.
  apply pathsinv0.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (dob d v))).
  reflexivity.
Qed.

Lemma L1_colim_L1_map_ispushoutOut_subproof
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  arrow_mor00 (K_L1_colim_mor f) 
  · (L1_colim_L1_map00 isclCC)
  = arrow_mor00 (Kcolim_colimL1_mor HK isclCC).
Proof. 
  use CoproductArrow_eq'.
  intro S.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f)).
  etrans. apply cancel_precomposition.
          apply id_left.
  
  apply (post_comp_with_z_iso_is_inj (z_iso_inv (colim_dom_L1_dom_iso isclCC))).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (pr122 (colim_dom_L1_dom_iso isclCC)).
  etrans. apply id_right.
  
  apply pathsinv0.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (L1_colim_L1_map_ispushoutOut_subproof0 HK isclCC).
  etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J f)).
  reflexivity.
Qed.

Lemma L1_colim_L1_map_ispushoutOut
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  K f · arrow_mor11 (Kcolim_colimL1_mor HK isclCC)
  = arrow_mor00 (K_L1_colim_mor f) 
  · L1_colim_L1_map_pushoutOut2 isclCC.
Proof.
  apply pathsinv0.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          exact (L1_colim_L1_map_ispushoutOut_subproof HK isclCC).
  
  exact (arrow_mor_comm (Kcolim_colimL1_mor HK isclCC)).
Qed.

(* the map L1 (colim fi) --> colim (L1 fi)
   that we need, defined with the pushout *)
Definition L1_colim_L1_map
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  fact_L F1 f
  --> colim (arrow_colims CC g (mapdiagram (fact_L F1) d)).
Proof.
  set (KLcolimPO := morcls_lp_coprod_diagram_pushout CC J f).
  use mors_to_arrow_mor.
  * exact (L1_colim_L1_map00 isclCC).
  * use (PushoutArrow KLcolimPO).
    + exact (arrow_mor11 (Kcolim_colimL1_mor HK isclCC)).
    + exact (L1_colim_L1_map_pushoutOut2 isclCC).
    + exact (L1_colim_L1_map_ispushoutOut HK isclCC).
  * abstract (
      set (poin2 := PushoutArrow_PushoutIn2 KLcolimPO _ _ _ (L1_colim_L1_map_ispushoutOut HK isclCC));
      exact (pathsinv0 poin2)
    ).
Defined.

(* the canonical arrow from f --> (colim CC d)
   (where the colimit is not necessarily f)
   projects down to the colimArrow on the domains  *)
Local Lemma colimArrow_projects
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (isclCC : isColimCocone d f ccf)
    (fcc := make_ColimCocone d f ccf isclCC)
    (domfcc := make_ColimCocone _ _ _ (dom_colim_dom_L1_isColimCocone isclCC)) :
  arrow_mor00 (colimArrow fcc _ (colimCocone (arrow_colims CC _ d)))
  = colimArrow domfcc _ (colimCocone (CC _ (project_diagram00 d))).
Proof.
  use (colimArrowUnique' domfcc).
  intro v.
  etrans. exact (arrow_mor00_eq (colimArrowCommutes fcc _ (colimCocone (arrow_colims CC _ d)) v)).
  apply pathsinv0.
  etrans. apply colimArrowCommutes.
  reflexivity.
Qed.

Local Lemma colimIn00_L1_colim_L1_commutes
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) 
    (v : vertex g) :
    arrow_mor00 (coconeIn (mapcocone (fact_L F1) d ccf) v · L1_colim_L1_map HK isclCC) =
    arrow_mor00 (colimIn (arrow_colims CC g (mapdiagram (fact_L F1) d)) v).
Proof.
  set (domfiscc := dom_colim_dom_L1_isColimCocone isclCC).
  set (domfcc := make_ColimCocone _ _ _ domfiscc).
  etrans. apply cancel_precomposition.
          apply id_left.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          etrans. apply cancel_precomposition.
                  exact (colimArrow_projects isclCC).
          apply (colimArrowCommutes domfcc).
  etrans. apply (colimArrowCommutes (CC _ (project_diagram00 d))).
  reflexivity.
Qed.
(* 
Local Lemma arrow_mor11_comp 
    {f g h : arrow C} 
    (γ : f --> g)
    (γ' : g --> h) :
  arrow_mor11 γ · arrow_mor11 γ' = arrow_mor11 (γ · γ').
Proof.
  reflexivity.
Qed. *)

Local Lemma colimIn11_Kcolim_colimL1_commutes
    {g : graph} {d : diagram g (arrow C)}
    {f : arrow C} {ccf : cocone d f}
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) 
    (v : vertex g)
    (iscodKfCC := L1_colim_L1_map_cod_Kf_is_colimCocone HK isclCC)
    (codKfCC := make_ColimCocone _ _ _ iscodKfCC) :
  colimIn codKfCC v · arrow_mor11 (Kcolim_colimL1_mor HK isclCC)
  = PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J (dob d v))
  · colimIn (CC _ (project_diagram11 (mapdiagram (fact_L F1) d))) v.
Proof.
  set (isHKCC := HK isclCC).
  set (HKCC := make_ColimCocone _ _ _ isHKCC).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          exact (arrow_mor11_eq (colimArrowCommutes HKCC _ _ v)).
  etrans. apply (colimArrowCommutes (CC _ (project_diagram11 (mapdiagram K d)))).
  reflexivity.
Qed.

Lemma L1_colim_L1_map_is_inverse_in_precat
    {g : graph} {d : diagram g (arrow C)} 
    {f : arrow C} {ccf : cocone d f} 
    (HK : preserves_colimit K _ _ ccf)
    (isclCC : isColimCocone d f ccf) :
  is_inverse_in_precat
    (colimArrow (arrow_colims CC _ (mapdiagram (fact_L F1) d)) _ (mapcocone (fact_L F1) d ccf))
    (L1_colim_L1_map HK isclCC).
Proof.
  set (isHKCC := HK isclCC).
  set (HKCC := make_ColimCocone _ _ _ isHKCC).
  
  set (isKfCC := L1_colim_L1_map_dom_Kf_is_colimCocone HK isclCC).
  set (KfCC := make_ColimCocone _ _ _ isKfCC).
  set (domfiscc := dom_colim_dom_L1_isColimCocone isclCC).
  set (domfcc := make_ColimCocone _ _ _ domfiscc).
  set (iscodKfCC := L1_colim_L1_map_cod_Kf_is_colimCocone HK isclCC).
  set (codKfCC := make_ColimCocone _ _ _ iscodKfCC).
  split.
  - apply pathsinv0.
    apply colim_endo_is_identity.
    intro v.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (colimArrowCommutes).
    use arrow_mor_eq.
    * exact (colimIn00_L1_colim_L1_commutes HK isclCC v).
    * use (MorphismsOutofPushoutEqual (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J (dob d v)))).
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (PushoutArrow_PushoutIn1).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply PushoutArrow_PushoutIn1.
        
        exact (colimIn11_Kcolim_colimL1_commutes HK isclCC v).
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (PushoutArrow_PushoutIn2).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply PushoutArrow_PushoutIn2.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                exact (colimIn00_L1_colim_L1_commutes HK isclCC v).
        etrans. apply (colimArrowCommutes (CC _ (project_diagram00 d))).
        reflexivity.
  - use arrow_mor_eq.
    * apply pathsinv0.
      use (colim_endo_is_identity _ domfcc).
      intro v.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (colimIn00_L1_colim_L1_commutes HK isclCC v).
      etrans. apply (colimArrowCommutes (CC _ (project_diagram00 (mapdiagram (fact_L F1) d)))).
      reflexivity.
    * use (MorphismsOutofPushoutEqual (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J f))).
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply PushoutArrow_PushoutIn1.
        apply pathsinv0.
        etrans. apply id_right.
        apply pathsinv0.
        
        use (colimArrowUnique' codKfCC).
        intro v.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                exact (colimIn11_Kcolim_colimL1_commutes HK isclCC v).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply (colimArrowCommutes (CC _ (project_diagram11 (mapdiagram (fact_L F1) d)))).
        etrans. apply PushoutArrow_PushoutIn1.
        reflexivity.
      + etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply PushoutArrow_PushoutIn2.
        apply pathsinv0.
        etrans. apply id_right.
        apply pathsinv0.
        use (colimArrowUnique' domfcc).
        intro v.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                etrans. apply assoc.
                apply cancel_postcomposition.
                exact (colimIn00_L1_colim_L1_commutes HK isclCC v).
        etrans. apply cancel_postcomposition.
                apply (colimArrowCommutes (CC _ (project_diagram00 d))).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply (colimArrowCommutes (CC _ (project_diagram11 (mapdiagram (fact_L F1) d)))).
        etrans. apply PushoutArrow_PushoutIn2.
        reflexivity.
Qed.

(* Main result *)
Lemma L1_preserves_colim_if_K_preserves_colim 
    {g : graph} {d : diagram g (arrow C)} 
    {f : arrow C} (ccf : cocone d f) :
  preserves_colimit K _ _ ccf
  -> preserves_colimit (fact_L F1) _ _ ccf.
Proof.
  intros HK isclCC.
  
  set (isHKCC := HK isclCC).
  set (HKCC := make_ColimCocone _ _ _ isHKCC).
  
  use (is_z_iso_isColim _ (arrow_colims CC _ (mapdiagram (fact_L F1) d))).
  exists (L1_colim_L1_map HK isclCC).
  exact (L1_colim_L1_map_is_inverse_in_precat HK isclCC).
Defined.

(* applying the main result *)
Lemma L1_small_if_K_small :
  preserves_colimits_of_shape K nat_graph
  -> preserves_colimits_of_shape (fact_L F1) nat_graph.
Proof.
  intro HK.
  intros d cl cc.
  apply L1_preserves_colim_if_K_preserves_colim.
  apply HK.
Qed.

End OSCSmall.