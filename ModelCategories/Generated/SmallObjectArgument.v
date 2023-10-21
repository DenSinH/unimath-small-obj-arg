
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
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import CategoryTheory.Chains.Chains.

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.NWFS.

Require Import CategoryTheory.ModelCategories.Generated.LiftingWithClass.
Require Import CategoryTheory.ModelCategories.Generated.OneStepMonad.
Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoid.
Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoidSequence.
Require Import CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.
Require Import CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSCocomplete.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSClosed.


Local Open Scope Cat.
Local Open Scope cat.


Section SmallObjectArgument.


Local Ltac functorial_factorization_eq f := (
  apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|];
  use funextsec;
  intro f;
  use subtypePath; [intro; apply isapropdirprod; apply homset_property|]
).

Context {C : category}.
Context {J : morphism_class C}.
Context (CC : Colims C).

Local Definition CCoproducts :
  ∏ g, Coproducts (morcls_lp J g) C.
Proof.
  intro g.
  apply Coproducts_from_Colims.
  intro d.
  exact (CC _ d).
Defined.

Local Definition CCoequalizers :
  Coequalizers C := (Coequalizers_from_Colims _ CC).

Local Definition CPushouts : Pushouts C.
Proof.
  apply Pushouts_from_Coequalizers_BinCoproducts.
  - apply BinCoproducts_from_Colims.
    intro d.
    exact (CC _ d).
  - intros H z f g.
    set (coeq := CCoequalizers _ _ f g).
    use tpair.
    * exists (CoequalizerObject _ coeq).
      exact (CoequalizerArrow _ coeq).
    * exists (CoequalizerArrowEq _ coeq).
      intros w h Hw.
      use unique_exists.
      + exact (CoequalizerOut _ coeq _ h Hw).
      + exact (CoequalizerArrowComm _ coeq _ h Hw).
      + intro y; apply homset_property.
      + intros y Hy.
        exact (CoequalizerOutUnique _ _ _ _ _ _ Hy).
Defined.

Definition one_step_comonad_as_LNWFS : total_category (LNWFS C).
Proof.
  exists (one_step_factorization J CCoproducts CPushouts).
  exact (one_step_comonad J CCoproducts CPushouts).
Defined.

Definition LNWFS_pointed (L : total_category (LNWFS C)) :
    pointed (@LNWFS_tot_monoidal C) :=
  (_,, LNWFS_tot_l_point L).

Local Definition Ff_mon : monoidal_cat :=
  (_,, @Ff_monoidal C).
Local Definition LNWFS_mon : monoidal_cat :=
  (_,, @LNWFS_tot_monoidal C).

(* Local Definition LNWFS_project_isColimCocone
    {d : chain LNWFS_mon}
    {cl : LNWFS_mon}
    {cc : cocone d cl}
    (clisCC : isColimCocone d cl cc) 
    (dbase := mapdiagram (pr1_category _) d) :
  isColimCocone dbase (pr1 cl) (project_cocone d cl cc).
Proof.
  intros cl' cc'.
Defined. *)

Import BifunctorNotations.
Import MonoidalNotations.

Lemma eq_section_nat_trans_component 
    {F F' : Ff C} 
    {γ γ' : F --> F'}
    (H : γ = γ') : 
  ∏ f, section_nat_trans γ f = section_nat_trans γ' f.
Proof.
  now induction H.
Qed.

Lemma eq_section_nat_trans_component11
    {F F' : Ff C} 
    {γ γ' : F --> F'}
    (H : γ = γ') : 
  ∏ f, three_mor11 (section_nat_trans γ f) = three_mor11 (section_nat_trans γ' f).
Proof.
  now induction H.
Qed.

Lemma eq_section_nat_trans_comp_component11
    {F F' F'' : Ff C} 
    {γ : F --> F''}
    {γ' : F --> F'}
    {γ'' : F' --> F''}
    (H : γ' · γ'' = γ) : 
  ∏ f, 
    three_mor11 (section_nat_trans γ' f) 
    · three_mor11 (section_nat_trans γ'' f) 
    = three_mor11 (section_nat_trans γ f).
Proof.
  induction H.
Admitted.

Lemma Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim 
    (L : total_category (LNWFS C))
    (d : chain LNWFS_mon)
    (CL := ChainsLNWFS CC d)
    (dbase := mapdiagram (pr1_category _) d) :
  isColimCocone 
    (mapdiagram (monoidal_left_tensor (pr1 L : Ff_mon)) dbase)
    ((pr1 L) ⊗_{Ff_mon} (pr1 (colim CL))) 
    (mapcocone (monoidal_left_tensor (pr1 L : Ff_mon)) _ (project_cocone _ _ (colimCocone CL))) 
    -> 
    isColimCocone 
      (mapdiagram (monoidal_left_tensor (L : LNWFS_mon)) d)
      (L ⊗_{LNWFS_mon} (colim CL)) 
      (mapcocone (monoidal_left_tensor (L : LNWFS_mon)) _ (colimCocone CL)).
Proof.
  intro HF.

  set (HFCC := make_ColimCocone _ _ _ HF).
  set (Ldbase := (mapdiagram (monoidal_left_tensor (pr1 L : Ff_mon)) dbase)).
  set (FfCCbase := ChainsFf CC CC Ldbase).
  set (base_mor := isColim_is_z_iso _ FfCCbase _ _ HF).
  set (base_inv := (colimArrow FfCCbase _ (colimCocone HFCC))).
  set (LNWFSCC := ChainsLNWFS CC (mapdiagram (monoidal_left_tensor (L : LNWFS_mon)) d)).

  use (is_z_iso_isColim _ LNWFSCC).
  use tpair.
  - exists (pr1 base_mor).
    split; intro f.
    * use arrow_mor_eq; [reflexivity|].
      
      set (inv11 := three_mor11 (section_nat_trans base_inv f)).
      use (pre_comp_with_z_iso_is_inj (f := inv11)).
      admit.
      admit.

      use colimArrowUnique'.
      intro v.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply colimArrowCommutes.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
      {
        set (test := LNWFSCocomplete.cocone_pointwise Ldbase (colim HFCC) (colimCocone HFCC) f).
        set (t := colimArrowCommutes HFCC _ (colimCocone FfCCbase) v).
        set (tf := eq_section_nat_trans_comp_component11 t f).
        exact tf.
      }
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
        set (cc := (mapcocone (monoidal_left_tensor (L : LNWFS_mon)) _ (colimCocone CL))).
        set (test := coconeIn cc v).
        set (ax := pr12 test f).
        set (ax11 := arrow_mor11_eq ax).
        exact ax11.
      }

      etrans. apply assoc'.
      apply pathsinv0.
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply pathsinv0.
      etrans. 
      {
        (* try to commute the middle 2 morphisms 
           (think about whiskercommutes)
           then compose first and last 2 
           (think about bifunctor_leftcomp / rightcomp)
           then rewrite commutativity on either

           we have:
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
        set (test := colimArrowCommutes HFCC _ (colimCocone FfCCbase) v).
        set (t := eq_section_nat_trans_comp_component11 test f).

      }

      (* 
        colimIn v at L∞, then 
      *)
      etrans. apply assoc.
      etrans. apply assoc4.
      etrans. apply cancel_postcomposition, cancel_precomposition.
      {
        
      }
      unfold lnwfs_mor.
      etrans. apply assoc'.
      unfold lnwfs_mor.
      apply cancel_precomposition.

      etrans. apply assoc'.
      etrans. apply cancel_postcomposition.
              cbn.
              reflexivity.
      apply pathsinv0.
      etrans. apply cancel_postcomposition.
              cbn.

      admit.
    * use arrow_mor_eq; [apply id_left|].
      
      set (inv11 := three_mor11 (section_nat_trans base_inv f)).
      use (pre_comp_with_z_iso_is_inj (f := inv11)).
      admit.
      admit.
      use colimArrowUnique'.
      intro v.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply colimArrowCommutes.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
      {
        set (test := LNWFSCocomplete.cocone_pointwise Ldbase (colim HFCC) (colimCocone HFCC) f).
        set (t := colimArrowCommutes HFCC _ (colimCocone FfCCbase) v).
        set (tf := eq_section_nat_trans_comp_component11 t f).
        exact tf.
      }
      etrans. apply colimArrowCommutes.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply colimArrowCommutes.
      etrans. 
      {
        etrans. apply cancel_precomposition.
                cbn.
                reflexivity.
        set (test := section_nat_trans (colimIn HFCC v) f).
        set (t := pr2 (three_mor_comm test)).
        exact (pathsinv0 t).
      }
      apply id_right.





  intros cl' cc'.
  



  assert (
    base_lnwfs_ax : 
    lnwfs_mor_axioms 
      (pr2 L L⊗ ColimLNWFS_disp CC d is_connected_nat_graph 0)
      (pr2 cl') 
      base_mor
  ).
  {
    split; intro f.
    * use arrow_mor_eq.
      + etrans. apply id_left.
        apply pathsinv0.
        etrans. apply id_left.
        etrans. apply id_left.
        exact (pathsinv0 (lnwfs_Σ_top_map_id (pr2 cl') f)).
      + show_id_type.
        cbn in TYPE.
        unfold three_ob1 in TYPE.
        cbn in TYPE.
        
        etrans. cbn.
        reflexivity.
        set (test := ChainsFf CC CC (mapdiagram (monoidal_left_tensor (pr1 L : Ff_mon)) dbase)).
        set (t := isColim_is_z_iso _ test _ _ (pr2 HFCC)).
        set (abc := colimArrow test _ (pr21 HFCC)).
        set (x := pr1 (pr1 abc f)).
        use (pre_comp_with_z_iso_is_inj (f := x)).
        {
          set (invabc := (pr11 t) f).
          exact (pr1 invabc).
        }
        {
          admit.
        }
        use colimArrowUnique'.
        intro v.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (colimArrowCommutes).
        (* etrans. apply cancel_postcomposition.
                apply pr1_transportf_const. *)
        (* etrans. apply assoc'.
        etrans. apply id_left. *)
        etrans. 
        {
          (* clear TYPE.
          show_id_type.
          cbn in TYPE. *)
          (* cbn. *)
          etrans. apply assoc.
          apply cancel_postcomposition.
          set (uvw := colimArrowCommutes HFCC _ cc'base v).
          set (uvwf := eq_section_nat_trans_comp_component11 uvw f).
          exact uvwf.
        }
        
        etrans.
        {
          set (abcd := coconeIn cc' v).
          set (axabcd := base_paths _ _ ((pr12 abcd) f)).
          set (testabcd := μ (lnwfs_L_monad (pr2 cl')) f
          · lnwfs_mor (pr2 (dob (mapdiagram (monoidal_left_tensor (L : LNWFS_mon)) d) v))
              (pr2 cl') (pr1 abcd) f).
          exact (pr2 (pathsdirprodweq axabcd)).
        }


        apply pathsinv0.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply (colimArrowCommutes).
        etrans. apply cancel_postcomposition.
                apply pr1_transportf_const.
        etrans. apply cancel_postcomposition.
                apply id_left.

        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
        {
          etrans. apply assoc.
          etrans. apply cancel_postcomposition.
          (*
            have #L(colimIn f) · arrow_mor11 (L (base_mor f))
          *)
          cbn.
          set (mor := (three_mor_mor12
          (section_nat_trans_data
             (LNWFSCocomplete.colim_nat_trans_in_data (v0 := 0) (v := v) CC
                (mapdiagram (pr1_category (LNWFS C)) d) is_connected_nat_graph)
             f))).
          set (comm := fiber_paths (nat_trans_ax (pr12 L) _ _ (mor))).
          (* todo: FROM HERE
                   FROM HERE
                   FROM HERE
                   FROM HERE
             write three_mor_eq11 function, need equality of middle morphisms above^
             maybe we should not do assoc and cancel_postcomposition.
          *)
        }


        etrans. apply cancel_postcomposition.
                apply pr1_transportf_const.
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
        {
          cbn.
          unfold arrow_mor11.
          cbn.
        }
        cbn in x.
        set ()

        apply pathsinv0.
        

        set (base_mor_comm := three_mor_comm (section_nat_trans (pr11 base_mor) f)).
        cbn in base_mor_comm.
        apply pathsinv0.
        (* etrans. apply cancel_postcomposition.
                cbn.
                reflexivity. *)
        
        set (base_nat := nat_trans_ax (section_nat_trans (pr11 base_mor)) _ _ (pr12 cl' f)).
        set (base_nat11 := (base_paths _ _ base_nat)).


        etrans. apply assoc.
        unfold three_mor01 in base_mor_comm.
        cbn in base_mor_comm.
        (* etrans. set (test := pr2 base_mor_comm). *)
                (* cbn in test. *)
                (* set (t := pathsinv0 test). *)
                (* simpl in t. *)
                (* exact t. *)
          (* exact (pathsinv0 (pr2 base_mor_comm)). *)
        admit.
    * use arrow_mor_eq; [apply id_left|].
      set (base_mor_comm := three_mor_comm (section_nat_trans (pr11 base_mor) f)).
      etrans. exact (pathsinv0 (pr2 base_mor_comm)).
      apply id_right.
  }

  use unique_exists.
  - exists (pr11 base_mor).
    exact (base_lnwfs_ax).
  - intro v.
    apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    exact (pr21 base_mor v).
  - intro y; apply impred; intro; apply homset_property.
  - intros y ccy.
    apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    use (base_paths _ _ (pr2 base_mor (pr1 y,, _))).
    intro v.
    exact (base_paths _ _ (ccy v)).
Admitted.

Lemma osc_preserves_diagram_on :
  T_preserves_diagram_on  _
    (LNWFS_pointed one_step_comonad_as_LNWFS) 
    (ChainsLNWFS CC)
    (CoequalizersLNWFS CC)
    (monoidal_unit LNWFS_tot_monoidal).
Proof.
  intros CC' cl' cc'.

  set (L1 := LNWFS_pointed one_step_comonad_as_LNWFS).
  set (d := (free_monoid_coeq_sequence_diagram_on 
    LNWFS_tot_monoidal 
    L1 
    (CoequalizersLNWFS CC)
    (monoidal_unit LNWFS_tot_monoidal)
  )).
  set (CL := ChainsLNWFS CC d).
  set (dbase := mapdiagram (pr1_category _) d).

  (* required assertion *)
  assert (HFf : isColimCocone 
    (mapdiagram (monoidal_left_tensor (pr11 L1 : Ff_mon)) dbase)
    ((pr11 L1) ⊗_{Ff_mon} (pr1 (colim CL))) 
    (mapcocone (monoidal_left_tensor (pr11 L1 : Ff_mon)) _ (project_cocone _ _ (colimCocone CL)))).
  {
    admit.
  }

  apply (
    Ff_lt_preserves_colim_impl_LNWFS_lt_preserves_colim
        L1 d HFf cl' cc'
  ).
Admitted.

Lemma free_monoid_coeq_sequence_converges_for_osc :
  free_monoid_coeq_sequence_converges_on _
    (LNWFS_pointed one_step_comonad_as_LNWFS) 
    (ChainsLNWFS CC)
    (CoequalizersLNWFS CC)
    (monoidal_unit LNWFS_tot_monoidal).
Proof.
  apply T_preserves_diagram_impl_convergence_on.
  exact osc_preserves_diagram_on.
Qed.

Theorem small_object_argument :
    total_category (NWFS C).
Proof.
  set (lnwfs_monoid := 
    Tinf_monoid 
      (@LNWFS_tot_monoidal C)
      (LNWFS_pointed one_step_comonad_as_LNWFS)
      (ChainsLNWFS CC)
      (CoequalizersLNWFS CC)
      free_monoid_coeq_sequence_converges_for_osc
      (LNWFS_rt_coeq CC)
      (LNWFS_rt_chain CC)
  ).

  use tpair; [|exact (LNWFS_tot_monoid_is_NWFS lnwfs_monoid)].
Defined.

End SmallObjectArgument.