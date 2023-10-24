(* Can be found on nlab:
    https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras
Or in G. M. Kelly. A unified treatment of transfinite constructions for free algebras, free
monoids, colimits, associated sheaves
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import CategoryTheory.Chains.Chains.

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.

Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoid.
Require Import CategoryTheory.ModelCategories.Generated.MonoidalHelpers.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.

Local Open Scope Cat.
Local Open Scope cat.


Section free_monoid_colim.

Import BifunctorNotations.
Import MonoidalNotations.

(* We will end up requiring that C is cocomplete anyway *)
Context {C : category}.
Context (V : monoidal C).
Local Definition CMon : monoidal_cat := (_,, V).
Context (T : pointed V).

Context (CL : Chains C).
Context (CE : Coequalizers C).

(* the horizontal map can be constructed from the vertical map:
              TXβ
                |
                | xβ
                v
  Xβ --------> Xβ1
     τXβ · xβ
  where τ is the unit of our pointed endofunctor (T, τ).
*)
Local Definition pair_diagram : UU :=
    ∑ (x0 x1 : C), (T ⊗_{V} x0 --> x1).

Local Definition pair_diagram_lob (X : pair_diagram) : C :=
    pr1 X.
Local Definition pair_diagram_rob (X : pair_diagram) : C :=
    pr12 X.
Coercion pair_diagram_arr (X : pair_diagram) :=
    pr22 X.

Local Definition pair_diagram_horizontal_arrow (X : pair_diagram) : (pair_diagram_lob X) --> (pair_diagram_rob X).
Proof.
  destruct X as [Xβ [Xβ1 xβ]].
  (* cbn. *)
  set (τX := (luinv_{V} Xβ) · (pointed_pt _ T) ⊗^{V}_{r} Xβ : Xβ --> T ⊗_{V} Xβ).
  exact (τX · xβ).
Defined.


Definition next_pair_diagram_coeq_arr0 (xβ : pair_diagram) : 
    T ⊗_{V} (pair_diagram_lob xβ) --> 
        T ⊗_{V} (pair_diagram_rob xβ).
Proof.
  (* destruct xβ as [Xβ [Xβ1 xβ]]. *)
  apply (compose (pair_diagram_arr xβ)).
  exact ((luinv_{V} _) · (pointed_pt _ T) ⊗^{V}_{r} _).
Defined.

Definition next_pair_diagram_coeq_arr1 (xβ : pair_diagram) : 
    T ⊗_{V} (pair_diagram_lob xβ) --> 
        T ⊗_{V} (pair_diagram_rob xβ).
Proof.
  (* destruct xβ as [Xβ [Xβ1 xβ]]. *)
  exact (T ⊗^{V}_{l} (pair_diagram_horizontal_arrow xβ)).
Defined.

Definition next_pair_diagram_coeq (xβ : pair_diagram) := 
    CE _ _ (next_pair_diagram_coeq_arr0 xβ) (next_pair_diagram_coeq_arr1 xβ).

Definition next_pair_diagram (xβ : pair_diagram) : pair_diagram.
Proof.
  (* Part of the sequence that we are considering:
    TXβ-1 --> TXβ ----> TXβ1
      |        |         |
      |     xβ |         | xβ1
      v        v         v
      Xβ ----> Xβ1 ----> Xβ2
          fβ
  *)
  (* the next "left object" is Xβ1 *)
  exists (pair_diagram_rob xβ).

  set (coeq := next_pair_diagram_coeq xβ).
  set (Xβ2 := CoequalizerObject _ coeq).
  exists Xβ2.

  set (xβ1 := CoequalizerArrow _ coeq).
  exact xβ1.
Defined.

Definition free_monoid_coeq_sequence_on (A : C) :
    nat -> pair_diagram.
Proof.
  intro n.
  induction n as [|β xβ].
  - exists A, (T ⊗_{V} A).
    exact (identity _).
    (* initial arrow is I ⟹ T *)
  - exact (next_pair_diagram xβ).
Defined.

Definition free_monoid_coeq_sequence_diagram_on (A : C) :
    chain C.
Proof.
  set (seq := free_monoid_coeq_sequence_on A).
  use tpair.
  - intro n.
    exact (pair_diagram_lob (seq n)).
  - simpl.
    intros m n H.
    induction H.
    exact ((pair_diagram_horizontal_arrow (seq m))).
Defined.

Definition rightwhisker_chain_with (P : CMon) (d : chain C) :
    chain C := mapchain (monoidal_right_tensor P) d.
Definition leftwhisker_chain_with (P : CMon) (d : chain C) :
    chain C := mapchain (monoidal_left_tensor P) d.

Definition free_monoid_coeq_sequence_colim_on (A : C) : 
  ColimCocone (free_monoid_coeq_sequence_diagram_on A) :=
    CL _.
    
Local Definition free_monoid_coeq_sequence_colim_unit := 
    free_monoid_coeq_sequence_colim_on I_{V}.
Local Definition Tinf : pointed V.
Proof.
  exists (colim free_monoid_coeq_sequence_colim_unit).
  exact (colimIn free_monoid_coeq_sequence_colim_unit 0).
Defined.

Definition free_monoid_coeq_sequence_leftwhisker_colim_on (P A : C) :
    ColimCocone (leftwhisker_chain_with P (free_monoid_coeq_sequence_diagram_on A)) :=
        CL _.
Definition free_monoid_coeq_sequence_rightwhisker_colim_on (P A : C) :
    ColimCocone (rightwhisker_chain_with P (free_monoid_coeq_sequence_diagram_on A)) :=
        CL _.

Definition chain_shift_left (c : chain C) : chain C.
Proof.
  use tpair.
  - intro n. exact (dob c (S n)).
  - intros m n e.
    use (dmor c).
    (* do NOT abstract this, otherwise the recursion will not
       resolve. *)
    now rewrite <- e.
Defined.

Definition chain_shift_left_base_cocone (c : chain C)
    (clmsh := colim (CL (chain_shift_left c))) :
  cocone c clmsh.
Proof.
  use make_cocone.
  - intro v.
    (* induction v.
    * exact ((dmor c (idpath _)) · (colimIn (CL (chain_shift_left c)) 0)).
    * exact (colimIn (CL (chain_shift_left c)) v). *)
    exact ((dmor c (idpath _)) · (colimIn (CL (chain_shift_left c)) v)).
  - abstract (
      intros u v e;
      etrans; [|
        apply cancel_precomposition;
        exact (colimInCommutes (CL (chain_shift_left c)) _ _ e)
      ];
      etrans; [apply assoc|];
      apply pathsinv0;
      etrans; [apply assoc|];
      apply cancel_postcomposition;
      rewrite <- e;
      apply cancel_precomposition;
      apply (maponpaths (dmor c));
      apply isasetnat
    ).
Defined.

Definition chain_shift_left_shl_cocone (c : chain C)
    (clm := colim (CL c)) :
  cocone (chain_shift_left c) clm.
Proof.
  use make_cocone.
  - intro v.
    apply (colimIn (CL c)).
  - abstract (
      intros u v e;
      apply (colimInCommutes _ (S u : vertex nat_graph) (S v))
    ).
Defined.

Definition chain_shift_left_fwd_cocone (c : chain C)
    {k : C} (cc : cocone c k) :
  cocone (chain_shift_left c) k.
Proof.
  use make_cocone.
  - intro v.
    exact (coconeIn cc (S v)).
  - abstract (
      intros u v e;
      apply (coconeInCommutes cc _ _ _)
    ).
Defined.

Definition chain_shift_left_inv_cocone (c : chain C)
    {k : C} (cc : cocone (chain_shift_left c) k) :
  cocone c k.
Proof.
  use make_cocone.
  - intro v.
    induction v.
    * apply (postcompose (coconeIn cc 0)).
      use (dmor c).
      reflexivity.
    * exact (coconeIn cc v).
  - abstract (
      intros u v e;
      induction u; [now rewrite <- e|];
      rewrite <- e;
      (* cbn. *)
      apply pathsinv0;
      etrans; [apply (pathsinv0 (coconeInCommutes cc _ _ (idpath (S u))))|];
      apply cancel_postcomposition;
      apply (maponpaths (dmor c));
      apply isasetnat
    ).
Defined.

Definition chain_shift_left_base_isColimCocone (c : chain C) :
    isColimCocone _ _ (chain_shift_left_base_cocone c).
Proof.
  set (clmsh := CL (chain_shift_left c)).
  intros cl cc.
  set (fwd_cocone := chain_shift_left_fwd_cocone _ cc).
  set (fwd_univProp := colimUnivProp clmsh cl fwd_cocone).
  destruct fwd_univProp as [mor uniqueness].
  use unique_exists.
  - exact (pr1 mor).
  - abstract (
      intro v;
      etrans; [apply assoc'|];
      etrans; [apply cancel_precomposition;
              exact (pr2 mor v)|];
      apply (coconeInCommutes cc)
    ).
  - abstract (
      intro; apply impred; intro; apply homset_property
    ).
  - abstract (
      intros y ccy;
      (* cbn. *)
      apply pathsinv0;
      etrans; [use (λ t, pathsinv0 (base_paths _ _ (uniqueness t)))|]; [
        exists y;
        intro v;
        apply pathsinv0;
        etrans; [exact (pathsinv0 (ccy (S v)))|];
        apply cancel_postcomposition;
        apply pathsinv0;
        etrans; [exact (pathsinv0 (colimInCommutes clmsh _ _ (idpath _)))|];
        apply cancel_postcomposition;
        apply (maponpaths (dmor c));
        apply isasetnat
      | reflexivity
      ] 
    ).
Qed.

Definition chain_shift_left_shl_colim_cocone (c : chain C)
    (clmsh := colim (CL (chain_shift_left c))) :
  ColimCocone c.
Proof.
  use (make_ColimCocone _ clmsh); [apply chain_shift_left_base_cocone|].
  exact (chain_shift_left_base_isColimCocone c).
Defined.

(* Definition chain_shift_left_colim_map (c : chain C) 
    (clm := colim (CL c))
    (clmls := colim (CL (chain_shift_left c))) :
  clm --> clmls.
Proof.
  (* unfold clm, clmls.
  cbn. *)
  use colimOfArrows.
  * intro n.
    use (dmor c).
    reflexivity.
  * intros m n e.
    (* cbn. *)
    rewrite <- e.
    apply cancel_precomposition.
    cbn.
    apply maponpaths.
    apply isasetnat.
Defined. *)

Definition chain_shift_left_colim_iso (c : chain C)
    (clm := colim (CL c))
    (clmls := colim (CL (chain_shift_left c))) :
  z_iso clm clmls.
Proof.
  exact (z_iso_from_colim_to_colim (CL c) (chain_shift_left_shl_colim_cocone c)).
Defined.

Lemma colimσ_on_welldefined 
    (A : C)
    (m : vertex nat_graph) :
  T ⊗^{ V}_{l} pair_diagram_horizontal_arrow (free_monoid_coeq_sequence_on A m)
  · next_pair_diagram (free_monoid_coeq_sequence_on A m) =
  free_monoid_coeq_sequence_on A m
  · pair_diagram_horizontal_arrow (next_pair_diagram (free_monoid_coeq_sequence_on A m)).
Proof.
  set (coeq := next_pair_diagram_coeq (free_monoid_coeq_sequence_on A m)).
  set (coeq_comm := CoequalizerArrowEq _ coeq).
  etrans. exact (pathsinv0 coeq_comm).

  apply pathsinv0.
  etrans. apply assoc.
  reflexivity.
Qed.

Definition colimσ_on (A : C) : 
    colim (free_monoid_coeq_sequence_leftwhisker_colim_on T A) -->
      colim (CL (chain_shift_left (free_monoid_coeq_sequence_diagram_on A))).
Proof.
  use colimOfArrows.
  - intro α.
    (* cbn. *)
    set (σα := free_monoid_coeq_sequence_on A α).
    exact σα.
  - abstract (
      intros m n e;
      etrans; [do 2 apply cancel_postcomposition;
              apply (bifunctor_rightid V)|];
      etrans; [apply cancel_postcomposition, id_left|];
      induction e;
      exact (colimσ_on_welldefined A m)
    ).
Defined.

(* canonical map 
(colim (free_monoid_coeq_sequence_leftwhisker_colim_on T A) --> T ⊗_{V} colim (free_monoid_coeq_sequence_colim_on A))
is well defined
i.e., map colim (T ⊗ X_α) --> T ⊗ colim X_α *)
Lemma can_colimArrow_forms_cocone (A : C) :
    forms_cocone
      (leftwhisker_chain_with T (free_monoid_coeq_sequence_diagram_on A))
      (λ n : nat, T ⊗^{ V}_{l} colimIn (free_monoid_coeq_sequence_colim_on A) n).
Proof.
  (* cbn. *)
  intros m n e.
  (* cbn.
  unfold monoidal_cat_tensor_mor.
  cbn.
  unfold functoronmorphisms1. *)
  etrans. do 2 apply cancel_postcomposition.
          apply (bifunctor_rightid V).
  etrans. apply cancel_postcomposition.
          apply id_left.
  etrans. apply (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
  apply maponpaths.
  set (colimA := free_monoid_coeq_sequence_colim_on A).
  
  apply pathsinv0.
  etrans. exact (pathsinv0 (colimInCommutes colimA _ _ e)).
  (* cbn. *)
  induction e.
  reflexivity.
Qed.

Local Definition can (A : C) :
    colim (free_monoid_coeq_sequence_leftwhisker_colim_on T A) --> T ⊗_{V} colim (free_monoid_coeq_sequence_colim_on A).
Proof.
  use colimArrow.
  use tpair.
  - intro n.
    (* cbn. *)
    set (arr := colimIn (free_monoid_coeq_sequence_colim_on A) n).
    exact (T ⊗^{V}_{l} arr).
  - exact (can_colimArrow_forms_cocone A).
Defined.

Local Definition top (A : C) :
    colim (free_monoid_coeq_sequence_leftwhisker_colim_on T A) --> T ⊗_{V} colim (free_monoid_coeq_sequence_colim_on A).
Proof.
  apply (compose (colimσ_on A)).
  apply (compose (z_iso_inv (chain_shift_left_colim_iso _))).
  apply (compose (luinv_{V} _)).
  exact ((pointed_pt _ T) ⊗^{V}_{r} _).
Defined.

Local Definition free_monoid_coeq_sequence_limit_step_coeq (A : C) :=
    CE _ _ (can A) (top A).

Definition free_monoid_coeq_sequence_limit_ordinal_step_on (A : C) : 
    pair_diagram.
Proof.
  exists (colim (free_monoid_coeq_sequence_colim_on A)).

  set (coeq := free_monoid_coeq_sequence_limit_step_coeq A).
  exists (CoequalizerObject _ coeq).
  exact (CoequalizerArrow _ coeq).
Defined.

Definition free_monoid_coeq_sequence_converges_on (A : C) :=
    is_z_isomorphism (
      pair_diagram_horizontal_arrow 
        (free_monoid_coeq_sequence_limit_ordinal_step_on A)
    ).

Section Convergence.

Definition T_preserves_diagram_on (A : C) : UU :=
  preserves_colimit 
    (monoidal_left_tensor (T : CMon)) 
    (free_monoid_coeq_sequence_diagram_on A)
    _ (colimCocone (free_monoid_coeq_sequence_colim_on A)).

Definition T_preserves_chains_impl_T_preserves_diagram_on (A : C) :
  preserves_colimits_of_shape
    (monoidal_left_tensor (T : CMon)) nat_graph
      -> T_preserves_diagram_on A.
Proof.
  intro H.
  intros CC cl cc.
  apply (
    H (free_monoid_coeq_sequence_diagram_on A) 
      _ _ (isColimCocone_from_ColimCocone (free_monoid_coeq_sequence_colim_on A))
  ).
Qed.

Context (A : C).
Context (HT : T_preserves_diagram_on A).

Local Definition HCC := HT (pr2 (free_monoid_coeq_sequence_colim_on A)).
Local Definition iso := 
    isColim_is_z_iso _
        (free_monoid_coeq_sequence_leftwhisker_colim_on T A)
        _ _ HCC.

Definition T_preserves_diagram_coeqout_arrow_on :
  T ⊗_{ V} colim (free_monoid_coeq_sequence_colim_on A) -->
    pair_diagram_lob (free_monoid_coeq_sequence_limit_ordinal_step_on A) :=
    (pr1 iso) · ((colimσ_on A) · (z_iso_inv (chain_shift_left_colim_iso _))).

Local Lemma chain_shift_left_colimIn_commutes 
  (u : vertex nat_graph) :
  colimIn (CL (chain_shift_left (free_monoid_coeq_sequence_diagram_on A))) u
  · colimArrow
      (chain_shift_left_shl_colim_cocone (free_monoid_coeq_sequence_diagram_on A))
      _ (colimCocone (free_monoid_coeq_sequence_colim_on A))
  = coconeIn (colimCocone (free_monoid_coeq_sequence_colim_on A)) (S u).
Proof.
  etrans. apply cancel_postcomposition.
          exact (pathsinv0 (colimInCommutes (CL (chain_shift_left (free_monoid_coeq_sequence_diagram_on A))) _ _ (idpath (S u)))).
  apply (colimArrowCommutes (chain_shift_left_shl_colim_cocone (free_monoid_coeq_sequence_diagram_on A)) _ _ (S u)).
Qed.

Local Lemma leftwhisker_colimIn_equals_on 
    (u : vertex nat_graph)
    (ltCC := (make_ColimCocone _ _ _ HCC)) :
  T ⊗^{ V}_{l} colimIn (free_monoid_coeq_sequence_colim_on A) u
  = colimIn (ltCC) u.
Proof.
  apply pathsinv0.
  etrans. apply cancel_postcomposition.
          apply (bifunctor_rightid V).
  apply id_left.
Qed.

Local Lemma TcolimIn_T_preserves_diagram_coeqout_arrow_on 
    (u : vertex nat_graph) :
  T ⊗^{ V}_{l} colimIn (free_monoid_coeq_sequence_colim_on A) u
  · T_preserves_diagram_coeqout_arrow_on
  = free_monoid_coeq_sequence_on A u
  · coconeIn (colimCocone (free_monoid_coeq_sequence_colim_on A)) (S u).
Proof.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
  {
    etrans. apply cancel_postcomposition.
            exact (leftwhisker_colimIn_equals_on u).
    apply (colimArrowCommutes (make_ColimCocone _ _ _ HCC)).
  }

  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (colimOfArrowsIn _ _ (free_monoid_coeq_sequence_leftwhisker_colim_on T A)).
  
  etrans. apply assoc'.
  apply cancel_precomposition.
  apply (chain_shift_left_colimIn_commutes).
Qed.

Lemma T_preserves_diagram_coeqout_arrow_on_is_coeqout :
    can A · T_preserves_diagram_coeqout_arrow_on =
    top A · T_preserves_diagram_coeqout_arrow_on.
Proof.
  use colimArrowUnique'.
  intro u.
  
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          use (colimArrowCommutes ((free_monoid_coeq_sequence_leftwhisker_colim_on T A))).
  etrans. exact (TcolimIn_T_preserves_diagram_coeqout_arrow_on u).

  apply pathsinv0.
  
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
  {
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimOfArrowsIn.
    etrans. apply assoc'.
    apply cancel_precomposition.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            exact (chain_shift_left_colimIn_commutes u).
    
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            exact (pathsinv0 (monoidal_leftunitorinvnat V _ _ _)).
    etrans. apply assoc'.
    apply cancel_precomposition.
    exact (pathsinv0 (whiskerscommutes V (bifunctor_equalwhiskers V) _ _)).
  }
  
  etrans. apply cancel_postcomposition.
          apply assoc.
  etrans. apply cancel_postcomposition.
          apply assoc.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (TcolimIn_T_preserves_diagram_coeqout_arrow_on (S u)).
  
  etrans. apply assoc'.
  etrans. apply assoc'.
  apply cancel_precomposition.
  etrans. apply assoc.
  etrans. apply assoc.
  exact ( colimInCommutes (free_monoid_coeq_sequence_colim_on A) _ _ (idpath (S (S u)))).
Qed.

Definition T_preserves_diagram_convergence_inv :
    pair_diagram_rob (free_monoid_coeq_sequence_limit_ordinal_step_on A)
    --> pair_diagram_lob (free_monoid_coeq_sequence_limit_ordinal_step_on A).
Proof.
  use CoequalizerOut.
  - exact T_preserves_diagram_coeqout_arrow_on.
  - exact T_preserves_diagram_coeqout_arrow_on_is_coeqout.
Defined.

Lemma T_preserves_diagram_convergence_inverse_in_precat :
  is_inverse_in_precat
    (pair_diagram_horizontal_arrow (free_monoid_coeq_sequence_limit_ordinal_step_on A))
  T_preserves_diagram_convergence_inv.
Proof.
  split.
  - apply pathsinv0.
    use colim_endo_is_identity.
    intro u.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply CoequalizerArrowComm.
    etrans. apply cancel_postcomposition.
    {
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (pathsinv0 (monoidal_leftunitorinvnat V _ _ _)).
      etrans. apply assoc'.
      apply cancel_precomposition.
      exact (pathsinv0 (whiskerscommutes V (bifunctor_equalwhiskers V) _ _)).
    }
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            exact (TcolimIn_T_preserves_diagram_coeqout_arrow_on u).
            
    etrans. apply assoc.
    exact (colimInCommutes (free_monoid_coeq_sequence_colim_on A) _ _ (idpath (S u))).
  - apply pathsinv0.
    use CoequalizerEndo_is_identity.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply CoequalizerArrowComm.

    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply assoc.
    etrans. apply cancel_precomposition.
    {
      etrans. apply cancel_postcomposition.
              apply assoc'.
      exact (pathsinv0 (CoequalizerArrowEq _ (free_monoid_coeq_sequence_limit_step_coeq A))).
    }
    apply (pre_comp_with_z_iso_is_inj iso).
    use colimArrowUnique'.
    intro u.
    (* revert iso *)
    etrans. apply cancel_precomposition.
    {
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (pr12 iso).
      apply id_left.
    }
    
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply colimArrowCommutes.
    (* cbn. *)
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (colimArrowCommutes (free_monoid_coeq_sequence_leftwhisker_colim_on T A)).
    etrans. apply assoc'.
    etrans. apply cancel_postcomposition.
            apply (bifunctor_rightid V).
    apply id_left.
Qed.

Lemma T_preserves_diagram_impl_convergence_on :
    free_monoid_coeq_sequence_converges_on A.
Proof.
  use make_is_z_isomorphism.
  - exact T_preserves_diagram_convergence_inv.
  - exact T_preserves_diagram_convergence_inverse_in_precat.
Qed.

End Convergence.

Section Monoid.

Context (Hconv: free_monoid_coeq_sequence_converges_on I_{V}).

Lemma free_monoid_coeq_sequence_converges_gives_adjoint_mon_alg  :
  Mon_alg _ T.
Proof.
  exists Tinf.
  use tpair.
  - set (limit_step := free_monoid_coeq_sequence_limit_ordinal_step_on I_{V}).
    set (σinfty := pair_diagram_arr limit_step).
    exact (σinfty · z_iso_inv_from_is_z_iso _ Hconv).
  - abstract (
      apply pathsinv0;
      use colim_endo_is_identity;
      intro n;
      (* cbn. *)
      
      apply pathsinv0;
      etrans; [exact (pathsinv0 (id_right _))|];
      apply cancel_precomposition;
      apply pathsinv0;
      (* cbn. *)
      
      etrans; [apply assoc|];
      exact (pr12 Hconv)
    ).
Defined.

Local Definition TinfM := free_monoid_coeq_sequence_converges_gives_adjoint_mon_alg.

Definition Tinf_pd_Tinf_map
    (n : nat)
    (p := free_monoid_coeq_sequence_on I_{V} n) :=
  ∑ (τn : pair_diagram_lob p ⊗_{V} Tinf --> Tinf) (τn1 : pair_diagram_rob p ⊗_{V} Tinf --> Tinf),
    (pair_diagram_arr p ⊗^{V}_{r} Tinf) · τn1 = α_{V} _ _ _ · (T ⊗^{V}_{l} τn) · (Mon_alg_map _ (pr2 TinfM)).


Lemma free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map_coeqout_rel
    (n : nat)
    (Hn : Tinf_pd_Tinf_map n)
    (Xn := free_monoid_coeq_sequence_on I_{V} n) :
  next_pair_diagram_coeq_arr0 (free_monoid_coeq_sequence_on I_{ V} n) ⊗^{ V}_{r} Tinf
  · (α_{ V } _ _ _
     · T ⊗^{ V}_{l} pr12 Hn · Mon_alg_map _ (pr2 TinfM)) =
  next_pair_diagram_coeq_arr1 (free_monoid_coeq_sequence_on I_{ V} n) ⊗^{ V}_{r} Tinf
  · (α_{ V } _ _ _
      · T ⊗^{ V}_{l} pr12 Hn · Mon_alg_map _ (pr2 TinfM)).
Proof.
  destruct Hn as [τn [τn1 τcomm]].
  apply pathsinv0.
  
  etrans. apply cancel_postcomposition.
          apply maponpaths.
          apply (bifunctor_leftcomp V).
  etrans. apply cancel_postcomposition.
          apply (bifunctor_rightcomp V).
  etrans. apply assoc.
  (* etrans. apply cancel_postcomposition, assoc. *)
  (* etrans. apply assoc'. *)
  etrans. apply assoc4.
  etrans. apply cancel_postcomposition, cancel_precomposition.
  {
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            exact (pathsinv0 (monoidal_associatornatleftright V _ _ _ _ _)).
    etrans. apply assoc'.
    apply cancel_precomposition.
    etrans. exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
    apply maponpaths.
    exact τcomm.
  }
  
  etrans. do 2 apply cancel_postcomposition.
  {
    etrans. apply maponpaths.
            apply (bifunctor_leftcomp V).
    apply (bifunctor_rightcomp V).
  }
  etrans. apply cancel_postcomposition, assoc.
  etrans. apply assoc'.
  etrans. apply assoc4.
  etrans. apply cancel_postcomposition, cancel_precomposition.
          apply (pathsinv0 (monoidal_associatornatleftright V _ _ _ _ _)).
  etrans. apply cancel_postcomposition, assoc.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
  {
    etrans. apply assoc.
    apply cancel_postcomposition.
    etrans. exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
    etrans. apply maponpaths.
    {
      etrans. apply assoc.
      apply cancel_postcomposition.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (pathsinv0 (monoidal_associatornatright V _ _ _ _ _)).
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply (whiskerscommutes V (bifunctor_equalwhiskers V)).
    }
    etrans. apply maponpaths.
    {
      etrans. apply cancel_postcomposition, assoc.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
      {
        etrans. exact (pathsinv0 (id_left _)).
        etrans. apply cancel_postcomposition.
                exact (pathsinv0 (pr1 (monoidal_leftunitorisolaw V _))).
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply assoc.
        etrans. apply cancel_precomposition.
                exact (pr22 TinfM).
        apply id_right.
      }
      etrans. apply assoc'.
      apply cancel_precomposition.
      apply (monoidal_leftunitornat V).
    }
    reflexivity.
  }
  etrans. apply cancel_postcomposition.
          exact (pathsinv0 (monoidal_associatornatleftright V _ _ _ _ _)).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
  {
    etrans. apply assoc.
    apply cancel_postcomposition.
    etrans. exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
    apply maponpaths.
    etrans. apply cancel_postcomposition.
            exact (pathsinv0 (monoidal_triangle_identity'_inv V _ _)).
    etrans. apply assoc.
    etrans. apply assoc4.
    etrans. apply cancel_postcomposition.
            etrans. apply cancel_precomposition.
                    apply (monoidal_associatorisolaw V).
            apply id_right.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (monoidal_leftunitorisolaw V).
    apply id_left.
  }
  etrans. apply assoc.
  etrans. exact (pathsinv0 τcomm).

  apply pathsinv0.
  etrans. apply cancel_postcomposition.
  {
    etrans. apply (bifunctor_rightcomp V).
    apply cancel_precomposition.
    apply (bifunctor_rightcomp V).
  }
  etrans. apply assoc'.
  apply cancel_precomposition.

  etrans. apply assoc.
  etrans. apply assoc4.
  etrans. apply cancel_postcomposition, cancel_precomposition.
  {
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (pathsinv0 (monoidal_associatornatright V _ _ _ _ _)).
    etrans. apply assoc'.
    apply cancel_precomposition.
    apply (whiskerscommutes V (bifunctor_equalwhiskers V)).
  }
          
  etrans. apply cancel_postcomposition, assoc.
  etrans. apply cancel_postcomposition, assoc.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
  {
    etrans. exact (pathsinv0 (id_left _)).
    etrans. apply cancel_postcomposition.
            exact (pathsinv0 (pr1 (monoidal_leftunitorisolaw V _))).
    etrans. apply assoc'.
    etrans. apply cancel_precomposition. 
    {
      etrans. apply assoc.
      exact (pr22 TinfM).
    }
    apply id_right.
  }
  etrans. do 3 apply cancel_postcomposition.
          exact (pathsinv0 (monoidal_triangle_identity'_inv V _ _)).
  etrans. apply cancel_postcomposition, assoc4.
  etrans. do 2 apply cancel_postcomposition.
          etrans. apply cancel_precomposition.
                  apply (monoidal_associatorisolaw V).
          apply id_right.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          apply (monoidal_leftunitornat V).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (monoidal_leftunitorisolaw V).
  apply id_left.
Qed.

Definition rt_coeq_coequalizer
    {A : C}
    (rt_coeq : preserves_colimits_of_shape 
          (monoidal_right_tensor (A : CMon)) Coequalizer_graph)
    {a b : C} {f g : a --> b}
    (coeq : Coequalizer _ f g) :
  Coequalizer _ (f ⊗^{V}_{r} A) (g ⊗^{V}_{r} A).
Proof.
  set (mapped_colimcocone := rt_coeq _ _ _ (isColimCocone_from_ColimCocone coeq)).

  use make_Coequalizer.
  - exact (CoequalizerObject _ coeq ⊗_{V} A).
  - exact (CoequalizerArrow _ coeq ⊗^{V}_{r} A).
  - abstract (
      etrans; [exact (pathsinv0 (bifunctor_rightcomp V _ _ _ _ _ _))|];
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_rightcomp V _ _ _ _ _ _))|];
      apply maponpaths;
      exact (pathsinv0 (CoequalizerArrowEq _ coeq))
    ).
  - use make_isCoequalizer.
    intros e h' H.
    transparent assert (cc : (cocone
            (mapdiagram (monoidal_right_tensor (A : CMon))
              (Coequalizer_diagram C f g)) e)).
    {
      use make_cocone.
      - use two_rec_dep.
        * exact ((f ⊗^{V}_{r} A) · h').
        * exact h'.
      - use two_rec_dep; use two_rec_dep.
        * exact (empty_rect _).
        * intro e'. induction e'.
          + etrans. apply assoc'.
            etrans. apply cancel_precomposition, cancel_postcomposition.
                    apply (bifunctor_leftid V).
            apply cancel_precomposition, id_left.
          + etrans. apply assoc'.
            etrans. apply cancel_precomposition, cancel_postcomposition.
                    apply (bifunctor_leftid V).
            etrans. apply cancel_precomposition, id_left.
            apply (! H).
        * exact (empty_rect _).
        * exact (empty_rect _).
    }

    destruct (mapped_colimcocone e cc) as [x uniqueness].
    use unique_exists.
    * exact (pr1 x).
    * abstract (
        etrans; [|exact (pr2 x (● 1)%stn)];
        apply pathsinv0;
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        etrans; [apply cancel_postcomposition;
                apply (bifunctor_leftid V)|];
        apply id_left
      ).
    * abstract (
        intro y; apply homset_property
      ).
    * abstract (
        intros y ccy;
        etrans; [use (λ t, base_paths _ _ (uniqueness (y,, t)))|]; [|reflexivity];
        use two_rec_dep; (
          etrans; [apply cancel_postcomposition;
                  etrans; [apply cancel_precomposition, (bifunctor_leftid V)|];
                  apply id_right|]
        ); [|exact ccy];
        apply pathsinv0;
        etrans; [apply cancel_precomposition;
                exact (pathsinv0 ccy)|];
        etrans; [apply assoc|];
        apply cancel_postcomposition;
        etrans; [exact (pathsinv0 (bifunctor_rightcomp V _ _ _ _ _ _))|];
        apply maponpaths;
        exact (coconeInCommutes (pr21 coeq) (stnpr 0) (stnpr 1) (inl tt))
      ).
Defined.

(* Definition lt_coeq_coequalizer
    {A : C}
    (lt_coeq : preserves_colimits_of_shape 
          (monoidal_left_tensor (A : CMon)) Coequalizer_graph)
    {a b : C} {f g : a --> b}
    (coeq : Coequalizer _ f g) :
  Coequalizer _ (A ⊗^{V}_{l} f) (A ⊗^{V}_{l} g).
Proof.
  set (mapped_colimcocone := lt_coeq _ _ _ (isColimCocone_from_ColimCocone coeq)).

  use make_Coequalizer.
  - exact (A ⊗_{V} CoequalizerObject _ coeq ).
  - exact (A ⊗^{V}_{l} CoequalizerArrow _ coeq).
  - abstract (
      etrans; [exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _))|];
      apply pathsinv0;
      etrans; [exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _))|];
      apply maponpaths;
      exact (pathsinv0 (CoequalizerArrowEq _ coeq))
    ).
  - use make_isCoequalizer.
    intros e h' H.
    transparent assert (cc : (cocone
            (mapdiagram (monoidal_left_tensor (A : CMon))
              (Coequalizer_diagram C f g)) e)).
    {
      use make_cocone.
      - use two_rec_dep.
        * exact ((A  ⊗^{V}_{l} f) · h').
        * exact h'.
      - use two_rec_dep; use two_rec_dep.
        * exact (empty_rect _).
        * intro e'. induction e'.
          + etrans. apply assoc'.
            etrans. apply cancel_postcomposition.
                    apply (bifunctor_rightid V).
            apply id_left.
          + etrans. apply assoc'.
            etrans. apply cancel_postcomposition.
                    apply (bifunctor_rightid V).
            etrans. apply id_left.
            apply (! H).
        * exact (empty_rect _).
        * exact (empty_rect _).
    }

    destruct (mapped_colimcocone e cc) as [x uniqueness].
    use unique_exists.
    * exact (pr1 x).
    * abstract (
        etrans; [|exact (pr2 x (● 1)%stn)];
        apply pathsinv0;
        etrans; [apply assoc'|];
        etrans; [apply cancel_postcomposition, (bifunctor_rightid V)|];
        apply id_left
      ).
    * abstract (
        intro y; apply homset_property
      ).
    * abstract (
        intros y ccy;
        etrans; [use (λ t, base_paths _ _ (uniqueness (y,, t)))|]; [|reflexivity];
        use two_rec_dep; (
          etrans; [apply cancel_postcomposition;
                  etrans; [apply cancel_postcomposition, (bifunctor_rightid V)|];
                  apply id_left|]
        ); [|exact ccy];
        apply pathsinv0;
        etrans; [apply cancel_precomposition;
                exact (pathsinv0 ccy)|];
        etrans; [apply assoc|];
        apply cancel_postcomposition;
        etrans; [exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _))|];
        apply maponpaths;
        exact (coconeInCommutes (pr21 coeq) (stnpr 0) (stnpr 1) (inl tt))
      ).
Defined. *)

Context (rt_coeq : rt_preserves_coequalizers V).

Definition free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map_coeqout
    (n : nat)
    (Hn : Tinf_pd_Tinf_map n) 
    (Xn1 := free_monoid_coeq_sequence_on I_{V} (S n)) :
  pair_diagram_rob Xn1 ⊗_{V} Tinf --> Tinf.
Proof.  
  set (τn1 := pr12 Hn).
  set (coeq := next_pair_diagram_coeq (free_monoid_coeq_sequence_on I_{V} n)).
  set (rt_coequalizer := rt_coeq_coequalizer (rt_coeq Tinf) coeq).
  use (CoequalizerOut _ rt_coequalizer).
  - exact (α_{V} _ _ _ · (T ⊗^{V}_{l} τn1) · Mon_alg_map _ (pr2 TinfM)).
  - exact (free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map_coeqout_rel n Hn).
Defined.

Definition free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map 
    (n : nat) :
  Tinf_pd_Tinf_map n.
Proof.
  induction n as [|n Hn].
  - exists (lu_{V} _).
    exists (ru_{V} T ⊗^{V}_{r} Tinf · Mon_alg_map _ (pr2 TinfM)).
    abstract (
      etrans; [apply cancel_postcomposition;
              apply (bifunctor_rightid V)|];
      etrans; [apply id_left|];
      apply pathsinv0;
      apply cancel_postcomposition;
      apply (monoidal_triangleidentity V)
    ).
  - set (τn1 := pr12 Hn).
    exists τn1.
    exists (free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map_coeqout n Hn).
    abstract (
      set (coeq := next_pair_diagram_coeq (free_monoid_coeq_sequence_on I_{V} n));
      set (rt_coequalizer := rt_coeq_coequalizer (rt_coeq Tinf) coeq);
      apply (CoequalizerArrowComm _ rt_coequalizer)
    ).
Defined.

Definition free_monoid_coeq_sequence_diagram_on_Tinf_Tinf_map
    (n : vertex nat_graph) : 
  dob (free_monoid_coeq_sequence_diagram_on I_{V}) n ⊗_{V} Tinf --> Tinf.
Proof.
  exact (pr1 (free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map n)).
Defined.

Lemma free_monoid_coeq_sequence_colim_on_Tinf_Tinf_map_formscocone
    (m : vertex nat_graph) :
  pair_diagram_horizontal_arrow (free_monoid_coeq_sequence_on I_{V} m) ⊗^{V}_{r} Tinf 
  · free_monoid_coeq_sequence_diagram_on_Tinf_Tinf_map (S m)
  = free_monoid_coeq_sequence_diagram_on_Tinf_Tinf_map m.
Proof.
  set (pdTinfmap_rel := pr22 (free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map m)).
  (* simpl in pdTinfmap_rel. *)
  simpl.
  etrans. apply cancel_postcomposition.
          apply (bifunctor_rightcomp V).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact pdTinfmap_rel.

  etrans. apply cancel_postcomposition.
          apply (bifunctor_rightcomp V).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition, assoc.
  etrans. apply assoc'.
  etrans. apply assoc4.
  etrans. apply cancel_postcomposition, cancel_precomposition.
          exact (pathsinv0 (monoidal_associatornatright V _ _ _ _ _)).
  etrans. apply cancel_postcomposition, assoc.
  etrans. apply assoc.
  etrans. apply assoc4.
  etrans. apply cancel_postcomposition, cancel_precomposition.
          apply (whiskerscommutes V (bifunctor_equalwhiskers V)).
  etrans. apply cancel_postcomposition, assoc.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
  {
    etrans. exact (pathsinv0 (id_left _)).
    etrans. apply cancel_postcomposition.
            exact (pathsinv0 (pr1 (monoidal_leftunitorisolaw V _))).
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            etrans. apply assoc.
            exact (pr22 TinfM).
    apply id_right.
  }
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          apply (monoidal_leftunitornat V).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
  {
    etrans. do 2 apply cancel_postcomposition.
            exact (pathsinv0 (monoidal_triangle_identity'_inv V _ _)).
    etrans. apply assoc4.
    etrans. apply cancel_postcomposition, cancel_precomposition.
            apply (monoidal_associatorisolaw V).
    etrans. apply cancel_postcomposition.
            apply id_right.
    apply (monoidal_leftunitorisolaw V).
  }
  apply id_left.
Qed.

(* We define the map from free_monoid_coeq_sequence_rightwhisker_colim_on, 
   i.e. from the chain on I_{V} rightwhiskered with T∞.
   It is possible, and in fact cleaner, to define a map
   colim (chain_on T∞) --> T∞,
   however, for this we need a morphism
   T∞ ⊗ T∞ --> colim (chain_on T∞),
   which is harder to define than 
   T∞ ⊗ T∞ --> colim ((chain_on I_{V}) ⊗ T∞),
   using the preservation of colimits of the right-
   whiskering functor. The two chains are in fact the same though,
   as they start with 
   I ⊗ T∞ --> T ⊗ T∞ --> ...
   and
   T∞ --> T ⊗ T∞ --> ...
   respectively.
   *)
Definition free_monoid_coeq_sequence_colim_on_Tinf_Tinf_map :
    colim (free_monoid_coeq_sequence_rightwhisker_colim_on Tinf I_{V}) --> Tinf.
Proof.
  use colimArrow.
  use tpair.
  - intro n.
    exact (free_monoid_coeq_sequence_diagram_on_Tinf_Tinf_map n).
  - abstract (
      intros m n e;
      induction e;
      etrans; [apply cancel_postcomposition, cancel_precomposition;
              apply (bifunctor_leftid V)|];
      etrans; [apply cancel_postcomposition, id_right|];
      exact (free_monoid_coeq_sequence_colim_on_Tinf_Tinf_map_formscocone m) 
    ).
Defined.

Context (rt_chain : rt_preserves_chains V).

Definition Tinf_monoid_mul_iso 
    (rt_colim := free_monoid_coeq_sequence_rightwhisker_colim_on Tinf I_{V}) :
  z_iso (colim (rt_colim)) (Tinf ⊗_{V} Tinf).
Proof.
  set (ccTinf := free_monoid_coeq_sequence_colim_on I_{V}).
  set (rt_ccTinf := rt_chain Tinf _ _ _ (isColimCocone_from_ColimCocone ccTinf)).
  set (iso := (_,, isColim_is_z_iso _ rt_colim _ _ rt_ccTinf) : z_iso _ _).
  exact iso.
Defined.

Definition Tinf_monoid_mul  :
  (Tinf ⊗_{V} Tinf) --> Tinf.
Proof.
  apply ((z_iso_inv Tinf_monoid_mul_iso) · free_monoid_coeq_sequence_colim_on_Tinf_Tinf_map).
Defined.

Definition Tinf_monoid_data :
    monoid_data V Tinf :=
  (Tinf_monoid_mul,, colimIn free_monoid_coeq_sequence_colim_unit 0).

Lemma Tinf_monoid_mul_iso_precomp_with_colimIn
    (v : vertex nat_graph) :
  colimIn free_monoid_coeq_sequence_colim_unit v ⊗^{V}_{r} Tinf
  · z_iso_inv Tinf_monoid_mul_iso
  = coconeIn (colimCocone (free_monoid_coeq_sequence_rightwhisker_colim_on Tinf I_{V})) v.
Proof.
  cbn.
  match goal with 
  |- _ · colimArrow ?CC_ _ _ = _ => set (CC := CC_)
  end.
  etrans; [|exact (colimArrowCommutes CC _ _ v)].
  apply cancel_postcomposition.
  apply pathsinv0.
  etrans. apply cancel_precomposition.
          apply (bifunctor_leftid V).
  apply id_right.
Qed.

Lemma Tinf_monoid_unit_left :
    monoid_laws_unit_left V Tinf_monoid_data.
Proof.
  etrans. apply assoc.
  apply (pre_comp_with_z_iso_is_inj (is_inverse_in_precat_inv (monoidal_leftunitorisolaw V _))).
  apply pathsinv0.
  etrans. exact (pr2 (monoidal_leftunitorisolaw V _)).
  use colim_endo_is_identity.
  intro v.
  etrans. do 2 apply cancel_precomposition.
          apply cancel_postcomposition.
          exact (Tinf_monoid_mul_iso_precomp_with_colimIn 0).

  etrans. do 2 apply cancel_precomposition.
  {
    set (CC := free_monoid_coeq_sequence_rightwhisker_colim_on Tinf I_{ V}).
    apply (colimArrowCommutes CC Tinf _ 0).
  }
  etrans. apply cancel_precomposition.
          apply (pr2 (monoidal_leftunitorisolaw V _)).
  apply id_right.
Qed.

Definition Tinf_rightwhisker_inclusion
    (v : vertex nat_graph) :
  dob (free_monoid_coeq_sequence_diagram_on I_{V}) v 
  --> dob (rightwhisker_chain_with Tinf (free_monoid_coeq_sequence_diagram_on I_{V})) v.
Proof.
  exact (ruinv_{V} _ · _ ⊗^{V}_{l} colimIn free_monoid_coeq_sequence_colim_unit 0).
Defined.

Lemma Tinf_rightwhisker_inclusion_commutes
    (v : vertex nat_graph) :
  Tinf_rightwhisker_inclusion v
  · dmor (free_monoid_coeq_sequence_diagram_on I_{ V}) (idpath (S v)) ⊗^{V}_{r} Tinf =
  dmor (free_monoid_coeq_sequence_diagram_on I_{V}) (idpath (S v))
  · Tinf_rightwhisker_inclusion (S v).
Proof. 
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (pathsinv0 (whiskerscommutes V (bifunctor_equalwhiskers V) _ _)).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (monoidal_rightunitorinvnat V).
  apply assoc'.
Qed.

Context (HT : T_preserves_diagram_on I_{V}).

Lemma Tinf_limit_step_colimIn_commutes
    (v : vertex nat_graph) :
  T ⊗^{ V}_{l} colimIn free_monoid_coeq_sequence_colim_unit (S v)
  · CoequalizerArrow C (free_monoid_coeq_sequence_limit_step_coeq I_{ V})
  = CoequalizerArrow C (next_pair_diagram_coeq (free_monoid_coeq_sequence_on I_{V} v))
  · colimIn free_monoid_coeq_sequence_colim_unit (S (S v))
  · pair_diagram_horizontal_arrow (free_monoid_coeq_sequence_limit_ordinal_step_on I_{V}).
Proof.
  show_id_type.
  set (coeq := free_monoid_coeq_sequence_limit_step_coeq I_{V}).
  set (limstepcomm := CoequalizerArrowEq _ coeq).
  set (TTinfin := colimIn (free_monoid_coeq_sequence_leftwhisker_colim_on T I_{ V}) (S v)).
  set (TTinfin_limstepcomm := cancel_precomposition _ _ _ _ _ _ TTinfin limstepcomm).
  use (pathscomp1 TTinfin_limstepcomm).
  - etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (colimArrowCommutes).
    reflexivity.
  - etrans. apply assoc.
    unfold top.
    etrans. apply cancel_postcomposition.
    {
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply (colimArrowCommutes).
      etrans. apply assoc'.
      apply cancel_precomposition.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply (chain_shift_left_colimIn_commutes).
      reflexivity.
    }
    cbn.
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    apply cancel_precomposition.
    apply pathsinv0.
    etrans. apply assoc'.
    reflexivity.
Qed.

Lemma Tinf_alg_map_commutes
    (v : vertex nat_graph) :
  T ⊗^{ V}_{l} colimIn free_monoid_coeq_sequence_colim_unit v · (Mon_alg_map _ (pr2 TinfM)) =
  free_monoid_coeq_sequence_on I_{ V} (v)
  · colimIn free_monoid_coeq_sequence_colim_unit (S v).
Proof.
  etrans. apply assoc.
  apply (post_comp_with_z_iso_is_inj (pr2 Hconv)).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (pr22 Hconv).
  etrans. apply id_right.
  
  apply pathsinv0.
  etrans. apply assoc.
  (* apply cancel_postcomposition. *)
  etrans. apply cancel_postcomposition.
  {
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            etrans. apply assoc.
            etrans. apply cancel_postcomposition.
                    exact (pathsinv0 (monoidal_leftunitorinvnat V _ _ _)).
            etrans. apply assoc'.
            apply cancel_precomposition.
            exact (pathsinv0 (whiskerscommutes V (bifunctor_equalwhiskers V) _ _)).
    etrans. apply assoc.
    apply assoc.
  }

  apply pathsinv0.
  etrans. apply cancel_postcomposition.
  {
    set (isHCC := HT (pr2 (free_monoid_coeq_sequence_colim_on I_{V}))).
    set (HCC := make_ColimCocone _ _ _ isHCC).
    etrans. 
    {
      etrans. exact (pathsinv0 (id_left _)).
      etrans. apply cancel_postcomposition.
              exact (pathsinv0 (bifunctor_rightid V _ _)).
      exact (pathsinv0 (colimInCommutes HCC _ _ (idpath (S v)))).
    }
    etrans. apply cancel_postcomposition.
    {
      etrans. apply cancel_postcomposition.
              apply (bifunctor_rightid V).
      apply id_left.
    }
    etrans. apply cancel_precomposition.
    {
      etrans. apply cancel_postcomposition.
              apply (bifunctor_rightid V).
      apply id_left.
    }
    reflexivity.
  }
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (Tinf_limit_step_colimIn_commutes v).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply assoc.
  apply pathsinv0.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          exact (Tinf_limit_step_colimIn_commutes v).
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply assoc.

  apply cancel_postcomposition.
  apply cancel_postcomposition.

  set (coeq := (next_pair_diagram_coeq (free_monoid_coeq_sequence_on I_{ V} v))).
  
  etrans. apply assoc'.
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          apply assoc.
  etrans. apply assoc.
  exact (CoequalizerArrowEq _ coeq).
Qed.


Lemma Tinf_monoid_unit_right_pointwise
    (v : vertex nat_graph) :
  ruinv^{ V }_{ pair_diagram_lob (free_monoid_coeq_sequence_on I_{ V} v)}
  · (pair_diagram_lob (free_monoid_coeq_sequence_on I_{ V} v)
    ⊗^{ V}_{l} colimIn free_monoid_coeq_sequence_colim_unit 0
    · free_monoid_coeq_sequence_diagram_on_Tinf_Tinf_map v) =
  colimIn free_monoid_coeq_sequence_colim_unit v.
Proof.
  (* Need to show that
                                   mon_map
    Xα+ --> Xα+ ⊗ I --> Xα+ ⊗ T∞ -------> T∞
                      =
    Xα+ ----------------------------------> T∞
                   colimIn
  *)
  induction v as [|v IHv].
  {
    etrans. apply cancel_precomposition.
            apply (monoidal_leftunitornat V).
    etrans. apply assoc.
    etrans. do 2 apply cancel_postcomposition.
            exact (pathsinv0 (unitorsinv_coincide_on_unit V)).
    etrans. apply cancel_postcomposition.
            apply (monoidal_leftunitorisolaw V).
    apply id_left.
  }
  induction v as [|v _].
  - etrans. apply cancel_precomposition.
    {
      etrans. apply assoc.
      apply cancel_postcomposition.
      exact (pathsinv0 (whiskerscommutes V (bifunctor_equalwhiskers V) _ _)).
    }
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            etrans. apply assoc.
            etrans. apply cancel_postcomposition.
                    etrans. apply (monoidal_rightunitorinvnat V).
                    exact (pr1 (monoidal_rightunitorisolaw V _)).
            apply id_left.
    etrans. exact (Tinf_alg_map_commutes 0).
    apply id_left.
  - set (Hn := free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map v).
    set (τn1 := pr12 Hn).
    set (coeq := next_pair_diagram_coeq (free_monoid_coeq_sequence_on I_{V} v)).
    set (coeqout := 
      pair_diagram_arr ((free_monoid_coeq_sequence_on I_{V} (S v))) 
      · colimIn free_monoid_coeq_sequence_colim_unit (S (S v))
    ).
    etrans. use (CoequalizerOutUnique _ coeq Tinf coeqout).
    * etrans. apply assoc.
      apply pathsinv0.
      etrans. apply assoc.
      apply cancel_postcomposition.
      exact (pathsinv0 (CoequalizerArrowEq _ coeq)).
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (pathsinv0 (monoidal_rightunitorinvnat V _ _ _)).
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              etrans. apply assoc.
              etrans. apply cancel_postcomposition.
                      apply (whiskerscommutes V (bifunctor_equalwhiskers V)).
              etrans. apply assoc'.
              apply cancel_precomposition.
              exact (pr22 (free_monoid_coeq_sequence_on_Tinf_pd_Tinf_map (S v))).
      
      etrans. apply cancel_precomposition.
              etrans. apply assoc.
              apply cancel_postcomposition.
              etrans. apply assoc.
              apply cancel_postcomposition.
              exact (pathsinv0 (monoidal_associatornatleft V _ _ _ _ _)).
      etrans. apply cancel_postcomposition.
              exact (pathsinv0 (monoidal_triangle_identity''_inv V _ _)).
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              etrans. apply assoc.
              apply cancel_postcomposition.
              etrans. apply assoc.
              apply cancel_postcomposition.
              etrans. apply assoc.
              etrans. apply cancel_postcomposition.
                      apply (monoidal_associatorisolaw V).
              apply id_left.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              etrans. apply cancel_precomposition.
                      exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
              etrans. exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
              apply maponpaths.
              exact IHv.
      exact (Tinf_alg_map_commutes (S v)).
    * apply pathsinv0.
      etrans; [use (CoequalizerOutUnique _ coeq Tinf coeqout)|]; [|reflexivity|reflexivity].
Qed.

Lemma Tinf_monoid_unit_right :
    monoid_laws_unit_right V Tinf_monoid_data.
Proof.
  etrans. apply assoc.
  apply (pre_comp_with_z_iso_is_inj (is_inverse_in_precat_inv (monoidal_rightunitorisolaw V _))).
  apply pathsinv0.
  etrans. exact (pr2 (monoidal_rightunitorisolaw V _)).
  use colim_endo_is_identity.
  intro v.

  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          exact (pathsinv0 (monoidal_rightunitorinvnat V _ _ _)).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
  {
    etrans. apply assoc.
            apply cancel_postcomposition.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (whiskerscommutes V (bifunctor_equalwhiskers V)).
    etrans. apply assoc'.
    apply cancel_precomposition.
    exact (Tinf_monoid_mul_iso_precomp_with_colimIn v).
  }
  
  (* cbn. *)
  etrans. apply cancel_precomposition.
          etrans. apply assoc'.
          apply cancel_precomposition.
  {
    set (CC := free_monoid_coeq_sequence_rightwhisker_colim_on Tinf I_{ V}).
    apply (colimArrowCommutes CC Tinf _ v).
  }
  exact (Tinf_monoid_unit_right_pointwise v).
Qed.

Lemma Tinf_monoid_assoc :
    monoid_laws_assoc V Tinf_monoid_data.
Proof.
  set (ccTinf := free_monoid_coeq_sequence_colim_on I_{V}).
  set (rt_ccTinf := rt_chain (Tinf ⊗_{V} Tinf) _ _ _ (isColimCocone_from_ColimCocone ccTinf)).
  set (rt_colim := free_monoid_coeq_sequence_rightwhisker_colim_on (Tinf ⊗_{V} Tinf) I_{V}).
  set (iso := (_,, isColim_is_z_iso _ rt_colim _ _ rt_ccTinf) : z_iso _ _).
  
  apply (pre_comp_with_z_iso_is_inj (is_inverse_in_precat_inv (monoidal_associatorisolaw V _ _ _))).
  apply (pre_comp_with_z_iso_is_inj iso).
  
  use colimArrowUnique'.
  intro v.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply colimArrowCommutes.
  etrans. apply cancel_precomposition.
  {
    etrans. apply assoc.
    apply cancel_postcomposition.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply (monoidal_associatorisolaw V).
    apply id_left.
  }
  etrans. apply cancel_postcomposition.
          etrans. apply cancel_precomposition.
                  apply (bifunctor_leftid V).
          apply id_right.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (whiskerscommutes V (bifunctor_equalwhiskers V)).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
          etrans. apply assoc.
          etrans. apply cancel_postcomposition.
                  exact (Tinf_monoid_mul_iso_precomp_with_colimIn v).
          apply (colimArrowCommutes ((free_monoid_coeq_sequence_rightwhisker_colim_on Tinf I_{ V}))).

  apply pathsinv0.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply colimArrowCommutes.
  etrans. apply cancel_postcomposition.
  etrans. apply cancel_precomposition.
          apply (bifunctor_leftid V).
  apply id_right.

  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (monoidal_associatorinvnatright V).
  etrans. apply assoc'.
  etrans. apply cancel_precomposition.
  {
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
    {
      etrans. exact (pathsinv0 (bifunctor_rightcomp V _ _ _ _ _ _)).
      apply maponpaths.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact (Tinf_monoid_mul_iso_precomp_with_colimIn v).
      
      apply (colimArrowCommutes ((free_monoid_coeq_sequence_rightwhisker_colim_on Tinf I_{ V}))).
    }
    reflexivity.
  }
  
  induction v.
  - cbn.
    admit.
  - cbn.
    admit.


  (* set (iso := Tinf_monoid_mul_iso).
  set (Tiso := is_z_iso_rightwhiskering_z_iso V Tinf _ (pr2 iso)).
  
  apply (pre_comp_with_z_iso_is_inj (pr2 Tiso)).
  show_id_type.
  cbn in TYPE.
  cbn in iso.
  set (test := pr1 iso).
  use (pre_comp_with_z_iso_is_inj (f := test))
  cbn in test.

  apply (pre_comp_with_z_iso_is_inj (pr22 iso)). *)
Admitted.

Definition Tinf_monoid_axioms :
    monoid_laws V Tinf_monoid_data :=
  (Tinf_monoid_unit_left,, Tinf_monoid_unit_right,, Tinf_monoid_assoc).

Definition Tinf_monoid : monoid V Tinf :=
    (_,, Tinf_monoid_axioms).

End Monoid.

End free_monoid_colim.

(* Check Tinf_monoid. *)