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

Require Import CategoryTheory.Chains.Chains.

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.

Require Import CategoryTheory.ModelCategories.Generated.GenericFreeMonoid.

Local Open Scope Cat.
Local Open Scope cat.

(*
  Inspired by lecture notes by Egbert Rijke linked at
  https://ncatlab.org/nlab/show/sequential+limit, then
  just removed it when I saw what was already in UniMath *)

(* Definition increasing_cat_sequence (C : category) : UU :=
    ∑ (ob : nat -> C), ∏ (n : nat), ob n --> ob (n + 1). *)
(* this definition is the same as chain C. *)

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

Definition next_pair_diagram (xβ : pair_diagram) : pair_diagram.
Proof.
  destruct xβ as [Xβ [Xβ1 xβ]].
  (* Part of the sequence that we are considering:
    TXβ-1 --> TXβ ----> TXβ1
      |        |         |
      |     xβ |         | xβ1
      v        v         v
      Xβ ----> Xβ1 ----> Xβ2
          fβ
  *)
  (* the next "left object" is Xβ1 *)
  exists Xβ1.

  set (TXβ := T ⊗_{V} Xβ).
  set (TXβ1 := T ⊗_{V} Xβ1).

  set (Tt := (ruinv_{V} T) · T ⊗^{V}_{l} (pointed_pt _ T)).
                (* T --> T ⊗_{V} T). *)
  set (TtXβ := Tt ⊗^{V}_{r} Xβ).
                (* T ⊗_{V} Xβ --> (T ⊗_{V} T) ⊗_{V} Xβ). *)
  set (tT := (luinv_{V} T) · (pointed_pt _ T) ⊗^{V}_{r} T). 
                (* T --> T ⊗_{V} T). *)
  set (tTXβ := tT ⊗^{V}_{r} Xβ).
                (* T ⊗_{V} Xβ --> (T ⊗_{V} T) ⊗_{V} Xβ). *)
  set (Txβ := T ⊗^{V}_{l} xβ).
                (* T ⊗_{V} (T ⊗_{V} Xβ) --> T ⊗_{V} Xβ1). *)
  (* 
  We define xβ1: TXβ1 ---> Xβ2 by the coequalizer of the two
  composites
      tT        Txβ
  TXβ ===> T2 Xβ --> TXβ1
      Tt
  *)
  set (αTxβ := α_{V} _ _ _ · Txβ).
  set (coeq := CE _ _ (tTXβ · αTxβ) (TtXβ · αTxβ)).
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
    assert (Hlob : pair_diagram_lob (seq (S m)) = pair_diagram_lob (seq n)).
    {
      now rewrite H.
    }
    exact ((pair_diagram_horizontal_arrow (seq m)) · (idtoiso Hlob)).
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

Definition chain_shift_left (c : chain C) : chain C.
Proof.
  use tpair.
  - intro n. exact (dob c (S n)).
  - intros m n e.
    use (dmor c).
    abstract (now rewrite <- e).
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

Definition colimσ_on (A : C) : 
    colim (free_monoid_coeq_sequence_leftwhisker_colim_on T A) --> 
      colim (CL (chain_shift_left (free_monoid_coeq_sequence_diagram_on A))).
Proof.
  use colimOfArrows.
  - intro n.
    (* cbn. *)
    set (σα := pair_diagram_arr (free_monoid_coeq_sequence_on A n)).
    exact σα.
  - intros m n e.
  simpl.
    (* cbn. *)
    (* cbn. *)
    (* unfold monoidal_cat_tensor_mor. *)
    (* cbn. *)
    etrans. do 2 apply cancel_postcomposition.
            apply (bifunctor_rightid V).
    etrans. apply cancel_postcomposition, id_left.
    rewrite <- e.
    etrans. apply cancel_postcomposition.
            apply maponpaths.
            apply id_right.
    simpl.
    unfold pair_diagram_horizontal_arrow.
    unfold next_pair_diagram.
    admit.
Admitted. (* annoying, maybe not trivial *)

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
  
  rewrite <- e.
  (* cbn. *)
  etrans. apply cancel_postcomposition.
          apply id_right.
  set (colimA := free_monoid_coeq_sequence_colim_on A).
  
  apply pathsinv0.
  etrans. exact (pathsinv0 (colimInCommutes colimA _ _ e)).
  (* cbn. *)
  rewrite <- e.
  (* cbn. *)
  apply cancel_postcomposition.
  apply id_right.
Qed.

Definition free_monoid_coeq_sequence_limit_ordinal_step_on (A : C) : 
    pair_diagram.
Proof.
  exists (colim (free_monoid_coeq_sequence_colim_on A)).

  transparent assert (can : (colim (free_monoid_coeq_sequence_leftwhisker_colim_on T A) --> T ⊗_{V} colim (free_monoid_coeq_sequence_colim_on A))).
  {
    use colimArrow.
    use tpair.
    - intro n.
      (* cbn. *)
      set (arr := colimIn (free_monoid_coeq_sequence_colim_on A) n).
      exact (T ⊗^{V}_{l} arr).
    - exact (can_colimArrow_forms_cocone A).
  }

  transparent assert (top : (colim (free_monoid_coeq_sequence_leftwhisker_colim_on T A) --> T ⊗_{V} colim (free_monoid_coeq_sequence_colim_on A))).
  {
    apply (compose (colimσ_on A)).
    apply (compose (z_iso_inv (chain_shift_left_colim_iso _))).
    apply (compose (luinv_{V} _)).
    exact ((pointed_pt _ T) ⊗^{V}_{r} _).
  }

  set (coeq := CE _ _ can top).
  exists (CoequalizerObject _ coeq).
  exact (CoequalizerArrow _ coeq).
Defined.

Definition free_monoid_coeq_sequence_converges_on (A : C) :=
    is_z_isomorphism (
      pair_diagram_horizontal_arrow 
        (free_monoid_coeq_sequence_limit_ordinal_step_on A)
    ).

Lemma free_monoid_coeq_sequence_converges_gives_adjoint_mon_alg 
    (Hconv: free_monoid_coeq_sequence_converges_on I_{V}) :
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

Definition free_monoid_coeq_sequence_converges_gives_adjoint_unit_data 
    (Hconv : free_monoid_coeq_sequence_converges_on I_{V}) :
  nat_trans_data (functor_identity _)
                 (Mon_alg_right_action _
                     (free_monoid_coeq_sequence_converges_gives_adjoint_mon_alg Hconv)
                   ∙ Mon_alg_forgetful_functor _ T).
Proof.
  intro A.
  (* cbn. *)
  exact ((luinv_{V} A) · (pointed_pt _ Tinf) ⊗^{V}_{r} A).
Defined.

Definition free_monoid_coeq_sequence_converges_gives_adjoint_unit_axioms
    (Hconv : free_monoid_coeq_sequence_converges_on I_{V}) :
  is_nat_trans _ _ 
    (free_monoid_coeq_sequence_converges_gives_adjoint_unit_data Hconv).
Proof.
  intros A B f.

  (* cbn.
  unfold free_monoid_coeq_sequence_converges_gives_adjoint_unit_data.
  cbn. *)
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
          apply (pathsinv0 (monoidal_leftunitorinvnat V _ _ f)).
  
  etrans. apply assoc'.
  apply pathsinv0.
  etrans. apply assoc'.
  apply cancel_precomposition.
  
  use whiskerscommutes.
  exact (bifunctor_equalwhiskers V).
Qed.

Definition right_tensor_preserves_colimits :=
    ∏ (A : CMon), is_omega_cocont (monoidal_right_tensor A).

Definition free_monoid_coeq_sequence_converges_gives_adjoint_counit_data 
    (Hconv : free_monoid_coeq_sequence_converges_on I_{V})
    (rt_cocont : right_tensor_preserves_colimits) :
  nat_trans_data (Mon_alg_forgetful_functor _ T
                  ∙ Mon_alg_right_action _
                      (free_monoid_coeq_sequence_converges_gives_adjoint_mon_alg Hconv))
                 (functor_identity _).
Proof.
  intro A.
  destruct A as [A a].
  set (test := rt_cocont A
          _ _ _ 
          (isColimCocone_from_ColimCocone (free_monoid_coeq_sequence_colim_on I_{V}))).
  unfold isColimCocone in test.
  cbn.
  assert (cocone
          (mapdiagram (monoidal_right_tensor (A : CMon))
            (free_monoid_coeq_sequence_diagram_on I_{ V})) A).
  {
    use tpair.
    - intro n.
      cbn.
      unfold monoidal_cat_tensor_pt.
      cbn.
  }
  set (t := test A).
  
Defined.


Definition free_monoid_coeq_sequence_converges_gives_adjoint_unit 
    (Hconv : free_monoid_coeq_sequence_converges_on I_{V}) : nat_trans _ _ :=
  (_,, free_monoid_coeq_sequence_converges_gives_adjoint_unit_axioms Hconv).

Lemma free_monoid_coeq_sequence_converges_gives_adjoint
    (rt_cocont : right_tensor_preserves_colimits) :
  free_monoid_coeq_sequence_converges_on I_{V}
    -> ∑ (X : Mon_alg _ T), alg_forgetful_functor_right_action_is_adjoint _ X.
Proof.
  intro Hconv.
  exists (free_monoid_coeq_sequence_converges_gives_adjoint_mon_alg Hconv).
  (* rt_cocont gives us the (natural) isomorphisms *)
  use tpair.
  - split.
    * exact (free_monoid_coeq_sequence_converges_gives_adjoint_unit Hconv).
    * 
Qed.

(* using Proposition 23 in Garner, 2007 (long), can construct
   free monoid from T-Mod that is left adjoint to forgetful functor.
   
   using Proposition*)


(* 
The rest of the construction:
  - Want to create "T-module on A", in our case, we only care if
    A = I (= id_C), since that is the sequence we are going to use
    with R1.
    This can be done with Proposition 27 in Garner, 2007 (long).
    However, we need to construct a map T □ T∞ --> T∞. In 
    Proposition 27, we assume that the module sequence rewri
    for some α (as we assume the limit ordinal is α-small).
    I guess in our case, this would boil down to only having a 
    finite number of steps? As ω is not ω-small.
    Garner gives the construction of the required map as 
               θα       Xαα+^{-1}
      T ⊗ Xα ----> Xα+ ---------> Xα
    Where I am assuming the first map is one of the two branches
    for the equalizer in the successor ordinal case, and the second
    map exists because the sequence rewri. Just using the 
    colimits as they are in UniMath would give me T∞, but then I 
    cannot use it as if it was an element in this sequence so to say...

    One thing I thought might be possible, but is not what we want to do,
    is that for any β : ℕ, we have this cocone
          Xβ ---> Xβ+1
          |  \     / |
          |   \   /  |
          |    T∞    |
           \    |   /
             \  |  /
               Xβ+1
    which we can apply T to, to obtain a transformation
    T □ T∞ --> T □ Xβ+1
    which we can compose with xβ+1 and the inclusion of Xβ+2 into
    T∞ to obtain a map, but this would factor though a chosen
    Xβ, which seems odd, and not what we want.

    He constructs the universal map from A (so I) to T∞ as X0α,
    which is just the inclusion into the colimit, so that is 
    easy to define.
  - I'm guessing the next step is using Proposition 24, which says
    that if the sequence on I (which is precisely the one we want) exists,
    and we have some condition on the module action, then
    we get an adjoint to the forgetful functor T-alg --> [C, C],
    which I think gives us the fact that T∞-Alg = T-Alg?
    
  - Then the last step is giving the multiplication on (T∞, τ∞).
    This should follow from the proof of Proposition 23, where we 
    get a unit (which I guess should be the same as the one
    we would find from the first point, the universal map from 
    A (so I) to T∞).
    
    The multiplication comes from the adjunction, 
    in combination with the action ⋆ described
    before. To define this action, I may need to first add some 
    more tools to work with whiskering. I can see how (X, x) ⋆ X
    would give the map for the multiplication, and I guess the
    adjunction gives us functorality of the map, but I am not 
    entirely sure why the adjunction even works:

    For (X, x) the free T-monoid over I (which is actually the one we
    want), we define [C, C] --> T-Alg as (X, x) ⋆ (-): A ↦ (X ⊗ A, x ⊗ A)
    Applying the forgetful functor would yield X ⊗ A, which is not the same
    as A, unless X = I, which is not the case, since X would be T∞ in
    our case. Okay, maybe these objects are isomorphic, but why?

  Like before with Garner's construction, using this construction
  may be too "generic" again. It seems like
  in our specific case, with our specific ω-sequence, we
  might be able to construct the unit and multiplication
  on T∞ more directly, and show that the Algebra's are preserved.
  I guess we'd still need to use the idea of the adjunction we obtain,
  but thinking about it, I don't really see how we would obtain the
  map T∞ ⊗ T∞ --> T∞...

*)


(* todo: up to iso? *)
Definition preserves_chains (A : C) :=
    colim (free_monoid_coeq_sequence_colim_on A) = 
      Tinf ⊗_{V} A.


End free_monoid_colim.

(* Kelly: chapte 23, see prop 23.2 *)