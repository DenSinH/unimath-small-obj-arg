Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.Retract.
Require Import CategoryTheory.ModelCategories.Lifting.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.NWFSisWFS.
Require Import CategoryTheory.ModelCategories.Generated.LiftingWithClass.

Require Import CategoryTheory.DisplayedCats.Examples.MonadAlgebras.
Require Import CategoryTheory.limits.coproducts.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.
Local Open Scope morcls.

Arguments CoproductArrow {_} {_} {_} _ {_}.
Arguments CoproductIn {_} {_} {_} _.
Arguments CoproductInCommutes {_} {_} {_} _ {_}.


(* We have to do this special stuff, because we come across
   a lot of equalities between coproduct inclusions, where
   the indexed objects are not the same (map, lifting problem map --> g)
   only because the lifting problems are not the same, the maps are
   in fact the same. 

   In fact, all the inclusions we do are based on the (co)domain of the
   map of the lifting problem, and entirely independent of the lifting
   problem itself. This means that indeed, the inclusions should just 
   be equal. 

   In theory though, in a general case, the inclusions would not be equal,
   and differ by some idtoiso (see CoproductIn_idtoiso), since the 
   objects that the inclusions originate from theoretically do not have
   to be the same.
*)
Lemma CoproductInLiftingProblemsEq 
    {C : category} {J : morphism_class C} {g : arrow C} 
    {a : total_category (morcls_disp J) -> C} {CCa : Coproduct _ _ (λ lp, a (morcls_lp_map lp))}
    {f : total_category (morcls_disp J)} {S S' : (pr1 f) --> g} :
    S = S' -> CoproductIn CCa (f,, S) = CoproductIn CCa (f,, S').
Proof.
  intro H.
  induction H.
  reflexivity.
Qed.

(* specialize domain / codomain cases *)
Lemma CoproductInLiftingProblemsEqDom 
    {C : category} {J : morphism_class C} {g : arrow C} 
    {CCa : Coproduct _ _ (λ lp, arrow_dom (pr1 (morcls_lp_map lp)))}
    {f : total_category (morcls_disp J)} {S S' : (pr1 f) --> g} :
    S = S' -> CoproductIn CCa (f,, S) = CoproductIn CCa (f,, S').
Proof.
  apply (CoproductInLiftingProblemsEq (a := λ f, arrow_dom (pr1 f))).
Qed.

Lemma CoproductInLiftingProblemsEqCod
    {C : category} {J : morphism_class C} {g : arrow C} 
    {CCa : Coproduct _ _ (λ lp, arrow_cod (pr1 (morcls_lp_map lp)))}
    {f : total_category (morcls_disp J)} {S S' : (pr1 f) --> g} :
    S = S' -> CoproductIn CCa (f,, S) = CoproductIn CCa (f,, S').
Proof.
  apply (CoproductInLiftingProblemsEq (a := λ f, arrow_cod (pr1 f))).
Qed.

(* first try basic apply / use, the more expensive match statement *)
Local Ltac morcls_lp_coproduct_in_eq := 
  apply (CoproductInLiftingProblemsEqCod) ||
  apply (CoproductInLiftingProblemsEqDom) ||
  use (CoproductInLiftingProblemsEqCod) ||
  use (CoproductInLiftingProblemsEqDom) ||
    match goal with 
    |- CoproductIn _ ?S = CoproductIn _ ?S'
      => apply (CoproductInLiftingProblemsEqCod (S:=pr2 S)) ||
         apply (CoproductInLiftingProblemsEqCod (S':=pr2 S')) ||
         apply (CoproductInLiftingProblemsEqDom (S:=pr2 S)) ||
         apply (CoproductInLiftingProblemsEqDom (S':=pr2 S'))
    end.

Section one_step_monad.

Context {C : category} (J : morphism_class C).
Context (CC : Colims C).

(* Garner 2008, section 5.2 (functor K) *)
Definition morcls_coprod_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - (* sending g to ∑_{x ∈ S_g} f_x*)
    intro g.
    exact (morcls_lp_coprod CC J g).
  - (* map γ: g --> g' gives map of lifting problems *)
    intros g g' γ.
    use mors_to_arrow_mor.
    * use CoproductOfArrowsInclusion.
      + (* inclusion of lifting problems S_g into S_g' with γ *)
        intro lpJg.
        destruct lpJg as [f S].  
        exists f.
        exact (S · γ).
      + (* map from lifting problem of S_g's left hand domain into that of S_g'
           The lifting problems have the same domain on the left, as f is the
           same. *)
        intro. exact (identity _).
    * use CoproductOfArrowsInclusion.
      + (* the same map here *)
        intro lpJg.
        destruct lpJg as [f S].  
        exists f.
        exact (S · γ).
      + intro. exact (identity _).
    * (* commutativity of coproduct arrow inclusion with
         ∑_{x∈S_g} f_x and ∑_{x∈S_g'} f_x *)
      abstract (
        (* simpl; *)
        (* unfold morcls_lp_coprod; *)
        (* simpl; *)
        etrans; [use CoproductOfArrowsInclusion_comp|];
        apply pathsinv0;
        etrans; [use CoproductOfArrowsInclusion_comp|];
        (* simpl; *)
        (* equality of coproduct of arrows *)
        apply maponpaths;
        apply funextsec;
        intro;
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply id_left|];
        reflexivity
      ).
Defined.

Definition morcls_coprod_functor_is_functor : is_functor morcls_coprod_functor_data.
Proof.
  split.
  - intro g.
    use arrow_mor_eq; apply pathsinv0, Coproduct_endo_is_identity; intro.
    * etrans.
      apply (CoproductOfArrowsInclusionIn _ (morcls_lp_dom_coprod CC J g)).
      (* simpl. *)
      etrans. apply id_left.
      (* unfold morcls_lp_dom_coprod. *)
      (* apply (CoproductInLiftingProblemsEqDom (S := pr2 i · _)). *)
      morcls_lp_coproduct_in_eq.
      etrans. apply id_right.
      reflexivity.
    * etrans.
      apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J g)).
      (* simpl. *)
      etrans. apply id_left.
      morcls_lp_coproduct_in_eq.
      (* apply (CoproductInLiftingProblemsEqCod (S := pr2 i · _)). *)
      apply id_right.
  - intros f g h S T.
    use arrow_mor_eq; apply pathsinv0.
    * etrans. use CoproductOfArrowsInclusion_comp.
      (* simpl. *)
      etrans. apply maponpaths.
              apply funextsec.
              intro.
              apply id_right.

      apply CoproductArrowUnique.
      intro.
      etrans. use (CoproductOfArrowsInclusionIn _ _ _ _ i).
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply id_left.
      (* apply (CoproductInLiftingProblemsEqDom (S := pr2 i · _)). *)
      morcls_lp_coproduct_in_eq.
      etrans. apply assoc.
      reflexivity.
    * etrans. use CoproductOfArrowsInclusion_comp.
      (* simpl. *)
      etrans. apply maponpaths.
              apply funextsec.
              intro.
              apply id_right.

      apply CoproductArrowUnique.
      intro.
      etrans. use (CoproductOfArrowsInclusionIn _ _ _ _ i).
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply id_left.
      morcls_lp_coproduct_in_eq.
      (* apply (CoproductInLiftingProblemsEqCod (S := pr2 i · _)). *)
      apply assoc.
Qed.

(* K in Garner *)
Definition morcls_coprod_functor : functor (arrow C) (arrow C) :=
    (_,, morcls_coprod_functor_is_functor).

Definition morcls_coprod_nat_trans_data : 
    nat_trans_data morcls_coprod_functor (functor_identity _).
Proof.
  intro g.
  exact (morcls_lp_coprod_diagram CC J g).
Defined.

Definition morcls_coprod_nat_trans_is_nat_trans : 
    is_nat_trans _ _ morcls_coprod_nat_trans_data.
Proof.
  intros g g' γ.
  use arrow_mor_eq.
  - etrans. use precompWithCoproductArrowInclusion.
    apply pathsinv0.
    etrans. apply postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply pathsinv0.
    apply id_left.
  - etrans. use precompWithCoproductArrowInclusion.
    apply pathsinv0.
    etrans. apply postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    apply pathsinv0.
    apply id_left.
Qed.

(* φ in Garner 2007, p23 *)
Definition morcls_coprod_nat_trans :
    nat_trans morcls_coprod_functor (functor_identity _) :=
  (_,, morcls_coprod_nat_trans_is_nat_trans).

Arguments CoproductObject {_} {_} {_}.
Lemma commuting_cube_construction {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod CC J _) 
          --> CoproductObject (morcls_lp_dom_coprod CC J _)}
    {bb : CoproductObject (morcls_lp_cod_coprod CC J g) 
          --> CoproductObject (morcls_lp_cod_coprod CC J g')}
    {cc : arrow_dom g --> arrow_dom g'}
    (leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g'))
    (topface  : arrow_mor00 (morcls_lp_coprod_diagram CC J g) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram CC J g')) :
  E1 CC J g --> E1 CC J g'.
Proof.
  (* The map induced by pushouts on the front and back face
     (only the front face is drawn)
          ∑h
      ∑A ------> C
       |\ aa       \  cc
  ∑f=Kg|  \     ∑h'  \
       |    ∑A' -----> C
       v    |
      ∑B    |Kg'       |
        \   |=     PO    λ1g'
      bb  \ v∑f'       v
           ∑B' - - - > E1g'
  *)
  set (CE1g' := cc · (λ1 CC J g')).
  set (BE1g' := bb · (PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J g'))).

  use (PushoutArrow 
       (morcls_lp_coprod_diagram_pushout CC J g)
       _ BE1g' CE1g').
  
  abstract (
    (* Left to show commutativity of (outer) pushout diagram *)
    (* Kg · (arrow_mor11 Kγ) · (PushoutIn1 g') = (PushoutIn g) · γ00 · λ1g *)
    (* unfold CE1g', BE1g'; *)
    etrans; [apply assoc|];

    (* first rewrite commutativity of left face *)
    etrans; [apply cancel_postcomposition; exact leftface|];
    etrans; [apply assoc'|];
    
    (* rewrite commutativity in top face *)
    apply pathsinv0;
    etrans; [apply assoc|];
    etrans; [apply cancel_postcomposition; exact topface|];

    (* cancel precomposition with aa: ∑A --> ∑A' arrow *)
    etrans; [apply assoc'|];
    apply cancel_precomposition;

    (* all that's left is commutativity in the pushout square of g' *)
    apply pathsinv0;
    exact (PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout CC J g'))
  ).
Defined.

Lemma commuting_cube_bottom_face {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod CC J g) 
          --> CoproductObject (morcls_lp_dom_coprod  CC J g')}
    {bb : CoproductObject (morcls_lp_cod_coprod  CC J g) 
          --> CoproductObject (morcls_lp_cod_coprod  CC J g')}
    {cc : arrow_dom g --> arrow_dom g'}
    {leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g')}
    {topface  : arrow_mor00 (morcls_lp_coprod_diagram  CC J g) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram  CC J g')} :
  PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J g) · commuting_cube_construction leftface topface =
  bb · PushoutIn1 (morcls_lp_coprod_diagram_pushout CC J g').
Proof.
  etrans. apply PushoutArrow_PushoutIn1.
  reflexivity.
Qed.

Lemma commuting_cube_right_face {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod CC J g) 
          --> CoproductObject (morcls_lp_dom_coprod CC J g')}
    {bb : CoproductObject (morcls_lp_cod_coprod CC J g) 
          --> CoproductObject (morcls_lp_cod_coprod CC J g')}
    {cc : arrow_dom g --> arrow_dom g'}
    {leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g')}
    {topface  : arrow_mor00 (morcls_lp_coprod_diagram CC J g) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram CC J g')} :
  cc · λ1 CC J g' =
  λ1 CC J g · commuting_cube_construction leftface topface.
Proof.
  apply pathsinv0.
  etrans. apply PushoutArrow_PushoutIn2.
  reflexivity.
Qed.

Lemma commuting_cube_construction_eq {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod CC J g) 
          --> CoproductObject (morcls_lp_dom_coprod CC J g')}
    {bb : CoproductObject (morcls_lp_cod_coprod CC J g) 
          --> CoproductObject (morcls_lp_cod_coprod CC J g')}
    {cc : arrow_dom g --> arrow_dom g'}
    {aa' : CoproductObject (morcls_lp_dom_coprod CC J g) 
           --> CoproductObject (morcls_lp_dom_coprod CC J g')}
    {bb' : CoproductObject (morcls_lp_cod_coprod CC J g) 
           --> CoproductObject (morcls_lp_cod_coprod CC J g')}
    {cc' : arrow_dom g --> arrow_dom g'}
    (leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g'))
    (topface  : arrow_mor00 (morcls_lp_coprod_diagram CC J g) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram CC J g'))
    (leftface' : (morcls_coprod_functor g) · bb' = aa' · (morcls_coprod_functor g'))
    (topface'  : arrow_mor00 (morcls_lp_coprod_diagram CC J g) · cc' = 
                 aa' · arrow_mor00 (morcls_lp_coprod_diagram CC J g')) :
  bb = bb' -> cc = cc' -> commuting_cube_construction leftface topface = commuting_cube_construction leftface' topface'.
Proof.
  intros Hb Hc.
  (* unfold commuting_cube_construction. *)
  use PushoutArrowUnique.
  - etrans. apply PushoutArrow_PushoutIn1.
    apply cancel_postcomposition.
    exact Hb.
  - etrans. apply PushoutArrow_PushoutIn2.
    apply cancel_postcomposition.
    exact Hc.
Qed.

(* one step comonad functor L1 sends g to λ1g *)
Definition one_step_comonad_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - intro g.
    exact (λ1 CC J g).
  - intros g g' γ.
    (* The map on morphisms becomes the right face from the cube induced by
          ∑h
      ∑A ------> C
       |\          \  γ00
  ∑f=Kg|  \     ∑h'  \
       |    ∑A' -----> C
       v Kγ |
      ∑B    |Kg'       |
        \   |=     PO    λ1g'
          \ v∑f'       v
           ∑B' - - - > E1g'
    *)
    (* the morphism E1g --> E1g' we will need arises from the pushout
         property with the following maps. *)
    set (Kγ := (#morcls_coprod_functor)%cat γ).
    set (φγ := nat_trans_ax morcls_coprod_nat_trans g g' γ).
    set (φγ00 := arrow_mor00_eq φγ).

    use mors_to_arrow_mor.
    * exact (arrow_mor00 γ).
    * use commuting_cube_construction.
      + exact (arrow_mor00 Kγ).
      + exact (arrow_mor11 Kγ).
      + exact (arrow_mor00 γ).
      + abstract (exact (pathsinv0 (arrow_mor_comm Kγ))).
      + abstract (exact (pathsinv0 φγ00)).
    * (* commutativity of right face *)
      (* γ00 · λ1g' = λ1g · ccc *)
      (* This follows simply from the properties of a pushout *)
      apply commuting_cube_right_face.
Defined.

Definition one_step_comonad_functor_is_functor : is_functor one_step_comonad_functor_data.
Proof.
  split.
  - intro g.
    use arrow_mor_eq.
    * (* top map is identity simply because it comes from a functor *)
      reflexivity.
    * (* bottom map is identity because the pushout arrow is unique *)
      apply pathsinv0, PushoutArrowUnique.
      + etrans. apply id_right.
        apply pathsinv0.
        etrans. apply cancel_postcomposition.
                apply maponpaths.
                apply functor_id.
        apply id_left.
      + etrans. apply id_right.
        apply pathsinv0.
        apply id_left.
  - intros f g h S T.
    use arrow_mor_eq.
    * reflexivity.
    * apply pathsinv0, PushoutArrowUnique.
      (* Gotta keep in mind that (# one_step_comonad_functor_data) S 
         is a PushoutArrow and we can then use pushout properties. *)
      + apply pathsinv0.
        etrans. apply cancel_postcomposition.
                apply maponpaths.
                apply functor_comp.
        apply pathsinv0.
        (* PushoutIn1 · (PushoutArrow · PushoutArrow) = arrow_mor11 · PushoutIn *)
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                use PushoutArrow_PushoutIn1.
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                use PushoutArrow_PushoutIn1.
        apply assoc.
      + (* PushoutIn2 (PushoutArrow · PushoutArrow) = arrow_mor00 (S T) · PushoutIn *)
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                use PushoutArrow_PushoutIn2.
        etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                use PushoutArrow_PushoutIn2.
        apply assoc.
Qed.

Definition one_step_comonad_functor : functor (arrow C) (arrow C) :=
    (_,, one_step_comonad_functor_is_functor).

Lemma one_step_comonad_ρ1_compat {g g' : arrow C} (γ : g --> g') :
    arrow_mor11 (#(one_step_comonad_functor) γ)%Cat · ρ1 CC J g' =
      ρ1 CC J g · arrow_mor11 γ.
Proof.
  use (MorphismsOutofPushoutEqual 
        (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J g))).
  - 
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use PushoutArrow_PushoutIn1.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            use PushoutArrow_PushoutIn1.
    etrans. apply precompWithCoproductArrowInclusion.
    
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn1. 
    etrans. apply postcompWithCoproductArrow.
    
    apply maponpaths.
    apply funextsec.
    intro.
    apply pathsinv0.
    apply id_left.
  - etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use PushoutArrow_PushoutIn2.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            use PushoutArrow_PushoutIn2.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn2. 

    apply pathsinv0.
    exact (arrow_mor_comm γ).
Qed.

Definition one_step_factorization_data : section_disp_data (three_disp C).
Proof.
  use tpair.
  - intro g.
    exists (E1 CC J g).
    exists (λ1 CC J g), (ρ1 CC J g).
    apply λ1_ρ1_compat.
  - intros g g' γ.
    (* cbn. *)
    set (L1γ := (#(one_step_comonad_functor) γ)%Cat).
    exists (arrow_mor11 L1γ).
    abstract (
      split; apply pathsinv0; [
        (* commutativity of λ1 and arrow_mor11 (#L1 γ) *)
        exact (arrow_mor_comm L1γ)
      | (* commutativity of ρ1 and arrow_mor11 (#L1 γ) = arrow_mor00 (#R1 γ) *)
        apply one_step_comonad_ρ1_compat
      ]
    ).
Defined.

Definition one_step_factorization_axioms : section_disp_axioms one_step_factorization_data.
Proof.
  (* these identities follow from the functorality of g -> λ1g (one_step_comonad_functor)
  *)
  
  split.
  - intro g.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    (* cbn. *)
    (* behavior of commuting cube construction on identity follows from
       identity axiom of the one_step_comonad_functor *)
    set (one_step_comonad_id := functor_id (one_step_comonad_functor) g).
    set (bottom := arrow_mor11_eq one_step_comonad_id).
    exact bottom.
  - intros g1 g2 g3 γ12 γ23.
    (* behavior of commuting cube construction on composition follows from
      identity axiom of the one_step_comonad_functor *)
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    set (one_step_comonad_comp := functor_comp (one_step_comonad_functor) γ12 γ23).
    set (bottom := arrow_mor11_eq one_step_comonad_comp).
    exact bottom.
Qed.

Definition one_step_factorization : functorial_factorization C :=
    (_,, one_step_factorization_axioms).

(* Lemma E1_compat (g : arrow C) : E1 CC J g = E1 J (opp_mor g) (CC _) POs.
Proof.
  reflexivity.
Qed.

Context (CCopp : ∏ (g : arrow (op_cat C)), Coproducts (morcls_lp (morphism_class_opp J) g) (op_cat C)) (POsopp : Pushouts (op_cat C)).

Lemma λ1_ρ1_opp_compat (g : arrow C) :
    arrow_cod (λ1 CC J g) = arrow_dom (ρ1 (morphism_class_opp J) (opp_arrow g) (CCopp _) POsopp).
Proof.
  cbn.
Defined. *)

Definition one_step_monad_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - intro g.
    exact (ρ1 CC J g).
  - intros g g' γ.
    
    use mors_to_arrow_mor.
    * exact (arrow_mor11 (#one_step_comonad_functor γ)%cat).
    * exact (arrow_mor11 γ).
    * exact (one_step_comonad_ρ1_compat _).
Defined.

Definition one_step_monad_functor_is_functor : is_functor one_step_monad_functor_data.
Proof.
  split.
  - intro g.
    use arrow_mor_eq.
    * (* bottom map is identity because the pushout arrow is unique *)
      apply pathsinv0, PushoutArrowUnique.
      + etrans. apply id_right.
        apply pathsinv0.
        etrans. apply cancel_postcomposition.
                apply maponpaths.
                apply functor_id.
        apply id_left.
      + etrans. apply id_right.
        apply pathsinv0.
        apply id_left.
    * (* bottom map is identity simply because it comes from a functor *)
      reflexivity.
  - intros f g h S T.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * etrans. apply maponpaths.
              apply (functor_comp one_step_comonad_functor).
      reflexivity.
    * reflexivity.
Qed.

Definition one_step_monad_functor : functor (arrow C) (arrow C) :=
    (_,, one_step_monad_functor_is_functor).

Definition one_step_comonad_counit_data : nat_trans_data (one_step_comonad_functor) (functor_identity _).
Proof.
  (* Send λ1 g --> g along
      C ====== C
      |        |
  λ1g |   L1   | g
      v        v
    E1g ----> D
          ρ1g
  *)
  intro g.
  use mors_to_arrow_mor.
  - exact (identity _).
  - exact (ρ1 CC J g).
  - abstract (exact (arrow_mor_comm (morcls_lp_coprod_diagram_red CC J g))).
Defined.

Definition one_step_comonad_counit_is_nat_trans : is_nat_trans _ _ one_step_comonad_counit_data.
Proof.
  intros g g' γ.
  use arrow_mor_eq.
  - etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
  - (* PushoutArrow (morcls_lp_coprod_diagram_pushout g (CC g) POs) ...
       · ρ1g' = ρ1g · γ11 *)
    (* We are trying to prove an equality of maps E1g --> arrow_cod g' *)
    use (MorphismsOutofPushoutEqual 
          (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J g))).
    * (* todo: this is a really common strategy, generalize this? *)
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              use PushoutArrow_PushoutIn1.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn1.

      (* simplify left hand side *)
      (* etrans. { simpl. reflexivity. } *)
      (* k_x · γ11 = arrow_mor11 (Kγ) · k_x' *) 
      (* this is just the commutativity of the bottom square of the
         commutative cube of φ *)
      set (φax := nat_trans_ax morcls_coprod_nat_trans g g' γ).
      set (bottom_square := arrow_mor11_eq φax).
      apply pathsinv0.
      exact (bottom_square).
    * 
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn2.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              use PushoutArrow_PushoutIn2.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn2.
              
      apply pathsinv0.
      exact (arrow_mor_comm γ).
Qed.

Definition one_step_comonad_counit : nat_trans (one_step_comonad_functor) (functor_identity _) :=
    (_,, one_step_comonad_counit_is_nat_trans).

Definition one_step_monad_unit_data : nat_trans_data (functor_identity _) (one_step_monad_functor).
Proof.
  (* Send g --> ρ1 g along
         λ1g
      C ----> E1g
      |        |
  g   |   R1   | ρ1g
      v        v
      D ====== D
  *)
  intro g.
  use mors_to_arrow_mor.
  - exact (λ1 CC J g).
  - exact (identity _). 
  - abstract (exact (arrow_mor_comm (morcls_lp_coprod_diagram_red_flipped CC J g))).
Defined.

Definition one_step_monad_unit_is_nat_trans : is_nat_trans _ _ one_step_monad_unit_data.
Proof.
  intros g g' γ.
  use arrow_mor_eq.
  - apply pathsinv0.
    apply PushoutArrow_PushoutIn2.
  - etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
Qed.

Definition one_step_monad_unit : nat_trans (functor_identity _) (one_step_monad_functor) :=
    (_,, one_step_monad_unit_is_nat_trans).

(* ψg in Garner *)
Definition morcls_lp_coprod_L1_inclusion (g : arrow C) :
    morcls_lp J g -> morcls_lp J (λ1 CC J g).
Proof.
  (* The inclusion of lifting problems is induced by
    S_g → S_{L1g} : x ↦ (f_x -- in_x -> Kg = ∑f -- ϵg -> L1g)
    where ϵg is morcls_lp_coprod_diagram_red:
              ∑h
    A ---> ∑A ---> C
    |      |       |
  f |    ∑f|       | λ1g
    v      v       v
    B ---> ∑B ---> E1g
    *)
  intro S.
  exists (pr1 S).
  (* right hand square *)
  set (rhs := PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout CC J g)).
  set (rhs_mor := mors_to_arrow_mor (morcls_lp_coprod CC J g) (λ1 CC J g) _ _ (pathsinv0 rhs)).
  use (λ inx, inx · rhs_mor).

  (* left hand square *)
  (* todo: generalize this *)
  use mors_to_arrow_mor.
  - exact (CoproductIn (morcls_lp_dom_coprod CC J g) S).
  - exact (CoproductIn (morcls_lp_cod_coprod CC J g) S).
  - abstract (exact (CoproductInCommutes _ _ S)).
Defined.

(* δg in Garner *)
Definition morcls_lp_coprod_L1_map (g : arrow C) :
    (morcls_lp_coprod CC J g) --> (morcls_lp_coprod CC J (λ1 CC J g)).
Proof.
  (* the inclusion of the objects are just identity on themselves *)
  use mors_to_arrow_mor;
    try exact (CoproductOfArrowsInclusion 
              (morcls_lp_coprod_L1_inclusion g) _ _ 
              (λ _, (identity _))).
  
  (* commutativity *)
  abstract (
    etrans; [use precompWithCoproductArrowInclusion|];
    (* simpl; *)
    apply pathsinv0;
    etrans; [use postcompWithCoproductArrow|];
    (* simpl; *)
    apply maponpaths;
    apply funextsec;
    intro S;
    apply pathsinv0;
    etrans; [apply id_left|];
    apply pathsinv0;
    etrans; [apply assoc'|];
    etrans; [apply cancel_precomposition; exact (CoproductOfArrowsInclusionIn _ _ _ _ S)|];
    etrans; [apply cancel_precomposition; apply id_left|];
    reflexivity
  ).
Defined.

Definition one_step_comonad_mul_data : 
    nat_trans_data
      (fact_L one_step_factorization)
      (functor_composite (fact_L one_step_factorization) (fact_L one_step_factorization)).
Proof.
  intro g.
  (* The map on morphisms becomes the right face from the cube induced by
          ∑h
      ∑A ------> C
       |\          =  
  ∑f=Kg|  \     ∑h'  =
       |    ∑A' -----> C
       v δg |
      ∑B    |Kλg       |
        \   |=     PO    λ1g
          \ v∑λg f     v
           ∑B  - - - > E1g
    *)
  set (δg := morcls_lp_coprod_L1_map g).
  
  use mors_to_arrow_mor.
  - exact (identity _).
  - use commuting_cube_construction.
    * (* aa *) exact (arrow_mor00 δg).
    * (* bb *) exact (arrow_mor11 δg).
    * (* cc *) exact (identity _).
    * (* left face *)
      exact (pathsinv0 (arrow_mor_comm δg)).
    * (* top face *)
      abstract (
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply precompWithCoproductArrowInclusion|];
        (* cbn. *)
        apply (maponpaths (CoproductArrow _));
        apply funextsec;
        intro S;
        etrans; [apply id_left|];
        exact (CoproductInCommutes _ _ S)
      ).
  - (* commutativity in right face *)
    use commuting_cube_right_face.
Defined.

Definition one_step_comonad_mul_is_nat_trans : is_nat_trans _ _ one_step_comonad_mul_data.
Proof.
  intros g g' γ.
  use arrow_mor_eq.
  - (* simpl. *)
    etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
  - (* equality of arrows E1 g --> E1 (λ1g) *)
    use (MorphismsOutofPushoutEqual 
      (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J g))).
    * 
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1. 
      etrans. apply assoc.

      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.

      apply cancel_postcomposition.
      (* cbn. *)
      etrans. use CoproductOfArrowsInclusion_comp.
      apply pathsinv0.
      etrans. use CoproductOfArrowsInclusion_comp.

      (* unfold CoproductOfArrowsInclusion. *)
      use CoproductArrowUnique.
      intro.
      (* simpl. *)
      etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod CC J g)).
      etrans. apply assoc'.
      do 2 (etrans; [apply id_left|]).
      apply pathsinv0.
      etrans. apply assoc'.
      do 2 (etrans; [apply id_left|]).

      morcls_lp_coproduct_in_eq.
      
      use arrow_mor_eq.
      + etrans. apply cancel_postcomposition.
                apply (CoproductInCommutes (morcls_lp_dom_coprod CC J g)).
        apply pathsinv0.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J g') _ (_,, _)).
        reflexivity.
      + etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply PushoutArrow_PushoutIn1.
                
        etrans. apply assoc.
        etrans. apply cancel_postcomposition.
                apply  (CoproductInCommutes (morcls_lp_cod_coprod CC J g)).
        etrans. apply assoc'.
        apply id_left.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              use PushoutArrow_PushoutIn2.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn2. 
              
      etrans. apply cancel_precomposition.
              apply id_left.
      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn2.
      etrans. etrans. apply assoc'.
              apply cancel_precomposition.
              apply PushoutArrow_PushoutIn2.
      apply id_left.
Qed.

Definition one_step_comonad_mul : 
    nat_trans 
      (fact_L one_step_factorization)
      (functor_composite (fact_L one_step_factorization) (fact_L one_step_factorization)) :=
  (_,, one_step_comonad_mul_is_nat_trans).

(* Definition one_step_comonad_functor_with_μ : functor_with_μ (op_cat (arrow C)) :=
    (functor_opp one_step_comonad_functor,, op_nt one_step_comonad_mul). *)

Definition one_step_comonad_data : Monad_data _ :=
    L_monad_data one_step_factorization one_step_comonad_mul.

Local Lemma one_step_comonad_assoc_law11 (g : arrow C) :
  arrow_mor11 (
    (# one_step_comonad_data)%Cat (μ one_step_comonad_data g)
    · μ one_step_comonad_data g
  ) =
  arrow_mor11 (
    μ one_step_comonad_data (one_step_comonad_data g)
    · μ one_step_comonad_data g
  ).
Proof.
  use (MorphismsOutofPushoutEqual (isPushout_Pushout (morcls_lp_coprod_diagram_pushout CC J g))).
  - etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use PushoutArrow_PushoutIn1.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply PushoutArrow_PushoutIn1.
    etrans. apply assoc.

    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn1.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply PushoutArrow_PushoutIn1.
    etrans. apply assoc.
    apply cancel_postcomposition.

    (* show_id_type. *)
    use CoproductArrow_eq'.
    intro S.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J g)).
    etrans. apply cancel_postcomposition.
            apply id_left.
    etrans. use (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (one_step_comonad_data g)) _ _ (morcls_lp_coprod_L1_inclusion g S)).
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            use (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J g)).
    etrans. apply assoc'.
    etrans. apply id_left.
    etrans. use (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J (one_step_comonad_data g)) _ _ (morcls_lp_coprod_L1_inclusion g S)).
    etrans. apply id_left.
    morcls_lp_coproduct_in_eq.
    use arrow_mor_eq.
    * etrans. apply id_right.
      etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J g)).
      apply pathsinv0.
      etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J (λ1 CC J g)) _ (morcls_lp_coprod_L1_inclusion g S)).
      etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J g)).
      reflexivity.
    * etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.
      apply cancel_postcomposition.
      etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J g)).
      apply id_left.
  - etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn2.
    etrans. apply assoc'.
    etrans. apply id_left.
    etrans. apply PushoutArrow_PushoutIn2.
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply PushoutArrow_PushoutIn2.
    etrans. apply assoc'.
    etrans. apply id_left.
    etrans. apply PushoutArrow_PushoutIn2.
    apply id_left.
Qed.

Definition one_step_comonad_laws : 
    Monad_laws one_step_comonad_data.
Proof.
  repeat split; intro g; use arrow_mor_eq.
  - apply id_left.
  - apply pathsinv0.
    use PushoutEndo_is_identity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply precompWithCoproductArrowInclusion.
      apply pathsinv0.

      use CoproductArrowUnique.
      intro.
      (* cbn. *)
      apply pathsinv0.
      apply id_left.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn2.
      apply id_left.
  - apply id_left.
  - apply pathsinv0.
    use PushoutEndo_is_identity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.

      apply pathsinv0.
      etrans. exact (pathsinv0 (id_left _)).
      apply cancel_postcomposition.

      apply pathsinv0.
      etrans. use CoproductOfArrowsInclusion_comp.
      apply pathsinv0.
      
      use Coproduct_endo_is_identity.
      intro S.
      etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod CC J g)).
      (* simpl. *)
      etrans. apply cancel_postcomposition.
              apply id_left.
      etrans. apply id_left.
      morcls_lp_coproduct_in_eq.
      
      use arrow_mor_eq.
      + etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply id_right.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod CC J g) _ S).
        reflexivity.
      + etrans. apply assoc'.
        etrans. apply cancel_precomposition.
                apply PushoutArrow_PushoutIn1.
                
        etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod CC J g) _ S).
        reflexivity.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc.
      
      etrans. apply assoc'.
      etrans. apply id_left.
      apply id_left.
  - reflexivity.
  - exact (one_step_comonad_assoc_law11 g).
Qed.

Definition one_step_comonad : 
    lnwfs_over one_step_factorization :=
  (one_step_comonad_mul,, one_step_comonad_laws).

End one_step_monad.
