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
  rewrite H.
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

Local Ltac morcls_lp_coproduct_in_eq := match goal with 
    |- CoproductIn _ ?S = CoproductIn _ ?S'
    => apply (CoproductInLiftingProblemsEqCod) ||
       apply (CoproductInLiftingProblemsEqCod (S:=pr2 S)) ||
       apply (CoproductInLiftingProblemsEqCod (S':=pr2 S')) ||
       apply (CoproductInLiftingProblemsEqDom) ||
       apply (CoproductInLiftingProblemsEqDom (S:=pr2 S)) ||
       apply (CoproductInLiftingProblemsEqDom (S':=pr2 S'))
    end.

Section one_step_monad.

Context {C : category} (J : morphism_class C).
Context (CC : ∏ (g : arrow C), Coproducts (morcls_lp J g) C) (POs : Pushouts C).

(* Garner 2008, section 5.2 (functor K) *)
Definition morcls_coprod_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - (* sending g to ∑_{x ∈ S_g} f_x*)
    intro g.
    exact (morcls_lp_coprod J g (CC g)).
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
        simpl;
        unfold morcls_lp_coprod;
        simpl;
        etrans; [use CoproductOfArrowsInclusion_comp|];
        apply pathsinv0;
        etrans; [use CoproductOfArrowsInclusion_comp|];
        simpl;
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
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; simpl; apply pathsinv0, Coproduct_endo_is_identity; intro.
    * etrans.
      apply (CoproductOfArrowsInclusionIn _ (morcls_lp_dom_coprod J g (CC g))).
      simpl.
      etrans. apply id_left.
      unfold morcls_lp_dom_coprod.
      (* apply (CoproductInLiftingProblemsEqDom (S := pr2 i · _)). *)
      morcls_lp_coproduct_in_eq.
      etrans. apply id_right.
      reflexivity.
    * etrans.
      apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod J g (CC g))).
      simpl.
      etrans. apply id_left.
      morcls_lp_coproduct_in_eq.
      (* apply (CoproductInLiftingProblemsEqCod (S := pr2 i · _)). *)
      apply id_right.
  - intros f g h S T.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; simpl; apply pathsinv0.
    * etrans. use CoproductOfArrowsInclusion_comp.
      simpl.
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
      simpl.
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

Definition morcls_coprod_nat_trans_data : nat_trans_data morcls_coprod_functor (functor_identity _).
Proof.
  intro g.
  exact (morcls_lp_coprod_diagram J g (CC g)).
Defined.

Definition morcls_coprod_nat_trans_is_nat_trans : is_nat_trans _ _ morcls_coprod_nat_trans_data.
Proof.
  intros g g' γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod; simpl.
  - etrans.
    use precompWithCoproductArrowInclusion.
    simpl.
    rewrite postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    etrans. apply id_left.
    reflexivity.
  - etrans.
    use precompWithCoproductArrowInclusion.
    simpl.
    rewrite postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    etrans. apply id_left.
    reflexivity.
Qed.

(* φ in Garner 2007, p23 *)
Definition morcls_coprod_nat_trans : nat_trans morcls_coprod_functor (functor_identity _) :=
    (_,, morcls_coprod_nat_trans_is_nat_trans).

Arguments CoproductObject {_} {_} {_}.
Lemma commuting_cube_construction {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod J _ (CC g)) 
          --> CoproductObject (morcls_lp_dom_coprod J _ (CC g'))}
    {bb : CoproductObject (morcls_lp_cod_coprod J _ (CC g)) 
          --> CoproductObject (morcls_lp_cod_coprod J _ (CC g'))}
    {cc : arrow_dom g --> arrow_dom g'}
    (leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g'))
    (topface  : arrow_mor00 (morcls_lp_coprod_diagram J g (CC _)) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram J g' (CC _))) :
  E1 J g (CC _) POs --> E1 J g' (CC _) POs.
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
  set (CE1g' := cc · (λ1 J g' (CC g') POs)).
  set (BE1g' := bb · (PushoutIn1 (morcls_lp_coprod_diagram_pushout J g' (CC g') POs))).

  use (PushoutArrow 
       (morcls_lp_coprod_diagram_pushout J g (CC g) POs)
       _ BE1g' CE1g').
  
  abstract (
    (* Left to show commutativity of (outer) pushout diagram *)
    (* Kg · (arrow_mor11 Kγ) · (PushoutIn1 g') = (PushoutIn g) · γ00 · λ1g *)
    unfold CE1g', BE1g';
    do 2 rewrite assoc;

    (* first rewrite commutativity of left face *)
    etrans; [apply maponpaths_2; exact leftface|];
    
    (* rewrite commutativity in top face *)
    apply pathsinv0;
    etrans; [apply maponpaths_2; exact topface|];

    (* cancel precomposition with aa: ∑A --> ∑A' arrow *)
    do 2 rewrite <- assoc;
    apply cancel_precomposition;

    (* all that's left is commutativity in the pushout square of g' *)
    apply pathsinv0;
    exact (PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout J g' (CC g') POs))
  ).
Defined.

Lemma commuting_cube_bottom_face {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod J _ (CC g)) 
          --> CoproductObject (morcls_lp_dom_coprod J _ (CC g'))}
    {bb : CoproductObject (morcls_lp_cod_coprod J _ (CC g)) 
          --> CoproductObject (morcls_lp_cod_coprod J _ (CC g'))}
    {cc : arrow_dom g --> arrow_dom g'}
    {leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g')}
    {topface  : arrow_mor00 (morcls_lp_coprod_diagram J g (CC _)) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram J g' (CC _))} :
  PushoutIn1 (morcls_lp_coprod_diagram_pushout J g (CC g) POs) · commuting_cube_construction leftface topface =
  bb · PushoutIn1 (morcls_lp_coprod_diagram_pushout J g' (CC g') POs).
Proof.
  etrans. apply PushoutArrow_PushoutIn1.
  reflexivity.
Qed.

Lemma commuting_cube_right_face {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod J _ (CC g)) 
          --> CoproductObject (morcls_lp_dom_coprod J _ (CC g'))}
    {bb : CoproductObject (morcls_lp_cod_coprod J _ (CC g)) 
          --> CoproductObject (morcls_lp_cod_coprod J _ (CC g'))}
    {cc : arrow_dom g --> arrow_dom g'}
    {leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g')}
    {topface  : arrow_mor00 (morcls_lp_coprod_diagram J g (CC _)) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram J g' (CC _))} :
  cc · λ1 J g' (CC _) POs =
  λ1 J g (CC _) POs · commuting_cube_construction leftface topface.
Proof.
  apply pathsinv0.
  etrans. apply PushoutArrow_PushoutIn2.
  reflexivity.
Qed.

Lemma commuting_cube_construction_eq {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod J _ (CC g)) 
          --> CoproductObject (morcls_lp_dom_coprod J _ (CC g'))}
    {bb : CoproductObject (morcls_lp_cod_coprod J _ (CC g)) 
          --> CoproductObject (morcls_lp_cod_coprod J _ (CC g'))}
    {cc : arrow_dom g --> arrow_dom g'}
    {aa' : CoproductObject (morcls_lp_dom_coprod J _ (CC g)) 
           --> CoproductObject (morcls_lp_dom_coprod J _ (CC g'))}
    {bb' : CoproductObject (morcls_lp_cod_coprod J _ (CC g)) 
           --> CoproductObject (morcls_lp_cod_coprod J _ (CC g'))}
    {cc' : arrow_dom g --> arrow_dom g'}
    (leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g'))
    (topface  : arrow_mor00 (morcls_lp_coprod_diagram J g (CC _)) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram J g' (CC _)))
    (leftface' : (morcls_coprod_functor g) · bb' = aa' · (morcls_coprod_functor g'))
    (topface'  : arrow_mor00 (morcls_lp_coprod_diagram J g (CC _)) · cc' = 
                 aa' · arrow_mor00 (morcls_lp_coprod_diagram J g' (CC _))) :
  bb = bb' -> cc = cc' -> commuting_cube_construction leftface topface = commuting_cube_construction leftface' topface'.
Proof.
  intros Hb Hc.
  unfold commuting_cube_construction.
  use PushoutArrowUnique.
  - etrans. apply PushoutArrow_PushoutIn1.
    apply cancel_postcomposition.
    exact Hb.
  - etrans. apply PushoutArrow_PushoutIn2.
    apply cancel_postcomposition.
    exact Hc.
Qed.

Local Ltac do_pushout_dragthrough := match goal with 
    | |- PushoutIn1 _ · ((PushoutArrow _ _ _ _ _) · _) = _
          => etrans; [apply assoc|]; do_pushout_dragthrough
    | |- PushoutIn1 _ · (PushoutArrow _ _ _ _ _) · _ = _
          => etrans; [apply maponpaths_2; use PushoutArrow_PushoutIn1|]; do_pushout_dragthrough
    | |- _ · PushoutIn1 _ · (PushoutArrow _ _ _ _ _) = _
          => etrans; [apply assoc'|]; do_pushout_dragthrough
    | |- _ · (PushoutIn1 _ · (PushoutArrow _ _ _ _ _)) = _
          => etrans; [apply maponpaths; use PushoutArrow_PushoutIn1|]; do_pushout_dragthrough
    | |- PushoutIn2 _ · ((PushoutArrow _ _ _ _ _) · _) = _
          => etrans; [apply assoc|]; do_pushout_dragthrough
    | |- PushoutIn2 _ · (PushoutArrow _ _ _ _ _) · _ = _
          => etrans; [apply maponpaths_2; use PushoutArrow_PushoutIn2|]; do_pushout_dragthrough
    | |- _ · PushoutIn2 _ · (PushoutArrow _ _ _ _ _) = _
          => etrans; [apply assoc'|]; do_pushout_dragthrough
    | |- _ · (PushoutIn2 _ · (PushoutArrow _ _ _ _ _)) = _
          => etrans; [apply maponpaths; use PushoutArrow_PushoutIn2|]; do_pushout_dragthrough
    | |- _ => idtac
    end.
Local Ltac pushout_dragthrough :=
    cbn;
    unfold commuting_cube_construction, λ1, ρ1;
    do_pushout_dragthrough; 
    symmetry;
    do_pushout_dragthrough; 
    symmetry.

(* one step comonad functor L1 sends g to λ1g *)
Definition one_step_comonad_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - intro g.
    exact (λ1 J g (CC g) POs).
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
    set (φγ00 := top_square φγ).

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
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * (* top map is identity simply because it comes from a functor *)
      reflexivity.
    * (* bottom map is identity because the pushout arrow is unique *)
      apply pathsinv0, PushoutArrowUnique.
      + now rewrite id_right, functor_id, id_left.
      + now rewrite id_right, id_left.
  - intros f g h S T.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * reflexivity.
    * apply pathsinv0, PushoutArrowUnique.
      (* Gotta keep in mind that (# one_step_comonad_functor_data) S 
         is a PushoutArrow and we can then use pushout properties. *)
      + rewrite functor_comp.
        (* PushoutIn1 · (PushoutArrow · PushoutArrow) = arrow_mor11 · PushoutIn *)
        (* rewrite assoc.
        etrans. apply maponpaths_2.
        use PushoutArrow_PushoutIn1.
        rewrite <- assoc.
        etrans. apply maponpaths.
        use PushoutArrow_PushoutIn1. *)
        pushout_dragthrough.
        rewrite assoc.
        reflexivity.
      + (* PushoutIn2 (PushoutArrow · PushoutArrow) = arrow_mor00 (S T) · PushoutIn *)
        (* rewrite assoc.
        etrans. apply maponpaths_2.
        use PushoutArrow_PushoutIn2.
        rewrite <- assoc.
        etrans. apply maponpaths.
        use PushoutArrow_PushoutIn2. *)
        pushout_dragthrough.
        rewrite assoc.
        reflexivity.
Qed.

Definition one_step_comonad_functor : functor (arrow C) (arrow C) :=
    (_,, one_step_comonad_functor_is_functor).

(* Lemma E1_compat (g : arrow C) : E1 J g (CC _) POs = E1 J (opp_mor g) (CC _) POs.
Proof.
  reflexivity.
Qed.

Context (CCopp : ∏ (g : arrow (op_cat C)), Coproducts (morcls_lp (morphism_class_opp J) g) (op_cat C)) (POsopp : Pushouts (op_cat C)).

Lemma λ1_ρ1_opp_compat (g : arrow C) :
    arrow_cod (λ1 J g (CC _) POs) = arrow_dom (ρ1 (morphism_class_opp J) (opp_arrow g) (CCopp _) POsopp).
Proof.
  cbn.
Defined. *)

Lemma one_step_comonad_ρ1_compat {g g' : arrow C} (γ : g --> g') :
    arrow_mor11 ((# one_step_comonad_functor)%Cat γ) · ρ1 J g' (CC _) POs =
      ρ1 J g (CC _) POs · arrow_mor11 γ.
Proof.
  use (MorphismsOutofPushoutEqual 
        (isPushout_Pushout (morcls_lp_coprod_diagram_pushout J g (CC g) POs))).
  - 
    (* rewrite assoc.
    etrans. apply maponpaths_2.
            apply PushoutArrow_PushoutIn1.
    rewrite assoc'.
    etrans. apply maponpaths.
            apply PushoutArrow_PushoutIn1. *)
    pushout_dragthrough.
    etrans. apply precompWithCoproductArrowInclusion.
    
    apply pathsinv0.
    (* rewrite assoc.
    etrans. apply maponpaths_2.
            apply PushoutArrow_PushoutIn1.  *)
    etrans. apply postcompWithCoproductArrow.
    
    apply maponpaths.
    apply funextsec.
    intro.
    now rewrite id_left.
  - 
    (* rewrite assoc.
    etrans. apply maponpaths_2.
            apply PushoutArrow_PushoutIn2.
    rewrite assoc'.
    etrans. apply maponpaths.
            apply PushoutArrow_PushoutIn2. *)
    pushout_dragthrough.

    (* apply pathsinv0.
    rewrite assoc.
    etrans. apply maponpaths_2.
            apply PushoutArrow_PushoutIn2. 

    apply pathsinv0. *)
    exact (arrow_mor_comm γ).
Qed.

Definition one_step_monad_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - intro g.
    exact (ρ1 J g (CC _) POs).
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
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * (* bottom map is identity because the pushout arrow is unique *)
      apply pathsinv0, PushoutArrowUnique.
      + now rewrite id_right, functor_id, id_left.
      + now rewrite id_right, id_left.
    * (* bottom map is identity simply because it comes from a functor *)
      reflexivity.
  - intros f g h S T.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * rewrite (functor_comp one_step_comonad_functor).
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
  - exact (ρ1 J g (CC g) POs).
  - abstract (exact (arrow_mor_comm (morcls_lp_coprod_diagram_red J g (CC g) POs))).
Defined.

Definition one_step_comonad_counit_is_nat_trans : is_nat_trans _ _ one_step_comonad_counit_data.
Proof.
  intros g g' γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - simpl.
    now rewrite id_left, id_right.
  - (* PushoutArrow (morcls_lp_coprod_diagram_pushout g (CC g) POs) ...
       · ρ1g' = ρ1g · γ11 *)
    (* We are trying to prove an equality of maps E1g --> arrow_cod g' *)
    use (MorphismsOutofPushoutEqual 
          (isPushout_Pushout (morcls_lp_coprod_diagram_pushout J g (CC g) POs))).
    * (* todo: this is a really common strategy, generalize this? *)
      (* rewrite assoc.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn1.
      rewrite <- assoc.
      etrans. apply maponpaths.
      use PushoutArrow_PushoutIn1.
      rewrite assoc.
      apply pathsinv0.
      etrans. apply maponpaths_2.
              use PushoutArrow_PushoutIn1. *)
      pushout_dragthrough.

      (* simplify left hand side *)
      (* etrans. { simpl. reflexivity. } *)
      (* k_x · γ11 = arrow_mor11 (Kγ) · k_x' *) 
      (* this is just the commutativity of the bottom square of the
         commutative cube of φ *)
      set (φax := nat_trans_ax morcls_coprod_nat_trans g g' γ).
      set (bottom_square := bottom_square φax).
      (* exact (pathsinv0 bottom_square). *)
      exact (bottom_square).
    * 
      (* rewrite assoc.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn2.
      rewrite <- assoc.
      etrans. apply maponpaths.
      use PushoutArrow_PushoutIn2.
      rewrite assoc.
      apply pathsinv0.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn2. *)
      pushout_dragthrough.
      
      (* simpl.
      exact (pathsinv0 (arrow_mor_comm γ)). *)
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
  - exact (λ1 J g (CC g) POs).
  - exact (identity _). 
  - abstract (exact (arrow_mor_comm (morcls_lp_coprod_diagram_red_flipped J g (CC g) POs))).
Defined.

Definition one_step_monad_unit_is_nat_trans : is_nat_trans _ _ one_step_monad_unit_data.
Proof.
  intros g g' γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod; simpl.
  - apply pathsinv0.
    etrans. apply PushoutArrow_PushoutIn2.
    reflexivity.
  - now rewrite id_left, id_right.
Qed.

Definition one_step_monad_unit : nat_trans (functor_identity _) (one_step_monad_functor) :=
    (_,, one_step_monad_unit_is_nat_trans).

(* ψg in Garner *)
Definition morcls_lp_coprod_L1_inclusion (g : arrow C) :
    morcls_lp J g -> morcls_lp J (λ1 J g (CC g) POs).
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
  set (rhs := PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout J g (CC g) POs)).
  set (rhs_mor := mors_to_arrow_mor (morcls_lp_coprod J g (CC g)) (λ1 _ _ (CC g) POs) _ _ (pathsinv0 rhs)).
  use (λ inx, inx · rhs_mor).

  (* left hand square *)
  use mors_to_arrow_mor.
  - exact (CoproductIn (morcls_lp_dom_coprod J _ (CC g)) S).
  - exact (CoproductIn (morcls_lp_cod_coprod J _ (CC g)) S).
  - abstract (exact (CoproductInCommutes _ _ S)).
Defined.

(* δg in Garner *)
Definition morcls_lp_coprod_L1_map (g : arrow C) :
    (morcls_lp_coprod J _ (CC g)) --> (morcls_lp_coprod J _ (CC (λ1 J g (CC g) POs))).
Proof.
  (* the inclusion of the objects are just identity on themselves *)
  use mors_to_arrow_mor;
    try exact (CoproductOfArrowsInclusion 
              (morcls_lp_coprod_L1_inclusion g) _ _ 
              (λ _, (identity _))).
  
  (* commutativity *)
  abstract (
    etrans; [use precompWithCoproductArrowInclusion|];
    simpl;
    apply pathsinv0;
    etrans; [use postcompWithCoproductArrow|];
    simpl;
    apply maponpaths;
    apply funextsec;
    intro S;
    rewrite id_left;
    rewrite <- assoc;
    etrans; [apply maponpaths; exact (CoproductOfArrowsInclusionIn _ _ _ _ S)|];
    etrans; [apply maponpaths; apply id_left|];
    reflexivity
  ).
Defined.

Definition one_step_comonad_mul_data : 
    nat_trans_data
      (one_step_comonad_functor)
      (functor_composite one_step_comonad_functor one_step_comonad_functor).
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
        rewrite id_right;
        cbn;
        rewrite precompWithCoproductArrowInclusion;
        apply maponpaths;
        apply funextsec;
        intro S;
        rewrite id_left;
        cbn;
        apply pathsinv0;
        etrans; [exact (CoproductInCommutes _ _ S)|];
        reflexivity
      ).
  - (* commutativity in right face *)
    apply commuting_cube_right_face.
Defined.

Definition one_step_comonad_mul_is_nat_trans : is_nat_trans _ _ one_step_comonad_mul_data.
Proof.
  intros g g' γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - (* simpl. *)
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply id_left.
    reflexivity. (* wow... *)
  - simpl.
    (* equality of arrows E1 g --> E1 (λ1g) *)
    use (MorphismsOutofPushoutEqual 
      (isPushout_Pushout (morcls_lp_coprod_diagram_pushout J g (CC _) POs))).
    * 
      (* etrans. apply assoc.
      etrans. apply maponpaths_2.
              use PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1. 
      etrans. apply assoc.

      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc. *)
      pushout_dragthrough.
      etrans. apply assoc.
      apply pathsinv0.
      etrans. apply assoc.

      apply cancel_postcomposition.
      cbn.
      etrans. use CoproductOfArrowsInclusion_comp.
      apply pathsinv0.
      etrans. use CoproductOfArrowsInclusion_comp.

      unfold CoproductOfArrowsInclusion.
      use CoproductArrowUnique.
      intro.
      simpl.
      etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod J g (CC _))).
      do 2 rewrite assoc'.
      do 2 (etrans; [apply id_left|]).
      apply pathsinv0.
      do 2 (etrans; [apply id_left|]).

      morcls_lp_coproduct_in_eq.
      (* Ltac test := match goal with 
        (* |- CoproductIn ?cc (?f,, ?S) = CoproductIn ?cc (?f,, ?S') *)
        |- CoproductIn _ ?S = CoproductIn _ ?S'
           => set (TYPES := S); set (TYPES' := S')
        end.
      test.
      apply (CoproductInLiftingProblemsEqCod
                (S' := pr2 TYPES')). *)
      
      apply subtypePath; [intro; apply homset_property|].
      apply pathsdirprod; cbn.
      + etrans. apply maponpaths_2.
                apply (CoproductInCommutes (morcls_lp_dom_coprod J g (CC _))).
        apply pathsinv0.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod J g' (CC _)) _ (_,, _)).
        reflexivity.
      + 
        (* etrans. apply assoc'.
        etrans. apply maponpaths.
                apply PushoutArrow_PushoutIn1. *)
        pushout_dragthrough.
        etrans. apply assoc.
        etrans. apply maponpaths_2.
                apply  (CoproductInCommutes (morcls_lp_cod_coprod J g (CC _))).
        etrans. apply assoc'.
        etrans. apply id_left.
        reflexivity.
    * 
      (* etrans. apply assoc.
      etrans. apply maponpaths_2.
              use PushoutArrow_PushoutIn2.
      etrans. rewrite assoc'.
              apply maponpaths.
              apply PushoutArrow_PushoutIn2.  *)
      pushout_dragthrough.
      etrans. now rewrite assoc, id_right.

      apply pathsinv0.
      (* etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      etrans. rewrite assoc'.
              apply maponpaths.
              apply PushoutArrow_PushoutIn2. *)
      etrans. apply id_left.
      pushout_dragthrough.

      reflexivity.
Qed.

Definition one_step_comonad_mul : 
    nat_trans 
      (one_step_comonad_functor)
      (functor_composite one_step_comonad_functor one_step_comonad_functor) :=
  (_,, one_step_comonad_mul_is_nat_trans).

Definition one_step_comonad_functor_with_μ : functor_with_μ (op_cat (arrow C)) :=
    (functor_opp one_step_comonad_functor,, op_nt one_step_comonad_mul).

Definition one_step_comonad_data : Monad_data (op_cat (arrow C)) :=
    ((functor_opp one_step_comonad_functor,,
      op_nt one_step_comonad_mul),,
    op_nt one_step_comonad_counit).

Lemma test2 {g : arrow C} (S : morcls_lp J (λ1 J g (CC _) POs)) :
    arrow_mor11 (pr2 S) = CoproductIn (morcls_lp_cod_coprod J (λ1 J g (CC _) POs) (CC _)) S · arrow_mor11 (morcls_lp_coprod_diagram J (λ1 J g (CC _) POs) (CC _)).
Proof.
  cbn.
  apply pathsinv0.
  etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod J (λ1 J g (CC g) POs) (CC _))).
  reflexivity.
Qed.


Lemma test {g : arrow C} (S : morcls_lp J (λ1 J g (CC _) POs)) :
    arrow_mor11 (pr2 S) = CoproductIn (morcls_lp_cod_coprod J g (CC _)) (pr1 S,, pr2 S · morcls_lp_coprod_diagram_red J g (CC _) POs) · PushoutIn1 (morcls_lp_coprod_diagram_pushout J g (CC _) POs).
Proof.
  (* test2 is apparently invertible this way *)
  (* etrans. apply test2.
  etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod J (λ1 J g (CC g) POs) (CC _))). *)
  apply pathsinv0.
  etrans. apply maponpaths.
          apply CoproductArrowEta.
  {
    show_id_type.
    set (test := )
  }
  
Admitted.

Definition one_step_comonad_laws : Monad_laws one_step_comonad_data.
Proof.
  repeat split; intro g; (apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod); simpl.
  - now rewrite id_left.
  - apply pathsinv0.
    use PushoutEndo_is_identity.
    * 
      (* rewrite assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn1.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1. *)
      pushout_dragthrough.
      etrans. apply precompWithCoproductArrowInclusion.
      apply pathsinv0.

      use CoproductArrowUnique.
      intro.
      cbn.
      apply pathsinv0.
      etrans. apply id_left.
      reflexivity.
    * 
      (* rewrite assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn2. *)
      pushout_dragthrough.
      rewrite id_left.
      reflexivity.
  - now rewrite id_left.
  - apply pathsinv0.
    use PushoutEndo_is_identity.
    * 
      (* etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn1.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc. *)
      pushout_dragthrough.
      etrans. apply assoc.

      apply pathsinv0.
      etrans. { apply pathsinv0. rewrite <- id_left. reflexivity. }
      apply cancel_postcomposition.

      apply pathsinv0.
      etrans. use CoproductOfArrowsInclusion_comp.
      apply pathsinv0.
      
      use Coproduct_endo_is_identity.
      intro S.
      etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod J g (CC g))).
      simpl.
      etrans. apply maponpaths_2.
              apply id_left.
      etrans. apply id_left.
      morcls_lp_coproduct_in_eq.
      apply subtypePath; [intro; apply homset_property|].
      
      destruct S as [f S].
      simpl.
      apply pathsdirprod.
      + rewrite id_right.
        cbn.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod J g (CC _)) _ (f,, S)).
        reflexivity.
      + 
        (* rewrite assoc'.
        etrans. apply maponpaths.
                apply PushoutArrow_PushoutIn1.
        cbn. *)
        pushout_dragthrough.
        etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod J g (CC _)) _ (f,, S)).
        reflexivity.
    * 
      (* etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc. *)
      pushout_dragthrough.
      rewrite id_left, id_left.
      reflexivity.
  - now rewrite id_left, id_left.
  - apply cancel_precomposition.
    use commuting_cube_construction_eq.
    * (* bb = bb' *)
      (* i.e. ∑_λ1g B --> ∑_λ1λ1g B induced by
         δλ1g (from one_step_comonad_mul_data) = L1-incl *)
      cbn.
      (* this boils down to coproduct inclusions of 
         the lifting problems being equal *)
      use CoproductArrowUnique.
      intro S.
      simpl.
      etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod J (λ1 J g (CC g) POs) (CC _))).
      simpl.
      do 2 rewrite id_left.
      morcls_lp_coproduct_in_eq.

      (* need to show that the included lifting problems are equal *)
      apply subtypePath; [intro; apply homset_property|].
      apply pathsdirprod; cbn.
      + rewrite id_right.
        apply pathsinv0.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod J (λ1 J g (CC g) POs) (CC _))).
        reflexivity.
      + destruct S as [f S].
        (* same situation as before *)
        set (S11 := arrow_mor11 S).
        set (H := test2 (f,, S)).
        
        etrans. apply maponpaths_2. exact H.
        rewrite assoc'.
        apply cancel_precomposition.

        etrans. apply postcompWithCoproductArrow.
        apply pathsinv0.
        etrans. apply CoproductArrowEta.
        apply maponpaths.
        apply funextsec.
        intro i.
        apply pathsinv0.
        (* same situation as before *)        
        (* assert (arrow_mor11 (morcls_lp_coprod_diagram J (λ1 J g (CC g) POs) (CC _)) = PushoutIn1 (morcls_lp_coprod_diagram_pushout J (λ1 J g (CC g) POs) (CC _) POs)). *)
        
        etrans.
        {
          (* rewrite commutativity of bottom square of commuting cube
             construction *)
          cbn.
          apply commuting_cube_bottom_face.
        }
        etrans. apply maponpaths. apply PushoutArrow_PushoutIn1.
        rewrite assoc.
        etrans. apply maponpaths_2. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod J g (CC _))).
        
        simpl.
        rewrite assoc'. 
        etrans. apply id_left.
        apply cancel_postcomposition.

        morcls_lp_coproduct_in_eq.
        apply subtypePath; [intro; apply homset_property|].
        apply pathsdirprod; cbn.
        -- etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod J g (CC g)) _ (f,, _)).
           cbn.
           now rewrite id_right.
        -- exact (pathsinv0 H).
        admit.

    * reflexivity.
    use (MorphismsOutofPushoutEqual 
          (isPushout_Pushout (morcls_lp_coprod_diagram_pushout J (λ1 J g (CC _) _) (CC _) POs))).
    * etrans. apply PushoutArrow_PushoutIn1.
      apply pathsinv0.
      etrans. apply PushoutArrow_PushoutIn1.
      (* pushout_dragthrough. *)

      apply cancel_postcomposition.
      cbn.

      use CoproductArrowUnique.
      intro S.
      simpl.
      rewrite id_left.
      etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod J (λ1 J g (CC g) POs) (CC _))).
      rewrite id_left.
      morcls_lp_coproduct_in_eq.
      apply subtypePath; [intro; apply homset_property|].
      apply pathsdirprod; cbn.
      + etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod J (λ1 J g (CC g) POs) (CC _))).
        now rewrite id_right.
      + (* lhs = bottom arrow of 
          A ------> C
          |        |
   f=pr1i |   S    | λ1
          v        |
          B -----> E1g
          composed with commuting cube construction of 
          g --> λ1g

          rhs:
             in              PO
          B ----> ∑_{λ1g} B ----> E1g
          
           ____________________________
          | comm?                      V
          |        ∑_{g} B_x -------> E1g
      S11 |      /      |   bottom of  |
          |   /         |     CCC      |
          |/  in        v              v
          B -----> ∑_{λ1g} B_y -----> E1λ1g 

          todo: assuming that 
          S11 : B ---> E1g is the same as 
              in (· λ1g --> g)             PO
            B ----------------> ∑_{g} B_x ---> E1g
          works for the rest of the proof, but I am not sure it
          holds.
          The composition should not matter, since the map of the
          lifting problem stays the same, so the inclusion 
          B ---> ∑_{g} B_x still includes cod f into the coproduct.
        *)
        destruct S as [f S].
        set (S11 := arrow_mor11 S).
        set (H := test (f,, S)).
        apply pathsinv0.
        etrans. apply maponpaths_2. exact H.
        rewrite assoc'.
        etrans. apply maponpaths. apply PushoutArrow_PushoutIn1.
        rewrite assoc.
        etrans. apply maponpaths_2. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod J g (CC _))).
        
        simpl.
        rewrite assoc'. 
        etrans. apply id_left.
        apply cancel_postcomposition.

        morcls_lp_coproduct_in_eq.
        apply subtypePath; [intro; apply homset_property|].
        apply pathsdirprod; cbn.
        -- etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod J g (CC g)) _ (f,, _)).
           cbn.
           now rewrite id_right.
        -- exact (pathsinv0 H).
    * etrans. apply PushoutArrow_PushoutIn2.
      apply pathsinv0.
      etrans. apply PushoutArrow_PushoutIn2.
      reflexivity.
Admitted. (* todo: this hangs *)

Definition one_step_comonad : Monad (op_cat (arrow C)) :=
    (_,, one_step_comonad_laws).

End one_step_monad.

Section one_step_factorization.
(* the maps λ1 and ρ1 define a functorial factorization *)

Context {C : category} (J : morphism_class C).
Context (CC : ∏ (g : arrow C), Coproducts (morcls_lp J g) C) (POs : Pushouts C).

Definition one_step_factorization_data : section_disp_data (three_disp C).
Proof.
  use tpair.
  - intro g.
    exists (E1 J g (CC _) POs).
    exists (λ1 J g (CC _) POs), (ρ1 J g (CC _) POs).
    apply λ1_ρ1_compat.
  - intros g g' γ.
    cbn.
    set (L1γ := (#(one_step_comonad_functor J CC POs) γ)%cat).
    exists (arrow_mor11 L1γ).
    split; apply pathsinv0.
    * (* commutativity of λ1 and arrow_mor11 (#L1 γ) *)
      exact (arrow_mor_comm L1γ).
    * (* commutativity of ρ1 and arrow_mor11 (#L1 γ) = arrow_mor00 (#R1 γ) *)
      apply one_step_comonad_ρ1_compat.
Defined.

Definition one_step_factorization_axioms : section_disp_axioms one_step_factorization_data.
Proof.
  (* these identities follow from the functorality of g -> λ1g (one_step_comonad_functor)
  *)
  split.
  - intro g.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    cbn.
    (* behavior of commuting cube construction on identity follows from
       identity axiom of the one_step_comonad_functor *)
    set (one_step_comonad_id := functor_id (one_step_comonad_functor J CC POs) g).
    set (bottom := bottom_square one_step_comonad_id).
    exact bottom.
  - intros g1 g2 g3 γ12 γ23.
    (* behavior of commuting cube construction on composition follows from
      identity axiom of the one_step_comonad_functor *)
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    set (one_step_comonad_comp := functor_comp (one_step_comonad_functor J CC POs) γ12 γ23).
    set (bottom := bottom_square one_step_comonad_comp).
    exact bottom.
Qed.

Definition one_step_factorization : functorial_factorization C :=
    (_,, one_step_factorization_axioms).

End one_step_factorization.
