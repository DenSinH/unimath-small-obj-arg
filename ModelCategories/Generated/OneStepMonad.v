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
    {a : total_category (morcls_disp J) -> C} {CCa : Coproduct _ _ (λ lp, a (pr1 lp))}
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
    {CCa : Coproduct _ _ (λ lp, arrow_dom (pr11 lp))}
    {f : total_category (morcls_disp J)} {S S' : (pr1 f) --> g} :
    S = S' -> CoproductIn CCa (f,, S) = CoproductIn CCa (f,, S').
Proof.
  apply (CoproductInLiftingProblemsEq (a := λ f, arrow_dom (pr1 f))).
Qed.

Lemma CoproductInLiftingProblemsEqCod
    {C : category} {J : morphism_class C} {g : arrow C} 
    {CCa : Coproduct _ _ (λ lp, arrow_cod (pr11 lp))}
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
      apply (CoproductInLiftingProblemsEqDom (S := pr2 i · _)).
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
      apply (CoproductInLiftingProblemsEqDom (S := pr2 i · _)).
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
      abstract (
        apply pathsinv0;
        etrans; [use PushoutArrow_PushoutIn2|];
        reflexivity
      ).
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
        rewrite assoc.
        etrans. apply maponpaths_2.
        use PushoutArrow_PushoutIn1.
        rewrite <- assoc.
        etrans. apply maponpaths.
        use PushoutArrow_PushoutIn1.
        rewrite assoc.
        reflexivity.
      + (* PushoutIn2 (PushoutArrow · PushoutArrow) = arrow_mor00 (S T) · PushoutIn *)
        rewrite assoc.
        etrans. apply maponpaths_2.
        use PushoutArrow_PushoutIn2.
        rewrite <- assoc.
        etrans. apply maponpaths.
        use PushoutArrow_PushoutIn2.
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
  - rewrite assoc.
    etrans. apply maponpaths_2.
            apply PushoutArrow_PushoutIn1.
    rewrite assoc'.
    etrans. apply maponpaths.
            apply PushoutArrow_PushoutIn1.
    etrans. apply precompWithCoproductArrowInclusion.
    
    apply pathsinv0.
    rewrite assoc.
    etrans. apply maponpaths_2.
            apply PushoutArrow_PushoutIn1. 
    etrans. apply postcompWithCoproductArrow.
    
    apply maponpaths.
    apply funextsec.
    intro.
    now rewrite id_left.
  - rewrite assoc.
    etrans. apply maponpaths_2.
            apply PushoutArrow_PushoutIn2.
    rewrite assoc'.
    etrans. apply maponpaths.
            apply PushoutArrow_PushoutIn2.
    
    apply pathsinv0.
    rewrite assoc.
    etrans. apply maponpaths_2.
            apply PushoutArrow_PushoutIn2. 

    apply pathsinv0.
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

(* 
todo: can we use this definition?
      If we do this, I think E1 arising from 
      one_step_monad_functor is not the same
      definitionally as that arising from 
      one_step_comonad_functor, so it might
      not be a good idea...

Definition one_step_monad_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - intro g.
    exact (opp_mor (one_step_comonad_functor (opp_mor g))).
  - intros ? ? γ.
    exact (opp_mor (#one_step_comonad_functor (opp_mor γ))%cat).
Defined.

Definition one_step_monad_functor_is_functor : is_functor one_step_monad_functor_data.
Proof.
  split.
  - exact (functor_id one_step_comonad_functor).
  - intros f g h S T.
    apply (functor_comp one_step_comonad_functor).
Qed.

Definition one_step_monad_functor : functor (arrow C) (arrow C) :=
    (_,, one_step_monad_functor_is_functor). *)

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
    * (* todo: see exactly what's going on here *)
      rewrite assoc.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn1.
      rewrite <- assoc.
      etrans. apply maponpaths.
      use PushoutArrow_PushoutIn1.
      rewrite assoc.
      apply pathsinv0.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn1.
      
      (* simplify left hand side *)
      etrans. { simpl. reflexivity. }
      (* k_x · γ11 = arrow_mor11 (Kγ) · k_x' *) 
      (* this is just the commutativity of the bottom square of the
         commutative cube of φ *)
      set (φax := nat_trans_ax morcls_coprod_nat_trans g g' γ).
      set (bottom_square := bottom_square φax).
      exact (pathsinv0 bottom_square).
    * rewrite assoc.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn2.
      rewrite <- assoc.
      etrans. apply maponpaths.
      use PushoutArrow_PushoutIn2.
      rewrite assoc.
      apply pathsinv0.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn2.

      simpl.
      exact (pathsinv0 (arrow_mor_comm γ)).
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
      ∑B    |Kg'       |
        \   |=     PO    λ1g'
          \ v∑f'       v
           ∑B' - - - > E1g'
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
    abstract (
      etrans; [apply id_left|];
      (* commuting cube construction is a pushout arrow *)
      apply pathsinv0;
      etrans; [apply PushoutArrow_PushoutIn2|];
      now rewrite id_left
    ).
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
    * etrans. apply assoc.
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
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod J g' (CC _)) _ (pr1 i,, _)).
        reflexivity.
      + etrans. apply assoc'.
        etrans. apply maponpaths.
                apply PushoutArrow_PushoutIn1.
        etrans. apply assoc.
        etrans. apply maponpaths_2.
                apply  (CoproductInCommutes (morcls_lp_cod_coprod J g (CC _))).
        etrans. apply assoc'.
        etrans. apply id_left.
        reflexivity.
    * etrans. apply assoc.
      etrans. apply maponpaths_2.
              use PushoutArrow_PushoutIn2.
      etrans. rewrite assoc'.
              apply maponpaths.
              apply PushoutArrow_PushoutIn2. 
      etrans. now rewrite assoc, id_right.

      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      etrans. rewrite assoc'.
              apply maponpaths.
              apply PushoutArrow_PushoutIn2.
      etrans. apply id_left.
      apply pathsinv0.
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

Definition one_step_comonad_laws : Monad_laws one_step_comonad_data.
Proof.
  repeat split; intro g; (apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod); simpl.
  - now rewrite id_left.
  - use (MorphismsOutofPushoutEqual 
          (isPushout_Pushout (morcls_lp_coprod_diagram_pushout J g (CC _) POs))).
    * rewrite assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn1.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1.
      rewrite id_right.
      cbn.
      etrans. apply precompWithCoproductArrowInclusion.
      apply pathsinv0.

      use CoproductArrowUnique.
      intro.
      cbn.
      apply pathsinv0.
      etrans. apply id_left.
      reflexivity.
    * rewrite assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn2.
      apply pathsinv0.
      etrans. apply id_right.
      rewrite id_left.
      reflexivity.
  - now rewrite id_left.
  - use (MorphismsOutofPushoutEqual 
          (isPushout_Pushout (morcls_lp_coprod_diagram_pushout J g (CC _) POs))).
    * etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn1.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.

      apply pathsinv0.
      etrans. apply id_right.
      
      unfold morcls_lp_coprod_L1_map.
      cbn.

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
      + rewrite assoc'.
        etrans. apply maponpaths.
                apply PushoutArrow_PushoutIn1.
        cbn.
        etrans. apply (CoproductInCommutes (morcls_lp_cod_coprod J g (CC _)) _ (f,, S)).
        reflexivity.
    * etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc.
      rewrite id_left, id_left, id_right.
      reflexivity.
  - now rewrite id_left, id_left.
  - use (MorphismsOutofPushoutEqual 
          (isPushout_Pushout (morcls_lp_coprod_diagram_pushout J g (CC _) POs))).
    * etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn1.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.

      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn1.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.

      apply cancel_postcomposition.
      cbn.
      apply cancel_precomposition.
      
      use CoproductArrowUnique.
      intro lpλ1g.
      cbn.
      etrans. apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod J (λ1 J g (CC g) POs) (CC _))).
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply id_left.

      morcls_lp_coproduct_in_eq.
      apply subtypePath; [intro; apply homset_property|].
      apply pathsdirprod; cbn.
      + rewrite id_right.
        apply pathsinv0.
        etrans. apply (CoproductInCommutes (morcls_lp_dom_coprod J (λ1 J g (CC g) POs) (CC _))).
        reflexivity.
      + (* rhs = bottom arrow of 
          A ------> C
          |        |
   f=pr1i |   S    | λ1
          v        |
          B -----> E1g
          composed with commuting cube construction of 
          g --> λ1g
          todo: assuming that 
          S11 : B ---> E1g is the same as 
              in          PO
            B ---> ∑ B_x ---> E1g
          works for the rest of the proof, but I am not sure it
          holds
        *)
        destruct lpλ1g as [f S].
        set (S11 := arrow_mor11 S).
        assert (H : S11 = CoproductIn (morcls_lp_cod_coprod J g (CC _)) (f,, S · morcls_lp_coprod_diagram_red J g (CC _) POs) · 
                          PushoutIn1 (morcls_lp_coprod_diagram_pushout J g (CC _) POs)).
        {
          set (ac := CoproductIn (morcls_lp_dom_coprod J g (CC _)) (f,, S · morcls_lp_coprod_diagram_red J g (CC _) POs)).
          set (outer_pushout := POs _ _ _ (pr1 f) ac).
          (* assert (S11 = PushoutIn1 outer_pushout). *)
          
          admit.
        }
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
    * etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc.

      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      rewrite assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn2.
      etrans. apply assoc.
      reflexivity.
Admitted.

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
