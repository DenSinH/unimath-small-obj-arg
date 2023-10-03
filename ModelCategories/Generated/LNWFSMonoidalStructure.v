Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.Lifting.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.

Local Open Scope cat.
Local Open Scope Cat.
Local Open Scope morcls.


Section LNWFS_composition.

(*  
All the displayed morphisms can be finished with Qed, since the 
data is always propositional. For the total category morphisms,
defining it in terms of the displayed morphisms (which are propositional)
is optimal, since then we know the morphism it lies over, which is sufficient.
*)

Context {C : category}.

(* F ⊗ F' (compose left factors)
   we flip the terms in Garner to be closer to · notation *)

Local Definition left_reduced_lp 
    (F : Ff C) {f g : arrow C}
    (γ : f --> g) : (f --> fact_R F g).
Proof.
  use mors_to_arrow_mor.
  - exact (arrow_mor00 γ · fact_L F g).
  - exact (arrow_mor11 γ).
  - abstract (
      etrans; [apply assoc'|];
      etrans; [apply cancel_precomposition;
              apply (three_comp (fact_functor F g))|];
      exact (arrow_mor_comm γ)
    ).
Defined.

(* todo move these to NWFS.v, add coercion nwfs >-> lnwfs *)
Lemma lnwfs_Σ_top_map_id {F : Ff C} (L : lnwfs_over F) (f : arrow C) :
    arrow_mor00 (pr1 L f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=lnwfs_L_monad L) f).
  set (top := top_square law1).
  apply pathsinv0.
  etrans.
  exact (pathsinv0 top).
  apply id_right.
Qed.

Lemma lnwfs_Σ_bottom_map_inv {F : Ff C} (L : lnwfs_over F) (f : arrow C) :
    arrow_mor11 (pr1 L f) · arrow_mor (fact_R F (fact_L F f)) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=lnwfs_L_monad L) f).
  set (bottom := bottom_square law1).
  exact bottom.
Qed.

Local Lemma left_reduced_lp_lift
    {F : Ff C} (L : lnwfs_over F)
    {f g : arrow C} (γ : (fact_L F f) --> g) :
  filler (arrow_mor_comm (left_reduced_lp F γ)).
Proof.
  set (Fγ11 := three_mor11 (#(fact_functor F) γ)).
  exists (arrow_mor11 (pr1 L f) · Fγ11).
  abstract (
    split; [
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
              exact (pathsinv0 (arrow_mor_comm (pr1 L f)))|];
      
      etrans; [apply assoc'|];
      etrans; [apply cancel_precomposition;
              exact (pr1 (three_mor_comm (#(fact_functor F) γ)))|];
      
      etrans; [apply cancel_postcomposition;
              exact (lnwfs_Σ_top_map_id L f)|];
      apply id_left
      |
      etrans; [apply assoc'|];
      etrans; [apply cancel_precomposition;
              exact (pathsinv0 (pr2 (three_mor_comm (#(fact_functor F) γ))))|];
      
      etrans; [apply assoc|];
      etrans; [apply cancel_postcomposition;
              exact (lnwfs_Σ_bottom_map_inv L f)|];
      apply id_left
    ]
  ).
Defined.


Definition LNWFS_lcomp_comul_data {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    nat_trans_data (fact_L (F ⊗ F')) ((fact_L (F ⊗ F')) ∙ (fact_L (F ⊗ F'))).
Proof.
  intro f.

  set (λf := fact_L F f).
  set (λ'ρf := fact_L F' (fact_R F f)).
  set (comp := λf · λ'ρf).
  set (λcomp := fact_L F comp).
  set (ρcomp := fact_R F comp).

  transparent assert (L_lp : (fact_L F f --> comp)).
  {
    use mors_to_arrow_mor.
    - exact (identity _).
    - exact (λ'ρf).
    - abstract (apply id_left).
  }

  set (L_lift := left_reduced_lp_lift L L_lp).
  destruct L_lift as [L_lift [L_comm1 L_comm2]].

  transparent assert (L'_lp : (λ'ρf --> ρcomp)).
  {
    use mors_to_arrow_mor.
    - exact (L_lift).
    - exact (identity _).
    - abstract (
        etrans; [exact L_comm2|];
        apply pathsinv0;
        apply id_right
      ).
  }

  set (L'_lift := left_reduced_lp_lift L' L'_lp).
  destruct L'_lift as [L'_lift [L'_comm1 L'_comm2]].

  use mors_to_arrow_mor.
  - exact (identity _).
  - exact (L'_lift).
  - abstract (
      etrans; [apply id_left|];
      apply pathsinv0;
      etrans; 
      [
        etrans; [apply assoc'|];
        apply cancel_precomposition;
        exact L'_comm1
      |];
      etrans; 
      [
        etrans; [apply assoc|];
        apply cancel_postcomposition;
        exact L_comm1
      |];
      etrans; [apply assoc'|];
      etrans; [apply id_left|];
      reflexivity
    ).
Defined.

(* everything used in the construction is natural, so this
   "should be trivial". Of course it's not in UniMath, but
   we just have to reverse all the naturalities we used. *)
Lemma LNWFS_lcomp_comul_axioms {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    is_nat_trans _ _ (LNWFS_lcomp_comul_data L L').
Proof.
  intros f g γ.
  apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod;
      [etrans; [apply id_right|]; apply pathsinv0; apply id_left|].
  (* work away left side (final step of comul_data was
     to use L' to get a lift in a specific diagram) *)
  etrans. 
  {
    (* rewrite naturality of L' at #ρ γ *)
    etrans. apply assoc.
    set (L'natργ := nat_trans_ax (pr1 L') _ _ (#(fact_R F) γ)).
    set (L'natργ11 := pr2 (pathsdirprodweq (base_paths _ _ L'natργ))).
    
    etrans. apply cancel_postcomposition.
            exact L'natργ11.
    etrans. apply assoc'.
    apply cancel_precomposition.

    use (pr1_section_disp_on_morphisms_comp F').
  }

  apply pathsinv0.
  etrans. apply assoc'.
  apply cancel_precomposition.
  
  etrans. use (pr1_section_disp_on_morphisms_comp F').
  use (section_disp_on_eq_morphisms F'); [|etrans; [apply id_left|]; apply pathsinv0; apply id_right].

  (* work away on right side, first step in comul_data
      was to obtain a lift using L *)
  apply pathsinv0.
  etrans. apply assoc.
  etrans. apply cancel_postcomposition.
  {
    (* rewrite naturality of L *)
    set (Lnatγ := nat_trans_ax (pr1 L) _ _ γ).
    set (Lnatγ11 := pr2 (pathsdirprodweq (base_paths _ _ Lnatγ))).
    exact (Lnatγ11).
  }

  etrans. apply assoc'.
  apply pathsinv0.
  etrans. apply assoc'.
  apply cancel_precomposition.

  etrans. use (pr1_section_disp_on_morphisms_comp F).
  apply pathsinv0. 
  etrans. use (pr1_section_disp_on_morphisms_comp F).
  use (section_disp_on_eq_morphisms F); [etrans; [apply id_right|]; apply pathsinv0; apply id_left|].
  
  (* cbn.
  unfold three_mor11, three_mor01.
  cbn. *)
  (* commutativity of F' on morphism #ρ γ *)
  (* middle step was composing a diagram in a specific way *)
  apply pathsinv0.
  exact (pr1 (three_mor_comm (#(fact_functor F') (#(fact_R F ) γ)))).
Qed.

Definition LNWFS_lcomp_comul {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    (fact_L (F ⊗ F')) ⟹ ((fact_L (F ⊗ F')) ∙ (fact_L (F ⊗ F'))) :=
  (_,, LNWFS_lcomp_comul_axioms L L').

Definition LNWFS_lcomp_comul_monad_laws {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    Monad_laws (L_monad_data (F ⊗ F') (LNWFS_lcomp_comul L L')).
Proof.
  repeat split; intro a.
  - apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod; [apply id_left|].
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. exact (pathsinv0 (lnwfs_Σ_bottom_map_inv L' (fact_R F a))).
    apply cancel_precomposition.
    apply pathsinv0.
    
    (* etrans. apply cancel_postcomposition.
            use (section_disp_on_eq_morphisms F' (γ' := identity _)). *)
    admit.
  - apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod; [apply id_left|].
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. exact (pathsinv0 (lnwfs_Σ_bottom_map_inv L' (fact_R F a))).
    apply cancel_precomposition.
    (* etrans.
    {
      cbn.
      unfold three_mor12.
      cbn.
    } *)
    apply pathsinv0.
    etrans. apply (pr1_section_disp_on_morphisms_comp F').
    admit.
  - admit.
    (* apply cancel_postcomposition.
    apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod. *)

Admitted. (* Qed *)

Definition LNWFS_lcomp {F F' : Ff C} (L : LNWFS C F) (L' : LNWFS C F') :
    LNWFS C (F ⊗ F') :=
  (LNWFS_lcomp_comul L L',, LNWFS_lcomp_comul_monad_laws L L').

Definition LNWFS_tot_lcomp (L L' : total_category (LNWFS C)) : 
    total_category (LNWFS C) :=
  (_,, LNWFS_lcomp (pr2 L) (pr2 L')).

Notation "l L⊗ l'" := (LNWFS_lcomp l l') (at level 50).
Notation "l Ltot⊗ l'" := (LNWFS_tot_lcomp l l') (at level 50).

(* I *)
Definition LNWFS_lcomp_unit_comul_data :
    nat_trans_data (fact_L (@Ff_lcomp_unit C)) ((fact_L Ff_lcomp_unit) ∙ (fact_L Ff_lcomp_unit)).
Proof.
  intro f.
  exists (identity _).
  reflexivity.
Defined.

Definition LNWFS_lcomp_unit_comul_axioms : 
    is_nat_trans _ _ LNWFS_lcomp_unit_comul_data.
Proof.
  intros f g γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - now rewrite id_right, id_left.
  - now rewrite id_right, id_left.
Qed.

Definition LNWFS_lcomp_unit_comul : 
    (fact_L (@Ff_lcomp_unit C)) ⟹ ((fact_L Ff_lcomp_unit) ∙ (fact_L Ff_lcomp_unit)) :=
  (_,, LNWFS_lcomp_unit_comul_axioms).

Definition LNWFS_lcomp_unit_comul_monad_laws :
  Monad_laws (L_monad_data (@Ff_lcomp_unit C) (LNWFS_lcomp_unit_comul)).
Proof.
  repeat split; 
    (intro f; 
     apply subtypePath; [intro; apply homset_property|]);
      apply pathsdirprod; try now rewrite id_left.
  - reflexivity.
  - reflexivity.
Qed.

Definition LNWFS_lcomp_unit :
    LNWFS C (@Ff_lcomp_unit C) :=
  (LNWFS_lcomp_unit_comul,, LNWFS_lcomp_unit_comul_monad_laws).

Definition LNWFS_tot_lcomp_unit : 
    total_category (LNWFS C) :=
  (_,, LNWFS_lcomp_unit).

Definition LNWFS_l_id_right {F : Ff C} (L : LNWFS _ F) : 
    (L L⊗ LNWFS_lcomp_unit) -->[Ff_l_id_right F] L.
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    (* cbn. *)
    apply pathsinv0.
    etrans. apply maponpaths.
            apply id_right.
    etrans. apply id_right.
    exact (pathsinv0 (lnwfs_Σ_top_map_id L a)).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply maponpaths.
            apply id_right.
    etrans. apply cancel_postcomposition.
            apply id_left.
    (* cbn.
    unfold three_mor11.
    cbn. *)
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            apply (pr1_section_disp_on_morphisms_comp F).
    etrans. apply cancel_precomposition.
    {
      etrans. use (section_disp_on_eq_morphisms F (γ' := identity _)); apply id_left.
      apply maponpaths.
      exact (section_disp_id F _).
    }
    apply id_right.
  - apply id_left.
  - apply id_left.
Qed.

Definition LNWFS_tot_l_id_right (L : total_category (LNWFS C)) :
    (L Ltot⊗ LNWFS_tot_lcomp_unit) --> L :=
  (_,, LNWFS_l_id_right (pr2 L)).
  
Definition LNWFS_l_id_right_rev {F : Ff C} (L : LNWFS _ F) : 
    L -->[Ff_l_id_right_rev F] (L L⊗ LNWFS_lcomp_unit).
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    (* cbn. *)
    apply pathsinv0.
    etrans. apply maponpaths.
            apply id_right.
    etrans. apply id_right.
    exact (lnwfs_Σ_top_map_id L a).
  - etrans. apply id_left.
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply maponpaths.
            apply id_right.
    (* cbn.
    unfold three_mor11.
    cbn. *)
    apply cancel_precomposition.
    use (section_disp_on_eq_morphisms F); reflexivity.
  - apply id_left.
  - apply id_left.
Qed.

Definition LNWFS_tot_l_id_right_rev (L : total_category (LNWFS C)) :
    L --> (L Ltot⊗ LNWFS_tot_lcomp_unit) :=
  (_,, LNWFS_l_id_right_rev (pr2 L)).

  
Definition LNWFS_l_id_left {F : Ff C} (L : LNWFS _ F) : 
    (LNWFS_lcomp_unit L⊗ L) -->[Ff_l_id_left F] L.
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    apply pathsinv0.
    (* cbn. *)
    etrans. apply maponpaths.
            apply id_left.
    etrans. apply id_right.
    exact (pathsinv0 (lnwfs_Σ_top_map_id L a)).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply maponpaths.
            apply id_right.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
    {
      (* cbn.
      unfold three_mor11.
      cbn. *)
      etrans. use (pr1_section_disp_on_morphisms_comp F).
      etrans. use (section_disp_on_eq_morphisms F (γ' := identity _)).
      - etrans. apply id_right.
        apply id_right.
      - apply id_right.
      - apply maponpaths.
        exact (section_disp_id F _).
    }
    apply id_right.
  - apply id_left.
  - apply id_left.
Qed.

Definition LNWFS_tot_l_id_left (L : total_category (LNWFS C)) :
    (LNWFS_tot_lcomp_unit Ltot⊗ L) --> L :=
  (_,, LNWFS_l_id_left (pr2 L)).
  
Definition LNWFS_l_id_left_rev {F : Ff C} (L : LNWFS _ F) : 
    L -->[Ff_l_id_left_rev F] (LNWFS_lcomp_unit L⊗ L).
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply id_right.
    etrans. apply id_right.
    exact (lnwfs_Σ_top_map_id L a).
  - etrans. apply id_left.
    apply cancel_precomposition.
    apply pathsinv0.
    etrans. apply id_right.
    apply pathsinv0.
    use (section_disp_on_eq_morphisms F).
    * apply id_left.
    * reflexivity.
  - apply id_left.
  - apply id_left.
Qed.

Definition LNWFS_tot_l_id_left_rev (L : total_category (LNWFS C)) :
    L --> (LNWFS_tot_lcomp_unit Ltot⊗ L) :=
  (_,, LNWFS_l_id_left_rev (pr2 L)).

Definition LNWFS_l_prewhisker {F G G': Ff C} (L : LNWFS _ F)
    {Λ : LNWFS _ G} {Λ' : LNWFS _ G'} {τG : G --> G'} (τ : Λ -->[τG] Λ') :
  (L L⊗ Λ) -->[F ⊗pre τG] (L L⊗ Λ').
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply id_right.
    apply id_right.
  - etrans. 
    {
      (* lnwfs_mor_axioms of τ at fact_R F a *)
      etrans. apply assoc.
      apply cancel_postcomposition.
      exact (pr2 (pathsdirprodweq (base_paths _ _ (pr1 τ (fact_R F a))))).
    }
    etrans. apply assoc'.
    apply pathsinv0.
    etrans. apply assoc'.
    apply cancel_precomposition.

    (* naturality of τG at 
    
    (left_reduced_lp_lift L
                (mors_to_arrow_mor (three_mor01 (F a))
                   (three_mor01 (F a) · three_mor01 (G' (fact_R F a)))
                   (identity (three_ob0 (F a))) (three_mor01 (G' (fact_R F a)))
                   (LNWFS_lcomp_comul_data_subproof F G' a))))

    todo: define ^this^ as it's own thing
    *)
    set (τGnat := pr2 τG).

    
    apply pathsinv0.

    admit.
  - apply id_left.
  - 

Admitted.  (* Qed *)

Definition LNWFS_tot_l_prewhisker (L : total_category (LNWFS C))
    {Λ Λ' : total_category (LNWFS C)} (τ : Λ --> Λ') :
  (L Ltot⊗ Λ) --> (L Ltot⊗ Λ') :=
    (_,, LNWFS_l_prewhisker (pr2 L) (pr2 τ)).

Notation "l L⊗pre τ" := (LNWFS_l_prewhisker l τ) (at level 50).
Notation "l Ltot⊗pre τ" := (LNWFS_tot_l_prewhisker l τ) (at level 50).

(* todo: we _could_ do this for LNWFS (displayed) as well, but
   it involves a bunch of transportf's, and I don't know if we
   want to even use this *)
Lemma LNWFS_tot_l_prewhisker_id
    (L Λ : total_category (LNWFS C)) :
  (L Ltot⊗pre identity Λ) = identity _.
Proof.
  apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
  cbn.
  etrans. use Ff_l_prewhisker_id.
  reflexivity.
Qed.

Lemma LNWFS_tot_l_prewhisker_comp
    (L : total_category (LNWFS C)) 
    {Λ Λ' Λ'': total_category (LNWFS C)} 
    (τ : Λ --> Λ') (τ' : Λ' --> Λ''):
  (L Ltot⊗pre (τ · τ')) = (L Ltot⊗pre τ) · (L Ltot⊗pre τ').
Proof.
  apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
  cbn.
  etrans. use Ff_l_prewhisker_comp.
  reflexivity.
Qed.

Definition LNWFS_l_postwhisker {F G G': Ff C}
    {Λ : LNWFS _ G} {Λ' : LNWFS _ G'} {τG : G --> G'} 
    (τ : Λ -->[τG] Λ') (L : LNWFS _ F) :
  (Λ L⊗ L) -->[τG ⊗post F] (Λ' L⊗ L).
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply id_right.
    apply id_right.
  - 
    admit.
  - apply id_left.
  - cbn.
    (* naturality of τG *)
    admit.
Admitted.  (* Qed *)

Definition LNWFS_tot_l_postwhisker {Λ Λ' : total_category (LNWFS C)} 
    (τ : Λ --> Λ') (L : total_category (LNWFS C)):
  (Λ Ltot⊗ L) --> (Λ' Ltot⊗ L):=
    (_,, LNWFS_l_postwhisker (pr2 τ) (pr2 L)).

Notation "τ L⊗post l" := (LNWFS_l_postwhisker τ l) (at level 50).
Notation "τ Ltot⊗post l" := (LNWFS_tot_l_postwhisker τ l) (at level 50).

Lemma LNWFS_tot_l_postwhisker_id
    (Λ L : total_category (LNWFS C)) :
  ((identity Λ) Ltot⊗post L) = identity _.
Proof.
  apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
  cbn.
  etrans. use Ff_l_postwhisker_id.
  reflexivity.
Qed.

Lemma LNWFS_tot_l_postwhisker_comp
    {Λ Λ' Λ'': total_category (LNWFS C)} 
    (τ : Λ --> Λ') (τ' : Λ' --> Λ'')
    (L : total_category (LNWFS C)) :
  ((τ · τ') Ltot⊗post L) = (τ Ltot⊗post L) · (τ' Ltot⊗post L).
Proof.
  apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
  cbn.
  etrans. use Ff_l_postwhisker_comp.
  reflexivity.
Qed.

Definition LNWFS_l_assoc {F F' F'' : Ff C} 
    (L : LNWFS _ F) (L' : LNWFS _ F') (L'' : LNWFS _ F'') :
  (L L⊗ L') L⊗ L'' -->[Ff_l_assoc F F' F''] (L L⊗ (L' L⊗ L'')).
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_left.
    apply id_left.
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply id_right.

            
    admit.
  - apply id_left.
  - apply id_left.
Admitted.  (* Qed *)

Definition LNWFS_tot_l_assoc (L L' L'' : total_category (LNWFS C)) :
    (L Ltot⊗ L') Ltot⊗ L'' --> (L Ltot⊗ (L' Ltot⊗ L'')) :=
  (_,, LNWFS_l_assoc (pr2 L) (pr2 L') (pr2 L'')).

Definition LNWFS_l_assoc_rev {F F' F'' : Ff C} 
    (L : LNWFS _ F) (L' : LNWFS _ F') (L'' : LNWFS _ F'') :
  (L L⊗ (L' L⊗ L'')) -->[Ff_l_assoc_rev F F' F''] ((L L⊗ L') L⊗ L'').
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_left.
    apply id_left.
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply cancel_precomposition.
            apply id_right.
    admit.
  - apply id_left.
  - apply id_left.
Admitted.  (* Qed *)

Definition LNWFS_tot_l_assoc_rev (L L' L'' : total_category (LNWFS C)) :
    (L Ltot⊗ (L' Ltot⊗ L'')) --> ((L Ltot⊗ L') Ltot⊗ L'' ) :=
  (_,, LNWFS_l_assoc_rev (pr2 L) (pr2 L') (pr2 L'')). 

Definition LNWFS_l_mor_comp {F F' G G' : Ff C} 
    {τF : F --> F'} {ρG : G --> G'}
    {L : LNWFS _ F} {L' : LNWFS _ F'}
    {Λ : LNWFS _ G} {Λ' : LNWFS _ G'}
    (τ : L -->[τF] L') (ρ : Λ -->[ρG] Λ') :
  (L L⊗ Λ) -->[Ff_l_mor_comp τF ρG] (L' L⊗ Λ').
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_left.
    apply id_left.
  - 
    admit.
  - apply id_left.
  - admit.
Admitted.  (* Qed *)

Definition LNWFS_tot_l_mor_comp {L L' Λ Λ' : total_category (LNWFS C)}
    (τ : L --> L') (ρ : Λ --> Λ') :
  (L Ltot⊗ Λ) --> (L' Ltot⊗ Λ') :=
    (_,, LNWFS_l_mor_comp (pr2 τ) (pr2 ρ)).

Definition LNWFS_l_point {F : Ff C} (L : LNWFS _ F) :
    LNWFS_lcomp_unit -->[Ff_l_point F] L.
Proof.
  split; (intro; apply subtypePath; [intro; apply homset_property|]; apply pathsdirprod).
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_left.
    etrans. apply id_left.
    exact (pathsinv0 (lnwfs_Σ_top_map_id L a)).
  - etrans. exact (pathsinv0 (arrow_mor_comm (pr1 L a))).
    etrans. apply cancel_postcomposition.
            exact (lnwfs_Σ_top_map_id L a).
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_left.
    apply id_left.
  - apply id_left.
  - apply (three_comp (fact_functor F a)).
Qed.

Definition LNWFS_tot_l_point (L : total_category (LNWFS C)) :
    LNWFS_tot_lcomp_unit --> L :=
  (_,, LNWFS_l_point (pr2 L)).

Lemma LNWFS_tot_mor_eq {L L' : total_category (LNWFS C)} 
    (τ τ' : L --> L') :
  (∏ (f : arrow C), pr1 (pr11 τ f) = pr1 (pr11 τ' f)) -> 
      τ = τ'.
Proof.
  intro H.
  apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
  apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
  apply funextsec.
  intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  exact (H f).
Qed.


Lemma LNWFS_tot_l_id_left_rev_comp (X A : total_category (LNWFS C)) :
    LNWFS_tot_l_id_left_rev (X Ltot⊗ A) = 
    (LNWFS_tot_l_id_left_rev X Ltot⊗post A) · LNWFS_tot_l_assoc _ _ _.
Proof.
  apply LNWFS_tot_mor_eq.
  intro f.
  (* cbn. *)
  apply pathsinv0.
  etrans. apply pr1_transportf_const.
  (* cbn. *)
  etrans. apply id_right.
  etrans. use (section_disp_on_eq_morphisms' (pr1 A) (γ := identity _)).
  etrans. apply maponpaths. use (section_disp_id (pr1 A)).
  reflexivity.
Qed.


End LNWFS_composition.

Notation "l L⊗ l'" := (LNWFS_lcomp l l') (at level 50).
Notation "l Ltot⊗ l'" := (LNWFS_tot_lcomp l l') (at level 50).
Notation "l L⊗pre τ" := (LNWFS_l_prewhisker l τ) (at level 50).
Notation "l Ltot⊗pre τ" := (LNWFS_tot_l_prewhisker l τ) (at level 50).
Notation "τ L⊗post l" := (LNWFS_l_postwhisker τ l) (at level 50).
Notation "τ Ltot⊗post l" := (LNWFS_tot_l_postwhisker τ l) (at level 50).

Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import CategoryTheory.Monoidal.Displayed.TotalMonoidal.

Section LNWFS_monoidal.

Context {C : category}.

Definition LNWFS_disp_tensor_data : disp_tensor (LNWFS C) Ff_monoidal.
Proof.
  use tpair.
  - use tpair.
    * exact (@LNWFS_lcomp C).
    * split.
      + intros; apply LNWFS_l_prewhisker.
        assumption.
      + intros A F F' γ α L L' γγ.
        exact (LNWFS_l_postwhisker γγ L').
  - abstract (
      repeat split; repeat intro; apply isaprop_lnwfs_mor_axioms
    ).
Defined.

Definition LNWFS_disp_monoidal_data : disp_monoidal_data (LNWFS C) Ff_monoidal.
Proof.
  exists LNWFS_disp_tensor_data.
  exists LNWFS_lcomp_unit.
  repeat split.
  - exact (pr1 (LNWFS_l_id_left xx)).
  - exact (pr2 (LNWFS_l_id_left xx)).
  - exact (pr1 (LNWFS_l_id_left_rev xx)).
  - exact (pr2 (LNWFS_l_id_left_rev xx)).
  - exact (pr1 (LNWFS_l_id_right xx)).
  - exact (pr2 (LNWFS_l_id_right xx)).
  - exact (pr1 (LNWFS_l_id_right_rev xx)).
  - exact (pr2 (LNWFS_l_id_right_rev xx)).
  - exact (pr1 (LNWFS_l_assoc xx yy zz)).
  - exact (pr2 (LNWFS_l_assoc xx yy zz)).
  - exact (pr1 (LNWFS_l_assoc_rev xx yy zz)).
  - exact (pr2 (LNWFS_l_assoc_rev xx yy zz)).
Defined.

Definition LNWFS_disp_monoidal_laws : disp_monoidal_laws LNWFS_disp_monoidal_data.
Proof.
  repeat split; (repeat intro; apply isaprop_lnwfs_mor_axioms).
Qed.

Definition LNWFS_monoidal : disp_monoidal (LNWFS C) Ff_monoidal :=
    (_,, LNWFS_disp_monoidal_laws).

Definition LNWFS_tot_monoidal : monoidal _ :=
    total_monoidal LNWFS_monoidal.

Definition Ff_monoidal : monoidal (Ff C) :=
    (_,, Ff_monoidal_laws).

End LNWFS_monoidal.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.

Section LNWFS_monoid_is_NWFS.

Context {C : category}.
Local Definition LNWFSC := total_category (LNWFS C).


Definition LNWFS_tot_monoid_is_NWFS_monoid_data 
    {L : LNWFSC} (R : monoid (LNWFS_tot_monoidal) L) :
  monoid_data Ff_monoidal (pr1 L).
Proof.
  set (Rμ := pr1 (monoid_to_monoid_data _ R)).
  set (RI := pr2 (monoid_to_monoid_data _ R)).

  repeat split.
  - exact (pr1 Rμ).
  - exact (pr1 RI).
Defined.

Definition LNWFS_tot_monoid_is_NWFS_monoid_axioms
    {L : LNWFSC} (R : monoid (LNWFS_tot_monoidal) L) :
  monoid_laws _ (LNWFS_tot_monoid_is_NWFS_monoid_data R).
Proof.
  repeat split.
  - set (law := monoid_to_unit_left_law _ R).
    apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
    exact (base_paths _ _ (base_paths _ _ law)).
  - set (law := monoid_to_unit_right_law _ R).
    apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
    exact (base_paths _ _ (base_paths _ _ law)).
  - set (law := monoid_to_assoc_law _ R).
    apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
    exact (base_paths _ _ (base_paths _ _ law)).
Qed.

Definition LNWFS_tot_monoid_projection 
      {L : LNWFSC} (R : monoid (LNWFS_tot_monoidal) L) :
  monoid Ff_monoidal (pr1 L) :=
    (_,, LNWFS_tot_monoid_is_NWFS_monoid_axioms R).

Definition LNWFS_tot_monoid_is_NWFS 
    {L : LNWFSC} (R : monoid (LNWFS_tot_monoidal) L) 
    (H : Ff_monoid_RNWFS_condition (LNWFS_tot_monoid_projection R)):
  NWFS C (pr1 L).
Proof.
  split.
  - exact (pr2 L).
  - use Ff_monoid_is_RNWFS.
    (* project monoid R down to Ff C *)
    * exact (LNWFS_tot_monoid_projection R).
    * exact H.
Defined.

End LNWFS_monoid_is_NWFS.
