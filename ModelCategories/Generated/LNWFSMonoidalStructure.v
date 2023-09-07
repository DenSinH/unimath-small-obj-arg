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
Definition LNWFS_lcomp_comul_data {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    nat_trans_data (fact_L (F ⊗ F')) ((fact_L (F ⊗ F')) ∙ (fact_L (F ⊗ F'))).
Proof.
  
Admitted.

Lemma LNWFS_lcomp_comul_axioms {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    is_nat_trans _ _ (LNWFS_lcomp_comul_data L L').
Proof.

Admitted. (* Qed *)

Definition LNWFS_lcomp_comul {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    (fact_L (F ⊗ F')) ⟹ ((fact_L (F ⊗ F')) ∙ (fact_L (F ⊗ F'))) :=
  (_,, LNWFS_lcomp_comul_axioms L L').

Definition LNWFS_lcomp_comul_monad_laws {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    Monad_laws (L_monad_data (F ⊗ F') (LNWFS_lcomp_comul L L')).
Proof.

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
  - rewrite id_left.
    cbn.
    apply pathsinv0.
    etrans. apply maponpaths.
            apply id_right.
    etrans. apply id_right.
    (* hint for what comul should be *)
    admit.
  - rewrite id_left.
    (* apply pathsinv0.
    etrans. apply maponpaths.
            apply id_right.
    cbn. *)
    admit.
Admitted.  (* Qed *)

Definition LNWFS_tot_l_id_right (L : total_category (LNWFS C)) :
    (L Ltot⊗ LNWFS_tot_lcomp_unit) --> L :=
  (_,, LNWFS_l_id_right (pr2 L)).
  
Definition LNWFS_l_id_right_rev {F : Ff C} (L : LNWFS _ F) : 
    L -->[Ff_l_id_right_rev F] (L L⊗ LNWFS_lcomp_unit).
Proof.
  
Admitted.  (* Qed *)

Definition LNWFS_tot_l_id_right_rev (L : total_category (LNWFS C)) :
    L --> (L Ltot⊗ LNWFS_tot_lcomp_unit) :=
  (_,, LNWFS_l_id_right_rev (pr2 L)).

  
Definition LNWFS_l_id_left {F : Ff C} (L : LNWFS _ F) : 
    (LNWFS_lcomp_unit L⊗ L) -->[Ff_l_id_left F] L.
Proof.

Admitted.  (* Qed *)

Definition LNWFS_tot_l_id_left (L : total_category (LNWFS C)) :
    (LNWFS_tot_lcomp_unit Ltot⊗ L) --> L :=
  (_,, LNWFS_l_id_left (pr2 L)).
  
Definition LNWFS_l_id_left_rev {F : Ff C} (L : LNWFS _ F) : 
    L -->[Ff_l_id_left_rev F] (LNWFS_lcomp_unit L⊗ L).
Proof.
  
Admitted.  (* Qed *)

Definition LNWFS_tot_l_id_left_rev (L : total_category (LNWFS C)) :
    L --> (LNWFS_tot_lcomp_unit Ltot⊗ L) :=
  (_,, LNWFS_l_id_left_rev (pr2 L)).

Definition LNWFS_l_prewhisker {F G G': Ff C} (L : LNWFS _ F)
    {Λ : LNWFS _ G} {Λ' : LNWFS _ G'} {τG : G --> G'} (τ : Λ -->[τG] Λ') :
  (L L⊗ Λ) -->[F ⊗pre τG] (L L⊗ Λ').
Proof.

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

Admitted.  (* Qed *)

Definition LNWFS_tot_l_assoc (L L' L'' : total_category (LNWFS C)) :
    (L Ltot⊗ L') Ltot⊗ L'' --> (L Ltot⊗ (L' Ltot⊗ L'')) :=
  (_,, LNWFS_l_assoc (pr2 L) (pr2 L') (pr2 L'')).

Definition LNWFS_l_assoc_rev {F F' F'' : Ff C} 
    (L : LNWFS _ F) (L' : LNWFS _ F') (L'' : LNWFS _ F'') :
  (L L⊗ (L' L⊗ L'')) -->[Ff_l_assoc_rev F F' F''] ((L L⊗ L') L⊗ L'').
Proof.

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
  
Admitted.  (* Qed *)

Definition LNWFS_tot_l_mor_comp {L L' Λ Λ' : total_category (LNWFS C)}
    (τ : L --> L') (ρ : Λ --> Λ') :
  (L Ltot⊗ Λ) --> (L' Ltot⊗ Λ') :=
    (_,, LNWFS_l_mor_comp (pr2 τ) (pr2 ρ)).

Definition LNWFS_l_point {F : Ff C} (L : LNWFS _ F) :
    LNWFS_lcomp_unit -->[Ff_l_point F] L.
Proof.

Admitted.  (* Qed. *)

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
  cbn.
  apply pathsinv0.
  etrans. apply pr1_transportf_const.
  cbn.
  rewrite id_right.
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
