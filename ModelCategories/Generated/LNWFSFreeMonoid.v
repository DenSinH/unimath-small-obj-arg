Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.

Local Open Scope cat.


Section LNWFS_alg.

Context {C : category}.

Local Definition LNWFSC := total_category (LNWFS C).

Definition LNWFS_alg_data (T X : LNWFSC) : UU :=
    ∑ (x : T Ltot⊗ X --> X), (LNWFS_tot_l_id_left_rev _) · ((LNWFS_tot_l_point T) Ltot⊗post X) · x  = identity _.

Coercion LNWFS_alg_map {T X : LNWFSC} (XX : LNWFS_alg_data T X) := pr1 XX.
Definition LNWFS_alg_map_comm {T X : LNWFSC} (XX : LNWFS_alg_data T X) := pr2 XX.

Definition LNWFS_alg_mor_axioms 
    {T : LNWFSC}
    {X Y : LNWFSC}
    (XX : LNWFS_alg_data T X)
    (YY : LNWFS_alg_data T Y)
    (f : X --> Y) : UU :=
  XX · f = (T Ltot⊗pre f) · YY.

Lemma isaprop_LNWFS_alg_mor_axioms 
    {T : LNWFSC}
    {X Y : LNWFSC}
    (XX : LNWFS_alg_data T X)
    (YY : LNWFS_alg_data T Y)
    (f : X --> Y) : 
  isaprop (LNWFS_alg_mor_axioms XX YY f).
Proof.
  apply homset_property.
Qed.

Definition LNWFS_alg_disp_ob_mor (T : LNWFSC) : disp_cat_ob_mor LNWFSC.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    exact (LNWFS_alg_data T X).
  - intros X Y XX YY f.
    exact (LNWFS_alg_mor_axioms XX YY f).
Defined.

Definition LNWFS_alg_disp_id_comp (T : LNWFSC) : 
    disp_cat_id_comp _ (LNWFS_alg_disp_ob_mor T).
Proof.
  split.
  - intros X XX.
    simpl.
    unfold LNWFS_alg_mor_axioms.
    rewrite id_right.
    apply pathsinv0.
    etrans. apply maponpaths_2.
            use LNWFS_tot_l_prewhisker_id.
    now rewrite id_left.
  - intros X Y Z f g XX YY ZZ ff gg.
    simpl.
    unfold LNWFS_alg_mor_axioms.

    etrans.
    {
      rewrite assoc, ff, assoc', gg, assoc.
      reflexivity. 
    }
    
    apply pathsinv0.
    etrans. apply maponpaths_2.
            use LNWFS_tot_l_prewhisker_comp.
    reflexivity.
(* Qed because morphisms are propositional anyway *)
Qed.  

Definition LNWFS_alg_disp_data (T : LNWFSC) : 
    disp_cat_data LNWFSC := (_,, LNWFS_alg_disp_id_comp T).

Definition LNWFS_alg_axioms (T : LNWFSC) :
    disp_cat_axioms _ (LNWFS_alg_disp_data T).
Proof.
  repeat split; intros; try apply homset_property.
  apply isasetaprop.
  apply homset_property.
Defined.

Definition LNWFS_alg_disp (T : LNWFSC) : 
    disp_cat LNWFSC := (_,, LNWFS_alg_axioms T).

Definition LNWFS_alg (T : LNWFSC) : 
    category := total_category (LNWFS_alg_disp T).

(* Lemma LNWFS_tot_l_id_left_rev_comp (X A : LNWFSC) :
    LNWFS_tot_l_id_left_rev (X Ltot⊗ A) = 
    (LNWFS_tot_l_id_left_rev X Ltot⊗post A) · LNWFS_tot_l_assoc _ _ _.
Proof.
  apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
  use section_nat_trans_eq.
  intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  cbn.
  apply pathsinv0.
  etrans. apply pr1_transportf_const.
  cbn.
  rewrite id_right.
  etrans. use (section_disp_on_eq_morphisms' (pr1 A) (γ := identity _)).
  etrans. apply maponpaths. use (section_disp_id (pr1 A)).
  reflexivity.
Qed. *)

Definition LNWFS_alg_left_action_data (T : LNWFSC) (A : LNWFSC) :
  functor_data (LNWFS_alg T) (LNWFS_alg T).
Proof.
  use make_functor_data.
  - intro X.
    destruct X as [X [x xrel]].
    exists (X Ltot⊗ A).
    cbn.
    unfold LNWFS_alg_data.
    exists ((LNWFS_tot_l_assoc_rev T X A) · (x Ltot⊗post A)).

    use LNWFS_tot_mor_eq.
    intro f.
    cbn.

    rewrite (LNWFS_tot_l_id_left_rev_comp X A).

    etrans. apply maponpaths_2, maponpaths_2.
            apply LNWFS_tot_l_postwhisker_comp
    apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    apply section_nat_trans_eq.
    intro f.
    apply pathsinv0.
    etrans.
    {
      cbn.
      show_id_type.
    }
    apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|].
    
Admitted.

(* basically want to formalize Garner / Kelly (generalized) stuff about
   T-Alg (/ T-Mod in Garner)
   and how one obtains a monoid from the free T-algebra
   LNWFS should be a monoidal category (Ff_C) is at least

   
*)