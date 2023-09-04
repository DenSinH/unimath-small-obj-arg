Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.

Local Open Scope cat.
Local Open Scope Cat.
Local Open Scope morcls.


Section LNWFS_composition.

Context {C : category}.

(* F ⊗ F' (compose left factors)
   we flip the terms in Garner to be closer to · notation *)
Definition LNWFS_lcomp_comul_data {F F' : Ff C} (L : lnwfs_over F) (L' : lnwfs_over F') :
    nat_trans_data (fact_L (F ⊗ F')) ((fact_L (F ⊗ F')) ∙ (fact_L (F ⊗ F'))).
Proof.
  intro f.
  set (L_comul := pr1 L).
  set (L'_comul := pr1 L').

  set (ρ'ρ := (fact_R F') ((fact_R F f))).
  set (λρ'ρ := fact_L F ρ'ρ).
  set (λ'ρρ'ρ := fact_L F' (fact_R F ρ'ρ)).

  use mors_to_arrow_mor.
  - exact (identity _).
  - cbn.
Defined.

Lemma Ff_lcomp_axioms (F F' : Ff C) : section_disp_axioms (Ff_lcomp_data F F').
Proof.
  split.
  - intro f.
    set (lf := fact_L F f).
    set (rf := fact_R F f).
    set (l'rf := fact_L F' rf).
    set (r'rf := fact_R F' rf).
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    cbn.
    rewrite (section_disp_id F).
    (* cbn.
    unfold three_mor11.
    cbn. *)
    
    etrans. use (section_disp_on_eq_morphisms _ (γ := identity rf)).
    etrans. apply maponpaths.
            exact (section_disp_id F' rf).
    reflexivity.
  - intros f f' f'' γ γ'.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    simpl.
    rewrite (section_disp_comp F _ _ _).
    (* cbn.
    unfold three_mor11.
    cbn. *)

    set (Fγ := #(fact_R F) γ).
    set (Fγ' := #(fact_R F) γ').
    
    etrans. use (section_disp_on_eq_morphisms _ (γ := Fγ · Fγ')).
    etrans. apply maponpaths.
            apply (section_disp_comp F' _ _ _). 
    cbn.
    reflexivity.
Qed.

Definition Ff_lcomp (F F' : Ff C) : section_disp (three_disp C) :=
    (_,, Ff_lcomp_axioms F F').

Notation "F ⊗ F'" := (Ff_lcomp F F').

(* I *)
Definition Ff_lcomp_unit_data : section_disp_data (three_disp C).
Proof.
  use tpair.
  - intro f.
    exists (arrow_dom f).
    exists (identity _), f.  
    abstract (now rewrite id_left).
  - intros f f' γ.
    cbn.
    exists (arrow_mor00 γ).
    abstract (
      rewrite id_left, id_right;
      split; [reflexivity| apply pathsinv0; exact (arrow_mor_comm γ)]
    ).
Defined.

Definition Ff_lcomp_unit_axioms : section_disp_axioms (Ff_lcomp_unit_data).
Proof.
  split.
  - intro f.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    reflexivity.
  - intros f f' f'' γ γ'.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    reflexivity.
Qed.

Definition Ff_lcomp_unit : section_disp (three_disp C) :=
    (_,, Ff_lcomp_unit_axioms).

(* todo: is a natural transformation sufficient? *)
(* Lemma Ff_l_id_left (F : Ff C) : 
    F ⊗ Ff_lcomp_unit = F.
Proof.
  apply subtypePath.
  - intro.
    use isaprop_section_disp_axioms.
    intros.
    apply isaset_total2; [apply homset_property|].
    intro.
    apply isasetaprop; apply isapropdirprod; apply homset_property.
  - simpl.
    show_id_type.
    (* this becomes a huge mess, need to show equality of
       Definition section_disp_data {C} (D : disp_cat C) : UU
        := ∑ (Fob : forall x:C, D x),
          (forall (x y:C) (f:x --> y), Fob x -->[f] Fob y).
    *)
    admit.
Admitted. *)

Definition Ff_l_id_right_data (F : Ff C) : 
    section_nat_trans_disp_data (F ⊗ Ff_lcomp_unit) F.
Proof.
  intro f.
  cbn.
  exists (identity _).
  abstract (
    now split; rewrite id_right, id_left; [rewrite id_right|]
  ).
Defined.

Definition Ff_l_id_right_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_id_right_data F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  etrans. use (pr1_transportf (id_right γ @ ! id_left γ) _).
  cbn; rewrite transportf_const.
  now rewrite id_left, id_right.
Qed.

Definition Ff_l_id_right (F : Ff C) : section_nat_trans_disp (F ⊗ Ff_lcomp_unit) F :=
    (_,, Ff_l_id_right_axioms F).

Definition Ff_l_id_right_rev_data (F : Ff C) : 
    section_nat_trans_disp_data F (F ⊗ Ff_lcomp_unit).
Proof.
  intro f.
  cbn. 
  exists (identity _).
  abstract (
    now split; rewrite id_right, id_left; [rewrite id_right|]
  ).
Defined.

Definition Ff_l_id_right_rev_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_id_right_rev_data F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  etrans. use (pr1_transportf (id_right γ @ ! id_left γ) _).
  cbn; rewrite transportf_const.
  now rewrite id_left, id_right.
Qed.

Definition Ff_l_id_right_rev (F : Ff C) : section_nat_trans_disp F (F ⊗ Ff_lcomp_unit)  :=
    (_,, Ff_l_id_right_rev_axioms F).

Definition Ff_l_id_left_data (F : Ff C) : 
    section_nat_trans_disp_data (Ff_lcomp_unit ⊗ F) F.
Proof.
  intro f.
  cbn.
  exists (identity _).
  abstract (
    now split; rewrite id_right, id_left; [rewrite id_left|]
  ).
Defined.

Definition Ff_l_id_left_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_id_left_data F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use (pr1_transportf (id_right γ @ ! id_left γ) _).
  cbn; rewrite transportf_const.
  simpl.
  rewrite id_right, id_left.
  unfold three_mor11.
  cbn.
  unfold three_mor22.
  use section_disp_on_eq_morphisms.
Qed.

Definition Ff_l_id_left (F : Ff C) : section_nat_trans_disp (Ff_lcomp_unit ⊗ F) F :=
    (_,, Ff_l_id_left_axioms F).

Definition Ff_l_id_left_rev_data (F : Ff C) : 
    section_nat_trans_disp_data F (Ff_lcomp_unit ⊗ F).
Proof.
  intro f.
  cbn.
  exists (identity _).
  abstract (
    now split; rewrite id_right, id_left; [rewrite id_left|]
  ).
Defined.

Definition Ff_l_id_left_rev_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_id_left_rev_data F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use (pr1_transportf (id_right γ @ ! id_left γ) _).
  cbn; rewrite transportf_const.
  simpl.
  rewrite id_right, id_left.
  apply pathsinv0.
  use section_disp_on_eq_morphisms.
Qed.

Definition Ff_l_id_left_rev (F : Ff C) : section_nat_trans_disp F (Ff_lcomp_unit ⊗ F) :=
    (_,, Ff_l_id_left_rev_axioms F).

Definition Ff_l_prewhisker_data (F : Ff C) {G G'} (τ : section_nat_trans_disp G G') :
    section_nat_trans_disp_data (F ⊗ G) (F ⊗ G').
Proof.
  intro f.
  cbn.
  set (τρf := τ (fact_R F f)).
  destruct τρf as [mor [comm1 comm2]].
  exists (mor).
  abstract (
    split; [
      rewrite assoc, id_left, assoc';
      apply cancel_precomposition;
      etrans; [exact comm1|];
      now rewrite id_left|
      rewrite id_right;
      apply pathsinv0;
      etrans; [exact (pathsinv0 comm2)|];
      now rewrite id_right
    ]
  ).
Defined.

Definition Ff_l_prewhisker_axioms (F : Ff C) {G G'} (τ : section_nat_trans_disp G G') :
    section_nat_trans_disp_axioms (Ff_l_prewhisker_data F τ).
Proof.
  intros f f' γ.
  
  destruct τ as [τ τax].
  unfold section_nat_trans_disp_axioms in τax.
  (* it should just be this... *)
  set (test := τax _ _ (#(fact_R F) γ)).


  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use (pr1_transportf (id_right γ @ ! id_left γ) _).
  cbn; rewrite transportf_const.
  simpl.
  unfold three_mor11.
  cbn.
  apply pathsinv0.
  (* τ (ρf) · (G' (Fγ)) *)
  (* this is effectively the naturality of τ *)
  admit.
Admitted.

Definition Ff_l_prewhisker (F : Ff C) {G G'} (τ : section_nat_trans_disp G G') :
    section_nat_trans_disp (F ⊗ G) (F ⊗ G') :=
  (_,, Ff_l_prewhisker_axioms F τ).

Notation "F ⊗pre τ" := (Ff_l_prewhisker F τ) (at level 50).


Definition Ff_l_postwhisker_data {G G'} (τ : section_nat_trans_disp G G') (F : Ff C) :
    section_nat_trans_disp_data (G ⊗ F) (G' ⊗ F).
Proof.
  intro f.
  
  destruct (τ f) as [τf [commτ1 commτ2]].
  set (ρGf := fact_R G f).
  set (ρG'f := fact_R G' f).
  unshelve epose (γρ := _ : ρGf --> ρG'f).
  {
    use mors_to_arrow_mor.
    - exact τf.
    - exact (identity _).
    - abstract (exact (pathsinv0 commτ2)).
  }
  
  set (Fγρ := (section_disp_on_morphisms (section_disp_data_from_section_disp F) γρ)).
  exists (pr1 Fγρ).
  set (comm := pr2 Fγρ).
  simpl in comm.

  (* commutativity of diagram
       =======
     |         |
  λG |         | λG'
     v   τf    v
       ------>   
     |         |
λFρG |         | λFρG'
     v   τρf   v
     □ ------>□  
     |         |
ρFρG |         | ρFρG'
     v         v  
       =======   
    *)
  abstract (
    split; [
      cbn; rewrite assoc';
      etrans; [apply maponpaths; exact (pr1 comm)|];
      rewrite assoc, assoc;
      apply cancel_postcomposition;
      exact (commτ1)|
      exact (pr2 comm)
    ]
  ).
Defined.

Definition Ff_l_postwhisker_axioms {G G'} (τ : section_nat_trans_disp G G') (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_postwhisker_data τ F).
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use (pr1_transportf (id_right γ @ ! id_left γ) _).
  cbn; rewrite transportf_const.
  simpl.
  unfold three_mor11.
  cbn.
  (* destruct τ as [τ τax].
  unfold section_nat_trans_disp_axioms in τax.
  set (test := τax _ _ (#(fact_R F) γ)).
  apply pathsinv0. *)
  (* this is effectively the naturality of τ *)
  admit.
Admitted.

Definition Ff_l_postwhisker {G G'} (τ : section_nat_trans_disp G G') (F : Ff C) :
    section_nat_trans_disp (G ⊗ F) (G' ⊗ F) :=
  (_,, Ff_l_postwhisker_axioms τ F).

Notation "τ ⊗post F" := (Ff_l_postwhisker τ F) (at level 50).


Definition Ff_l_assoc_data (F F' F'' : Ff C) :
    section_nat_trans_disp_data ((F ⊗ F') ⊗ F'') (F ⊗ (F' ⊗ F'')).
Proof.
  intro f.
  exists (identity _).
  abstract (
    split; rewrite id_left, id_right;
      [cbn; now rewrite assoc|reflexivity]
  ).
Defined.

Definition Ff_l_assoc_axioms (F F' F'' : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_assoc_data F F' F'').
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  (* for some reason this becomes insanely slow *)
  (* etrans. use (pr1_transportf (id_right γ @ ! id_left γ) _).
  etrans.
  {
    rewrite transportf_const.
    reflexivity.
  }
  cbn.
  rewrite id_left.
  rewrite id_right.
  unfold three_mor11.
  cbn. *)
  admit.
Admitted.

End Ff_composition.