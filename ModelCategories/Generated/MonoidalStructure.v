Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.NWFS.

Require Import CategoryTheory.DisplayedCats.Examples.MonadAlgebras.
Require Import CategoryTheory.limits.coproducts.

Local Open Scope cat.
Local Open Scope Cat.
Local Open Scope morcls.



Lemma isaprop_section_disp_axioms {C : category} {D : disp_cat C} (F : section_disp_data D) 
    (Hmor : ∏ (x y : C) (f : x --> y) (c : D x) (d : D y), isaset (c -->[f] d)) :
    isaprop (section_disp_axioms F).
Proof.
  apply isapropdirprod.
  - apply impred; intro.
    apply Hmor.
  - do 5 (apply impred; intro).
    apply Hmor.
Qed.

(* helper for showing section_disp_axioms *)
Lemma section_disp_on_eq_morphisms {C : category} (F : Ff C) {f f' : arrow C} {γ : f --> f'} 
    (H : arrow_mor00 γ · f' = f · arrow_mor11 γ) :
  let alternate := ((arrow_mor00 γ,, arrow_mor11 γ),, H) : f --> f' in
  pr1 (section_disp_on_morphisms (section_disp_data_from_section_disp F) alternate) =
    pr1 (section_disp_on_morphisms (section_disp_data_from_section_disp F) γ).
Proof.
  intro.
  assert (Heq : alternate = γ).
  {
    apply subtypePath; [intro; apply homset_property|].
    reflexivity.
  }
  rewrite Heq.
  reflexivity.
Qed.

Section Ff_composition.

Context {C : category}.

(* F ⊗ F' (compose left factors)
   we flip the terms in Garner to be closer to · notation *)
Definition Ff_lcomp_data (F F' : Ff C) : section_disp_data (three_disp C).
Proof.
  use tpair.
  - intro f.
    set (lf := fact_L F f).
    set (rf := fact_R F f).
    set (l'rf := fact_L F' rf).
    set (r'rf := fact_R F' rf).
    exists (arrow_cod l'rf).
    exists (lf · l'rf), r'rf.
    abstract (
      rewrite assoc';
      etrans; [apply maponpaths;
               apply (three_comp ((fact_functor F') rf))|];
      simpl;
      etrans; [apply (three_comp (f,, _))|];
      reflexivity
    ).
  - intros f f' γ.
    set (lγ := #(fact_L F) γ).
    set (rγ := #(fact_R F) γ).
    set (l'rγ := #(fact_L F') rγ).
    set (r'rγ := #(fact_R F') rγ).
    exists (arrow_mor00 r'rγ).

    set (lf := fact_L F f).
    set (rf := fact_R F f).
    set (l'rf := fact_L F' rf).
    set (r'rf := fact_R F' rf).
    set (lf' := fact_L F f').
    set (rf' := fact_R F f').
    set (l'rf' := fact_L F' rf').
    set (r'rf' := fact_R F' rf').
    
    split; simpl.
    * abstract (
        rewrite assoc;
        apply pathsinv0;
        etrans; [apply maponpaths_2;
                 exact (arrow_mor_comm lγ)|];
        do 2 rewrite assoc';
        apply cancel_precomposition;
        exact (arrow_mor_comm l'rγ)
    ).
    * abstract (
        apply pathsinv0;
        exact (arrow_mor_comm r'rγ)
      ).
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