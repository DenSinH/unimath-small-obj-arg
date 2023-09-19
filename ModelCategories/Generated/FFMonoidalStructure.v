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
Require Import CategoryTheory.ModelCategories.Generated.Helpers.

Local Open Scope cat.
Local Open Scope Cat.
Local Open Scope morcls.


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
    
    abstract (
      split; [
        rewrite assoc;
        apply pathsinv0;
        etrans; [apply maponpaths_2;
                 exact (arrow_mor_comm lγ)|];
        do 2 rewrite assoc';
        apply cancel_precomposition;
        exact (arrow_mor_comm l'rγ)
      | apply pathsinv0;
        exact (arrow_mor_comm r'rγ)
      ]
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
    
    etrans. use (section_disp_on_eq_morphisms' _ (γ := identity rf)).
    etrans. apply maponpaths.
            exact (section_disp_id F' rf).
    reflexivity.
  - intros f f' f'' γ γ'.
    apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    (* simpl.
    unfold arrow_mor00, three_mor11.
    simpl. *)

    apply pathsinv0.
    etrans. apply pr1_section_disp_on_morphisms_comp.
    use section_disp_on_eq_morphisms.
    * apply pr1_section_disp_on_morphisms_comp.
    * reflexivity.
Qed.

Definition Ff_lcomp (F F' : Ff C) : Ff C :=
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

Definition Ff_lcomp_unit : Ff C :=
    (_,, Ff_lcomp_unit_axioms).

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
  etrans. use pr1_transportf_const.
  cbn.
  now rewrite id_left, id_right.
Qed.

Definition Ff_l_id_right (F : Ff C) : (F ⊗ Ff_lcomp_unit) --> F :=
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
  etrans. use pr1_transportf_const.
  cbn.
  now rewrite id_left, id_right.
Qed.

Definition Ff_l_id_right_rev (F : Ff C) : F --> (F ⊗ Ff_lcomp_unit) :=
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
  
  etrans. use pr1_transportf_const.

  (* simpl makes it very slow *)
  (* simpl. *)
  etrans. apply id_right.
  apply pathsinv0.
  etrans. apply id_left.
    
  (* unfold three_mor11.
  cbn. *)
  
  use (section_disp_on_eq_morphisms F (γ := γ)); reflexivity.
Qed.

Definition Ff_l_id_left (F : Ff C) : (Ff_lcomp_unit ⊗ F) --> F :=
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
  
  etrans. use pr1_transportf_const.
  
  (* simpl makes it very slow *)
  (* simpl. *)
  etrans. apply id_right.
  apply pathsinv0.
  etrans. apply id_left.

  use section_disp_on_eq_morphisms; reflexivity.
Qed.

Definition Ff_l_id_left_rev (F : Ff C) : F --> (Ff_lcomp_unit ⊗ F) :=
    (_,, Ff_l_id_left_rev_axioms F).

Definition Ff_l_prewhisker_data (F : Ff C) {G G' : Ff C} (τ : section_nat_trans_disp G G') :
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
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use pr1_transportf_const.

  destruct τ as [τ τax].
  set (τcommf := base_paths _ _ (τax _ _ (#(fact_R F) γ))).
  apply pathsinv0.
  etrans. exact (pathsinv0 τcommf).
  etrans. use pr1_transportf_const.
  reflexivity.
Qed.

Definition Ff_l_prewhisker (F : Ff C) {G G'} (τ : G --> G') :
    (F ⊗ G) --> (F ⊗ G') :=
  (_,, Ff_l_prewhisker_axioms F τ).

Notation "F ⊗pre τ" := (Ff_l_prewhisker F τ) (at level 50).


Lemma Ff_l_prewhisker_id (F G : Ff C) :
    (F ⊗pre (identity G)) = identity _.
Proof.
  use section_nat_trans_eq; intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  reflexivity.
Qed.

Lemma Ff_l_prewhisker_comp (F : Ff C) {G G' G'' : Ff C}
    (τ : G --> G') (τ' : G' --> G'') :
  (F ⊗pre (τ · τ')) = (F ⊗pre τ) · (F ⊗pre τ').
Proof.
  use section_nat_trans_eq; intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  (* cbn makes it very slow *)
  (* cbn. *)

  etrans. use (pr1_transportf_const).
  apply pathsinv0.
  etrans. use (pr1_transportf_const).
  reflexivity.
Qed.

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
  
  etrans. use pr1_transportf_const.
  (* simpl.
  unfold three_mor11.
  cbn. *)

  etrans. use pr1_section_disp_on_morphisms_comp.
  apply pathsinv0.
  etrans. use pr1_section_disp_on_morphisms_comp.

  (* destruct τ as [τ τax]. *)
  (* unfold section_nat_trans_disp_axioms in τax. *)
  set (τcommf := base_paths _ _ 
                  ((section_nt_disp_axioms_from_section_nt_disp τ) _ _ γ)).

  use section_disp_on_eq_morphisms.
  - (* cbn makes it very slow *)
    (* cbn. *)
    etrans. exact (pathsinv0 τcommf).
    etrans. use pr1_transportf_const.
    reflexivity.
  - etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_right.
    reflexivity.
Qed.

Definition Ff_l_postwhisker {G G'} (τ : G --> G') (F : Ff C) :
    (G ⊗ F) --> (G' ⊗ F) :=
  (_,, Ff_l_postwhisker_axioms τ F).

Notation "τ ⊗post F" := (Ff_l_postwhisker τ F) (at level 50).

Lemma Ff_l_postwhisker_id (G F : Ff C) :
    ((identity G) ⊗post F) = identity _.
Proof.
  use section_nat_trans_eq; intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  (* cbn makes it very slow *)
  (* cbn. *)
  etrans. use (section_disp_on_eq_morphisms' F (γ := identity _)).
  etrans. apply maponpaths.
          use (section_disp_id F _).
  reflexivity.
Qed.

Local Lemma three_disp11_comp {x x' x'' : arrow C} {γ : x --> x'} (γ' : x' --> x'')
    {f : three_disp _ x} {f' : three_disp _ x'} {f'' : three_disp _ x''}
    (Γ : f -->[γ] f') (Γ' : f' -->[γ'] f'') :
  pr1 Γ · pr1 Γ' = pr1 (comp_disp Γ Γ').
Proof.
  reflexivity.
Qed.

Lemma Ff_l_postwhisker_comp {G G' G'' : Ff C}
    (τ : G --> G') (τ' : G' --> G'') (F : Ff C) :
  ((τ · τ') ⊗post F) = (τ ⊗post F) · (τ' ⊗post F).
Proof.
  use section_nat_trans_eq; intro f.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  apply pathsinv0.
  etrans. use (pr1_transportf_const).
  
  (* cbn. *)
  etrans. apply three_disp11_comp.
  etrans. use (pr1_section_disp_on_morphisms_comp F).
  
  use (section_disp_on_eq_morphisms F).
  - apply pathsinv0.
    etrans. use (pr1_transportf_const).
    reflexivity.
  - apply id_left.
Qed.

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
  
  etrans. use pr1_transportf_const.
  (* cbn makes it very slow *)
  (* cbn. *)
  etrans. apply id_right.
  apply pathsinv0.
  etrans. apply id_left.
  
  (* unfold three_mor11.
  simpl. *)

  use (section_disp_on_eq_morphisms F''); reflexivity.
Qed.

Definition Ff_l_assoc (F F' F'' : Ff C) :
    ((F ⊗ F') ⊗ F'') --> (F ⊗ (F' ⊗ F'')) :=
  (_,, Ff_l_assoc_axioms F F' F'').


Definition Ff_l_assoc_rev_data (F F' F'' : Ff C) :
    section_nat_trans_disp_data (F ⊗ (F' ⊗ F'')) ((F ⊗ F') ⊗ F'').
Proof.
  intro f.
  exists (identity _).
  abstract (
    split; rewrite id_left, id_right;
      [cbn; now rewrite assoc|reflexivity]
  ).
Defined.

Definition Ff_l_assoc_rev_axioms (F F' F'' : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_assoc_rev_data F F' F'').
Proof.
  intros f f' γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use pr1_transportf_const.
  (* cbn makes it very slow *)
  (* cbn. *)
  etrans. apply id_right.
  apply pathsinv0.
  etrans. apply id_left.
  
  (* unfold three_mor11.
  simpl. *)
  use section_disp_on_eq_morphisms.
  - cbn.
    reflexivity.
  - reflexivity.
Qed.

Definition Ff_l_assoc_rev (F F' F'' : Ff C) :
    (F ⊗ (F' ⊗ F'')) --> ((F ⊗ F') ⊗ F'') :=
  (_,, Ff_l_assoc_rev_axioms F F' F'').

(* todo: is this defined correctly? *)
Definition Ff_l_mor_comp {F F' G G' : Ff C} 
    (τ : F --> F') (ρ : G --> G') :
  (F ⊗ G) --> (F' ⊗ G').
Proof.
  exact ((τ ⊗post G) · (F' ⊗pre ρ)).
Defined.

Definition Ff_l_point_data (F : Ff C) :
    section_nat_trans_disp_data Ff_lcomp_unit F.
Proof.
  intro f.
  exists (fact_L F f).
  abstract (
    split; [
      now do 2 rewrite id_left|
      rewrite id_right;
      apply pathsinv0;
      exact (three_comp (fact_functor F f))
    ]
  ).
Defined.

Definition Ff_l_point_axioms (F : Ff C) :
    section_nat_trans_disp_axioms (Ff_l_point_data F).
Proof.
  intros f g γ.
  apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
  
  etrans. use (pr1_transportf (id_right γ @ ! id_left γ) _).
  cbn; rewrite transportf_const.
  exact (arrow_mor_comm (#(fact_L F) γ)).
Qed.

Definition Ff_l_point (F : Ff C) :
    Ff_lcomp_unit --> F :=
  (_,, Ff_l_point_axioms F).

End Ff_composition.


(* redefine notation *)
Notation "F ⊗ F'" := (Ff_lcomp F F').
Notation "F ⊗pre τ" := (Ff_l_prewhisker F τ) (at level 50).
Notation "τ ⊗post F" := (Ff_l_postwhisker τ F) (at level 50).
Notation "τ ⊗prod ρ" := (Ff_l_mor_comp τ ρ) (at level 50).