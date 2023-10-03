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

Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import CategoryTheory.Chains.Chains.
Require Import CategoryTheory.limits.colimits.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.

Local Open Scope cat.
Local Open Scope Cat.
Local Open Scope morcls.


Local Ltac functorial_factorization_eq f := (
  apply subtypePath; [intro; apply isaprop_section_nat_trans_disp_axioms|];
  use funextsec;
  intro f;
  use subtypePath; [intro; apply isapropdirprod; apply homset_property|]
).

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
  (* cbn. *)
  set (τρf := τ (fact_R F f)).
  destruct τρf as [mor [comm1 comm2]].
  exists (mor).
  abstract (
    split; cbn; [
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
    split; 
      (etrans; [apply id_right|];
       apply pathsinv0;
       etrans; [apply id_left|]); 
          [apply assoc|reflexivity]
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
    split; 
      (etrans; [apply id_right|];
       apply pathsinv0;
       etrans; [apply id_left|]); 
          [apply assoc'|reflexivity]
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
  use section_disp_on_eq_morphisms; reflexivity.
Qed.

Definition Ff_l_assoc_rev (F F' F'' : Ff C) :
    (F ⊗ (F' ⊗ F'')) --> ((F ⊗ F') ⊗ F'') :=
  (_,, Ff_l_assoc_rev_axioms F F' F'').

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


Require Import CategoryTheory.Monoidal.Categories.

Section Ff_monoidal.

Context {C : category}.

Definition Ff_tensor_data : tensor_data (Ff C).
Proof.
  use tpair.
  - exact (Ff_lcomp).
  - split.
    * exact (Ff_l_prewhisker).
    * exact (λ b _ _ γ, Ff_l_postwhisker γ b).
Defined.

Definition Ff_monoidal_data : monoidal_data (Ff C).
Proof.
  use make_monoidal_data.
  - exact Ff_tensor_data.
  - exact Ff_lcomp_unit.
  - exact Ff_l_id_left.
  - exact Ff_l_id_left_rev.
  - exact Ff_l_id_right.
  - exact Ff_l_id_right_rev.
  - exact Ff_l_assoc.
  - exact Ff_l_assoc_rev.
Defined.

Definition Ff_monoidal_laws : monoidal_laws Ff_monoidal_data.
Proof.
  repeat split.
  - intros F F'.
    functorial_factorization_eq f.
    reflexivity.
  - intros F F'.
    functorial_factorization_eq f.
    cbn.
    etrans. use (section_disp_on_eq_morphisms F (γ' := identity _)); reflexivity. 
    etrans. apply maponpaths. apply (section_disp_id F).
    reflexivity.
  - intros A F F' F'' γ γ'.
    functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    reflexivity.
  - intros A F F' F'' γ γ'.
    functorial_factorization_eq f.
    (* cbn. *)
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    (* cbn. *)
    etrans. use (pr1_section_disp_on_morphisms_comp A).
    use (section_disp_on_eq_morphisms A).
    * apply pathsinv0.
      etrans. use pr1_transportf_const.
      reflexivity.
    * apply id_left.
  - intros A F F' F'' γ γ'.
    functorial_factorization_eq f.
    (* cbn. *)
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    cbn.
    transparent assert (mor : (fact_R A f --> fact_R F f)).
    {
      set (γf := (section_nat_trans_data_from_section_nat_trans_disp_funclass γ) f).
      (* simpl in γf. *)
      use mors_to_arrow_mor.
      - exact (pr1 γf).
      - exact (identity _).
      - exact (pathsinv0 (pr22 γf)).
    }
    set (γ'naturality := section_nt_disp_axioms_from_section_nt_disp γ').
    set (γ'natf := γ'naturality _ _ mor).
    set (γ'natfb := base_paths _ _ γ'natf).
    etrans. apply maponpaths.
            use (section_disp_on_eq_morphisms F'' (γ' := mor)); reflexivity.
            
    etrans. exact (pathsinv0 γ'natfb).
    etrans. use pr1_transportf_const.
    apply cancel_postcomposition.
    use (section_disp_on_eq_morphisms F'); reflexivity.
  - intros F F' γ.
    functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    (* cbn. *)
    etrans. apply id_left.
    apply pathsinv0.
    etrans. apply id_right.
    reflexivity.
  - functorial_factorization_eq f.
    (* cbn. *)
    etrans. use pr1_transportf_const.
    apply id_left.
  - functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply id_left.
  - intros F F' γ.
    functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_left.
    apply pathsinv0.
    apply id_right.
  - functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply id_left.
  - functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply id_left.
  - intros A F F' F'' γ.
    functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_right.
    apply pathsinv0.
    apply id_left.
  - intros A F F' F'' γ.
    functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply id_left.
    use (section_disp_on_eq_morphisms F''); reflexivity.
  - intros A F F' F'' γ.
    functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply id_left.
    use (section_disp_on_eq_morphisms F''); reflexivity.
  - functorial_factorization_eq f. 
    etrans. use pr1_transportf_const.
    apply id_left.
  - functorial_factorization_eq f. 
    etrans. use pr1_transportf_const.
    apply id_left.
  - intros F F'.
    functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    etrans. apply id_left.
    apply pathsinv0.
    (* cbn. *)
    etrans. use (section_disp_on_eq_morphisms F' (γ' := identity _)); reflexivity.
    etrans. apply maponpaths.
            apply (section_disp_id F').
    reflexivity.
  - intros A F F' F''.
    functorial_factorization_eq f.
    etrans. use pr1_transportf_const.
    etrans. apply cancel_postcomposition.
            use pr1_transportf_const.
    etrans. apply id_right.
    etrans. apply id_right.

    apply pathsinv0.
    etrans. use pr1_transportf_const.
    etrans. apply id_left.
    apply pathsinv0.

    etrans. use (section_disp_on_eq_morphisms F'' (γ' := identity _)); reflexivity.
    etrans. apply maponpaths.
            apply (section_disp_id F'').
    reflexivity.
Qed.

Definition Ff_monoidal : monoidal (Ff C) :=
    (_,, Ff_monoidal_laws).

End Ff_monoidal.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.

Section Ff_monoid_is_RNWFS.

Context {C : category}.


Definition Ff_monoid_is_RNWFS_mul_data 
    {F : Ff C} (R : monoid (Ff_monoidal) F) :
  nat_trans_data (functor_composite (fact_R F) (fact_R F)) (fact_R F).
Proof.
  intro f.

  set (μ := monoid_data_multiplication _ R).
  set (μf := (section_nat_trans_data_from_section_nat_trans_disp_funclass μ) f).
  
  use mors_to_arrow_mor.
  - exact (pr1 μf).
  - exact (identity _).
  - exact (pathsinv0 (pr22 μf)).
Defined.

Lemma Ff_monoid_is_RNWFS_mul_axioms 
    {F : Ff C} (R : monoid (Ff_monoidal) F) :
  is_nat_trans _ _ (Ff_monoid_is_RNWFS_mul_data R).
Proof.
  intros f f' γ.

  set (μ := monoid_data_multiplication _ R).
  set (μaxγ := (section_nt_disp_axioms_from_section_nt_disp μ) _ _ γ).
  set (μaxγb := base_paths _ _ μaxγ).
  
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - (* cbn.
    cbn in μaxγb. *)
    apply pathsinv0.
    etrans. exact (pathsinv0 μaxγb).
    etrans. use pr1_transportf_const.
    apply cancel_postcomposition.
    use (section_disp_on_eq_morphisms F); reflexivity.
  - etrans. apply id_right.
    apply pathsinv0.
    etrans. apply id_left.
    reflexivity.
Qed.

Definition Ff_monoid_is_RNWFS_mul 
      {F : Ff C} (R : monoid (Ff_monoidal) F) :
    (functor_composite (fact_R F) (fact_R F)) ⟹ (fact_R F) :=
  (_,, Ff_monoid_is_RNWFS_mul_axioms R).

Local Definition pathscomp1 {X : UU} {a b x y : X} (e1 : a = b) (e2 : a = x) (e3 : b = y) : x = y.
Proof.
  induction e1. induction e2. apply e3.
Qed.

Definition Ff_monoid_RNWFS_base_condition 
    {F : Ff C} (R : monoid (Ff_monoidal) F) : UU :=
  ∏ f, pr1 (section_nat_trans_data_from_section_nat_trans_disp_funclass (monoid_data_unit Ff_monoidal R) f) = fact_L F f.

Definition Ff_monoid_RNWFS_condition 
    {F : Ff C} (R : monoid (Ff_monoidal) F) : UU :=
  monoid_data_unit Ff_monoidal R = Ff_l_point F.

Lemma Ff_monoid_RNWFS_base_condition_iff_cond 
    {F : Ff C} (R : monoid (Ff_monoidal) F) :
  Ff_monoid_RNWFS_base_condition R <-> Ff_monoid_RNWFS_condition R.
Proof.
  split.
  - intro H.
    functorial_factorization_eq f.
    exact (H f).
  - intros H f.
    set (Hf := eq_section_nat_trans_disp_on_morphism H f).
    exact (base_paths _ _ Hf).
Qed.

Lemma Ff_monoid_is_RNWFS_monad_laws 
    {F : Ff C} (R : monoid (Ff_monoidal) F) 
    (H : Ff_monoid_RNWFS_condition R) :
  Monad_laws (R_monad_data F (Ff_monoid_is_RNWFS_mul R)).
Proof.
  set (μ := monoid_data_multiplication _ R).
  
  repeat split.
  - intro f.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [|apply id_left].
    
    set (μax := monoid_to_unit_right_law _ R).
    set (μf := (section_nat_trans_data_from_section_nat_trans_disp_funclass μ) f).
    set (μaxf := eq_section_nat_trans_disp_on_morphism μax f).
    set (μaxfb := base_paths _ _ μaxf).
    
    apply pathsinv0.
    etrans. exact (pathsinv0 μaxfb).
    etrans. use pr1_transportf_const.

    apply cancel_postcomposition.
    (* cbn. *)
    (* this is the unit condition we need, applied to fact_R F f *)
    exact (pr2 (Ff_monoid_RNWFS_base_condition_iff_cond R) H (fact_R F f)).
  - intro f.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [|apply id_left].

    set (μax := monoid_to_unit_left_law _ R).
    set (μf := (section_nat_trans_data_from_section_nat_trans_disp_funclass μ) f).
    set (μaxf := eq_section_nat_trans_disp_on_morphism μax f).
    set (μaxfb := base_paths _ _ μaxf).

    apply pathsinv0.
    etrans. exact (pathsinv0 μaxfb).
    etrans. use pr1_transportf_const.

    apply cancel_postcomposition.
    set (mor := Λ F f).
    etrans. use (section_disp_on_eq_morphisms F (γ' := mor)).
    * (* this is the unit condition we need *)
      (* cbn. *)
      exact (pr2 (Ff_monoid_RNWFS_base_condition_iff_cond R) H f).
    * reflexivity.
    * reflexivity.
  - intro f.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; [|reflexivity].

    set (μax := monoid_to_assoc_law _ R).
    set (μf := (section_nat_trans_data_from_section_nat_trans_disp_funclass μ) f).
    set (μaxf := eq_section_nat_trans_disp_on_morphism μax f).
    set (μaxfb := base_paths _ _ μaxf).

    use (pathscomp1 (pathsinv0 μaxfb)).
    * etrans. use pr1_transportf_const.
      (* cbn.
      unfold three_mor11.
      cbn. *)
      apply cancel_postcomposition.
      use (section_disp_on_eq_morphisms F); reflexivity.
    * etrans. use pr1_transportf_const.
      etrans. apply cancel_postcomposition.
              use pr1_transportf_const.
      
      etrans. apply assoc'.
      etrans. apply id_left.
      
      reflexivity.
Qed.

Definition Ff_monoid_is_RNWFS 
      {F : Ff C} (R : monoid (Ff_monoidal) F)
      (H : Ff_monoid_RNWFS_condition R) :
    rnwfs_over F.
Proof.
  exists (Ff_monoid_is_RNWFS_mul R).
  exact (Ff_monoid_is_RNWFS_monad_laws R H).
Defined.

End Ff_monoid_is_RNWFS.

Section Ff_cocomplete.

Context {C : category}.
Context (CC : Colims C).

Section Ff_cocomplete_diagram.

Context {g : graph} (D : diagram g (Ff C)).
Context (H : is_connected g).

(* diagram of middle objects *)
Local Definition diagram_pointwise (a : arrow C) : diagram g C.
Proof.
  use tpair.
  - intro v.
    exact (pr1 (pr1 (dob D v) a)).
  - intros u v e.
    exact (pr1 (pr1 (dmor D e) a)).
Defined.

Local Definition HCg : ∏ (a : arrow C), ColimCocone (diagram_pointwise a) :=
    λ a, CC _ _.

(* this construction only works for non-empty graphs, since
   we need an arrow arrow_dom a --> colim (HCg a), 
   but we can only find this for a non-empty graph *)
Definition ColimFf_ob (v0 : vertex g) (a : arrow C) : three_disp C a.
Proof.
  exists (colim (HCg a)).

  exists (pr12 (pr1 (dob D v0) a) · (colimIn (HCg a) v0)).
  use tpair.
  - use colimArrow.
    use make_cocone.
    + intro v.
      exact (pr122 (pr1 (dob D v) a)).
    + intros u v e.
      etrans. exact (pathsinv0 (pr22 (pr1 (dmor D e) a))).
      apply id_right.
  - (* cbn. *)
    abstract (
      etrans; [apply assoc'|];
      etrans; [apply cancel_precomposition;
              use (colimArrowCommutes (HCg a))|];
      (* cbn. *)
      exact (three_comp (fact_functor (dob D v0) a))
    ).
Defined.

Definition ColimFf_mor (v0 : vertex g)
    {a b : arrow C} (f : a --> b) :
  ColimFf_ob v0 a -->[f] ColimFf_ob v0 b.
Proof.
  use tpair.
  - use colimOfArrows.
    * intro v.
      (* cbn. *)
      set (Dv := (dob D v)).
      exact (pr1 ((section_disp_on_morphisms (section_disp_data_from_section_disp Dv)) f)).
    * intros u v e.
      (* cbn. *)
      abstract (
        set (De := (dmor D e));
        set (Deax := section_nt_disp_axioms_from_section_nt_disp De _ _ f);
        etrans; [exact (pathsinv0 (base_paths _ _ Deax))|];
        etrans; [apply pr1_transportf_const|];
        reflexivity
      ).
  - (* functorality of dob D v *)
    split.
    * (* cbn. *)
      abstract (
        set (Dv0f := ((section_disp_on_morphisms (section_disp_data_from_section_disp (dob D v0))) f));
        set (Dv0fax := pr2 Dv0f);
        etrans; [apply assoc'|];
        etrans; [apply cancel_precomposition;
                 use (colimArrowCommutes (HCg a))|];
        
        etrans; [apply assoc|];
        apply pathsinv0;
        etrans; [apply assoc|];
        apply cancel_postcomposition;
        exact (pathsinv0 (pr1 Dv0fax))
      ).
    * (* cbn. *)

      abstract (
        etrans; [use postcompWithColimArrow|];
        apply pathsinv0;
        etrans; [use precompWithColimOfArrows|];
        apply maponpaths;
        use cocone_paths;
        intro v;
        (* cbn. *)
        set (Dvf := ((section_disp_on_morphisms (section_disp_data_from_section_disp (dob D v))) f));
        set (Dvfax := pr2 Dvf);
  
        exact (pathsinv0 (pr2 Dvfax))
      ).
Defined.

Definition ColimFf_data (v0 : vertex g) : section_disp_data (three_disp C) :=
    (_,, @ColimFf_mor v0).

Lemma ColimFf_axioms (v0 : vertex g) : section_disp_axioms (ColimFf_data v0).
Proof.
  split.
  - intro a.
    use subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    apply pathsinv0, colim_endo_is_identity; intro u.
    (* cbn. *)
    etrans. use (colimOfArrowsIn _ _ (HCg a)).
    (* cbn. *)
    etrans. apply cancel_postcomposition.
            apply maponpaths.
            exact (section_disp_id (dob D u) _).
    apply id_left.
  - intros a b c fab fbc.
    use subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    (* cbn. *)
    apply pathsinv0.
    etrans. apply precompWithColimOfArrows.
    apply pathsinv0, colimArrowUnique.
    intro u.
    etrans. apply colimOfArrowsIn.

    apply pathsinv0.
    etrans. apply assoc.
    apply cancel_postcomposition.

    etrans. apply pr1_section_disp_on_morphisms_comp.
    reflexivity.
Qed.

Definition ColimFf (v0 : vertex g) : Ff C := 
    (_,, ColimFf_axioms v0).

(* we need an edge from v0 to v for this to work,
   regarding equality of (arrow_dom v/v0 · colimIn v/v0) *)
Local Definition colim_nat_trans_in_data 
      {v0 : vertex g} {v : vertex g} : 
    dob D v --> ColimFf v0.
Proof.
  use tpair.
  - intro a.
    exists (colimIn (HCg a) v).
    split.
    * (* unfold ColimFf. *)
      (* cbn. *)
      abstract (
        apply pathsinv0;
        etrans; [apply id_left|];
        set (predicate := λ v, pr12 (pr1 (ColimFf v0) a) = pr12 (pr1 (dob D v) a) · colimIn (HCg a) v);
        use (connected_graph_zig_zag_strong_induction v0 H predicate); [reflexivity|];
        intros u u' Hu uu';
        induction uu' as [e|e]; (etrans; [exact Hu|]);
          [|apply pathsinv0];
          (etrans; [apply cancel_precomposition;
                 exact (pathsinv0 (colimInCommutes (HCg a) _ _ e))|];
           etrans; [apply assoc|];
           apply cancel_postcomposition;
           etrans; [exact (pr12 (pr1 (dmor D e) a))|];
           apply id_left)
      ).
    * abstract (
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply (colimArrowCommutes (HCg a))|];
        reflexivity
      ).
  - abstract (
      intros a b f;
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|];
      etrans; [use pr1_transportf_const|];
      apply pathsinv0;
      (* cbn. *)
      etrans; [apply (colimOfArrowsIn _ _ (HCg a))|];
      reflexivity
    ).
Defined.

Local Definition cocone_pointwise (F : Ff C) (cc : cocone D F) a :
  cocone (diagram_pointwise a) (pr1 (pr1 F a)).
Proof.
  use make_cocone.
  - intro v.
    exact (pr1 (pr1 (coconeIn cc v) a)).
  - abstract (
      intros u v e;
      (* cbn. *)
      set (cccomm_pointwise := eq_section_nat_trans_disp_on_morphism (coconeInCommutes cc _ _ e) a);
      apply pathsinv0;
      etrans; [exact (pathsinv0 (base_paths _ _ cccomm_pointwise))|];
      etrans; [use pr1_transportf_const|];
      reflexivity
    ).
Defined.

Definition ColimFf_unique_mor
    (v0: vertex g)
    (F : Ff C) (cc : cocone D F) :
  ColimFf v0 --> F.
Proof.
  use tpair.
  * intro a.
    exists (colimArrow (HCg a) _ (cocone_pointwise F cc a)).
    split.
    + abstract (
        (* cbn. *)
        etrans; [apply assoc'|];
        etrans; [apply cancel_precomposition;
                 apply (colimArrowCommutes (HCg a))|];
        apply pathsinv0;
        etrans; [apply id_left|];
        apply pathsinv0;
        (* cbn. *)
        etrans; [exact (pr12 (pr1 (coconeIn cc v0) a))|];
        apply id_left
      ).
    + abstract (
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply postcompWithColimArrow|];
        apply maponpaths;
        use cocone_paths;
        intro u;
        (* cbn. *)
        (* naturality of coconeIn cc at u *)
        etrans; [exact (pathsinv0 (pr22 (pr1 (coconeIn cc u) a)))|];
        apply id_right
      ).
  * abstract (
      intros a b f;
      apply subtypePath; [intro; apply isapropdirprod; apply homset_property|];
      etrans; [use pr1_transportf_const|];
      etrans; [apply precompWithColimOfArrows|];
      apply pathsinv0;
      etrans; [apply postcompWithColimArrow|];

      use colimArrowUnique;
      intro u;
      etrans; [apply (colimArrowCommutes (HCg a))|];
      (* cbn. *)
  
      set (ccuf := (section_nt_disp_axioms_from_section_nt_disp (coconeIn cc u)) _ _ f);
      etrans; [exact (pathsinv0 (base_paths _ _ ccuf))|];
      etrans; [use pr1_transportf_const|];
      reflexivity
    ).
Defined.

Lemma ColimFf_unique
    {v0 : vertex g}
    (F : Ff C) (cc : cocone D F) :
  ∃! x : ColimFf v0 --> F,
            ∏ v, colim_nat_trans_in_data · x = coconeIn cc v.
Proof.
  use unique_exists.
  - exact (ColimFf_unique_mor v0 F cc).
  - abstract (
      intro v;
      functorial_factorization_eq a;
      etrans; [use pr1_transportf_const|];
      etrans; [apply (colimArrowCommutes (HCg a))|];
      reflexivity
    ).
  - abstract (
      intro; apply impred; intro; apply homset_property
    ).
  - abstract (
      intros f t;
      functorial_factorization_eq a;
      apply colimArrowUnique;
      intro u;
      (* cbn. *)
      set (tax := eq_section_nat_trans_disp_on_morphism (t u) a);
      apply pathsinv0;
      etrans; [exact (pathsinv0 (base_paths _ _ tax))|];
      etrans; [use pr1_transportf_const|];
      reflexivity
    ).
Defined.

Lemma ColimFfCocone
    {v0 : vertex g} :
  ColimCocone D.
Proof.
  use make_ColimCocone.
  - exact (ColimFf v0).
  - use make_cocone.
    * intro v. exact (colim_nat_trans_in_data).
    * abstract (
        intros u v e;
        functorial_factorization_eq a;
        etrans; [use pr1_transportf_const|];
        (* cbn. *)
        apply (colimInCommutes (HCg a))
      ).
  - intros F cc; exact (ColimFf_unique _ cc).
Defined.

End Ff_cocomplete_diagram.

Lemma ChainsFf (HC : Colims C) : 
    Chains (Ff C).
Proof.
  intros d.
  use (ColimFfCocone d).
  - use (is_connected_pointed nat_graph 0).
    intro v.
    induction v as [|v Hv].
    * exists 0.
      reflexivity.
    * use (append_graph_zig_zag Hv).
      exists 1.
      exists (S v).
      split.
      + apply inl.
        reflexivity.
      + reflexivity.
  - exact 0.
Defined.


Lemma CoequalizersFf (HC : Colims C) :
    Coequalizers (Ff C).
Proof.
  intros F G f g.
  use (ColimFfCocone).
  - use (is_connected_pointed Coequalizer_graph (● 0)%stn).
    intro v.
    induction v as [v v2].
    induction v as [|v Hv].
    * exists 0.
      apply subtypePath; [intro; apply propproperty|].
      reflexivity.
    * induction v as [|v Hv2]; [|induction (nopathsfalsetotrue v2)].
      exists 1.
      exists (● 1)%stn.
      split.
      + do 2 apply inl.
        exact tt.
      + apply subtypePath; [intro; apply propproperty|].
        reflexivity.
  - exact (● 0)%stn.
Defined.

End Ff_cocomplete.