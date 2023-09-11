Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.Generated.FFMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.LNWFSMonoidalStructure.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.

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

Lemma LNWFS_alg_action_alg_map_rel {T : LNWFSC} 
    (X : LNWFS_alg T) (A : LNWFSC) :
  LNWFS_tot_l_id_left_rev (pr1 X Ltot⊗ A)
  · (LNWFS_tot_l_point T Ltot⊗post (pr1 X Ltot⊗ A))
  · (LNWFS_tot_l_assoc_rev T (pr1 X) A · (pr12 X Ltot⊗post A)) =
  identity _.
Proof.
  (* this should hold, as all the involved middle morphisms
     are identity, sadly the terms become a bit too big... *)
  use LNWFS_tot_mor_eq.
  intro f.
  (* todo: make Ff_comp: (F · F') f = F f · F' f lemma *)
Admitted.

Lemma LNWFS_alg_action_mor_rel {T : LNWFSC} (X : LNWFS_alg T)
    {A B : LNWFSC} (f : A --> B) :
  LNWFS_alg_mor_axioms 
      (_,, LNWFS_alg_action_alg_map_rel X A)  
      (_,, LNWFS_alg_action_alg_map_rel X B)
      ((pr1 X) Ltot⊗pre f).   
Proof.
  (* this should hold *)
Admitted.

Definition LNWFS_alg_right_action_data {T : LNWFSC} (X : LNWFS_alg T) :
  functor_data LNWFSC (LNWFS_alg T).
Proof.
  use make_functor_data.
  - intro A.
    exists ((pr1 X) Ltot⊗ A).
    cbn.
    unfold LNWFS_alg_data.
    exists ((LNWFS_tot_l_assoc_rev T (pr1 X) A) · ((pr12 X) Ltot⊗post A)).
    apply LNWFS_alg_action_alg_map_rel.
  - intros A B f.
    simpl.
    exists ((pr1 X) Ltot⊗pre f).
    exact (LNWFS_alg_action_mor_rel X f).
Defined.

Definition LNWFS_alg_right_action_axioms {T : LNWFSC} (X : LNWFS_alg T) :
    is_functor (LNWFS_alg_right_action_data X).
Proof.
  split.
  - intro x.
    apply subtypePath; [intro; apply isaprop_LNWFS_alg_mor_axioms|].
    apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    etrans. apply Ff_l_prewhisker_id.
    reflexivity.
  - intros A B D f g.
    apply subtypePath; [intro; apply isaprop_LNWFS_alg_mor_axioms|].
    apply subtypePath; [intro; apply isaprop_lnwfs_mor_axioms|].
    etrans. apply Ff_l_prewhisker_comp.
    reflexivity.
Qed.

Definition LNWFS_alg_right_action {T : LNWFSC} (X : LNWFS_alg T) :
    functor LNWFSC (LNWFS_alg T) :=
  (_,, LNWFS_alg_right_action_axioms X).

(* basically want to formalize Garner / Kelly (generalized) stuff about
   T-Alg (/ T-Mod in Garner)
   and how one obtains a monoid from the free T-algebra
   LNWFS should be a monoidal category (Ff_C) is at least
*)
Lemma LNWFS_induced_alg_map_rel {T S A : LNWFSC} (F : T --> S)
    (a : LNWFS_alg_disp S A) : 
    LNWFS_tot_l_id_left_rev (functor_identity LNWFSC A)
    · (LNWFS_tot_l_point T Ltot⊗post functor_identity LNWFSC A)
    · ((F Ltot⊗post A) · (LNWFS_alg_map a)) = identity (functor_identity LNWFSC A).
Proof.

Admitted.

Lemma LNWFS_induced_alg_map_mor_rel {T S A B : LNWFSC} (F : T --> S)
    {a : LNWFS_alg_disp S A} {b : LNWFS_alg_disp S B} {f : A --> B}
    (ff : LNWFS_alg_mor_axioms a b f) :
  ((F Ltot⊗post A) · (LNWFS_alg_map a)) · f = (T Ltot⊗pre f) · ((F Ltot⊗post B) · (LNWFS_alg_map b)).
Proof.

Admitted.

Definition LNWFS_induced_alg_map_data {T S : LNWFSC} (F : T --> S) :
    disp_functor_data (functor_identity _) (LNWFS_alg_disp S) (LNWFS_alg_disp T).
Proof.
  use tpair.
  - intros A a.
    exists ((F Ltot⊗post A) · (LNWFS_alg_map a)).
    apply LNWFS_induced_alg_map_rel.
  - simpl.
    intros A B a b f ff.
    unfold LNWFS_alg_mor_axioms.
    apply LNWFS_induced_alg_map_mor_rel.
    unfold LNWFS_alg_mor_axioms.
    exact ff.
Defined.

Definition LNWFS_induced_alg_map_axioms {T S : LNWFSC} (F : T --> S) :
    disp_functor_axioms (LNWFS_induced_alg_map_data F).
Proof.
  use tpair; simpl; intros; apply isaprop_LNWFS_alg_mor_axioms.
Qed.

Definition LNWFS_induced_alg_map {T S : LNWFSC} (F : T --> S) :
    disp_functor (functor_identity _) (LNWFS_alg_disp S) (LNWFS_alg_disp T) :=
  (_,, LNWFS_induced_alg_map_axioms F).

Definition NWFS_forgetful_functor : 
    disp_functor (functor_identity _) (NWFS C) (LNWFS C) :=
  dirprodpr1_disp_functor (LNWFS C) (RNWFS C).

(* define NWFS_alg as disp_cat over LNWFS_alg with
   "associativity axiom" (Kelly, par 22.1)
   then free monoid as NWFS with equivalence of alg- categories 
   
   I think equivalence should be sufficient, as opposed to
   iso, since we care about the retract closure of the algebras
   in the end anyway?

   if we do not care about cofibrantly generated, we can skip
   this NWFS-alg stuff definition for now, and just show
   that the NWFS exists.
*)

Definition LNWFS_alg_forgetful_functor (T : LNWFSC) :
    functor (LNWFS_alg T) LNWFSC :=
  pr1_category _.

(* todo: show that this holds whenever sequence on I --> X
   converges *)
Definition alg_forgetful_functor_right_action_is_adjoint {T : LNWFSC} (X : LNWFS_alg T) : UU :=
    are_adjoints (LNWFS_alg_right_action X) (LNWFS_alg_forgetful_functor T).  

Lemma alg_forgetful_functor_right_action_is_adjoint_for_limit
    {T : LNWFSC} (X : LNWFS_alg T) (* seq on I --> X converges *) :
  alg_forgetful_functor_right_action_is_adjoint X.
Proof.
  use make_are_adjoints.
  - (* todo: define ..._left_adj *)
    admit.
  - (* todo: define ..._right_adj *)
    admit.
  - (* todo: lemma ..._form_adjunction Qed. *)
    admit.
Admitted.

Definition alg_forgetful_functor_right_action_is_adjoint_induced_mul_data {T : LNWFSC} {X : LNWFS_alg T} 
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :
  nat_trans_data (functor_composite (fact_R (pr11 X)) (fact_R (pr11 X))) (fact_R (pr11 X)).
Proof.
  intro f.
  set (μ := pr11 (counit_from_are_adjoints Adj X)).
  cbn in μ.
  set (μf := μ f).
  (* todo: make this into three -> arrow (select three_1212) *)
  use mors_to_arrow_mor.
  - exact (three_mor11 μf).
  - exact (identity _).
  - abstract (
      apply pathsinv0;
      exact (pr2 (three_mor_comm μf))
    ).
Defined.

Definition alg_forgetful_functor_right_action_is_adjoint_induced_mul_ax {T : LNWFSC} {X : LNWFS_alg T} 
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :
  is_nat_trans _ _ (alg_forgetful_functor_right_action_is_adjoint_induced_mul_data Adj).
Proof.
  intros f g γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  + cbn.
    (* nat_trans_ax from μ *)
    unfold three_mor11.
    cbn.
    set (μ := pr11 (counit_from_are_adjoints Adj X)).
    cbn in μ.
    set (μf := μ f).
    set (μax := nat_trans_ax μ _ _ γ).
    set (μax11_path := base_paths _ _ (pathsinv0 (fiber_paths μax))).
    apply pathsinv0.
    etrans. exact μax11_path.
    etrans. use pr1_transportf_const.
    reflexivity.
  + (* this also follows from μ's axioms, but
       it is trivial, since those morphisms are always identity *)
    rewrite id_left, id_right.
    reflexivity.
Qed.

Definition alg_forgetful_functor_right_action_is_adjoint_induced_mul {T : LNWFSC} {X : LNWFS_alg T} 
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :
  (functor_composite (fact_R (pr11 X)) (fact_R (pr11 X))) ⟹ (fact_R (pr11 X)) :=
    (_,, alg_forgetful_functor_right_action_is_adjoint_induced_mul_ax Adj).

Lemma eq_section_nat_trans_disp_on_morphism
    {F F' : section_disp (three_disp C)}
    {γ γ' : section_nat_trans_disp F F'} :
  γ = γ' -> ∏ f, γ f = γ' f. 
Proof.
  intro H.
  now rewrite H.
Qed.

Lemma alg_forgetful_functor_right_action_is_adjoint_monad_laws {T : LNWFSC} {X : LNWFS_alg T} 
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :
  Monad_laws (R_monad_data (pr11 X) (alg_forgetful_functor_right_action_is_adjoint_induced_mul Adj)).
Proof.
  set (μ := pr11 (counit_from_are_adjoints Adj X)).
  cbn in μ.
  (* triangle1 statement *)
  (* base_paths: T-Alg map -> LNWFS map -> FfC map *)
  set (tr1 := base_paths _ _ (base_paths _ _ ((pr12 Adj) (pr1 X)))).
  simpl in tr1.
  (* set (tr2 := base_paths _ _ (base_paths _ _ ((pr22 Adj) X))). *)

  repeat split; (intro f; apply subtypePath; [intro; apply homset_property|]).
  - apply pathsdirprod; cbn.
    * unfold three_mor01.
      cbn.
      set (t := eq_section_nat_trans_disp_on_morphism tr1 f).
      set (t' := base_paths _ _ t).
      unfold three_ob1.
      simpl.
      admit.
    * apply id_left.
  - apply pathsdirprod; cbn.
    * 
      admit.
    * apply id_left.
  - apply pathsdirprod; cbn.
    * cbn.
      apply cancel_postcomposition.
      unfold three_mor11.
      cbn.
      unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul_data.
      cbn.
      admit.
    * reflexivity.
Admitted.

(* todo: define free monoid *)
Lemma alg_free_monad_exists_if_alg_forgetful_functor_right_action_is_adjoint {T : LNWFSC} (X : LNWFS_alg T) :
    alg_forgetful_functor_right_action_is_adjoint X -> (total_category (NWFS C)).
Proof.
  intro Adj.

  exists (pr11 X).
  split; [exact (pr21 X)|].
  exists (alg_forgetful_functor_right_action_is_adjoint_induced_mul Adj).
  exact (alg_forgetful_functor_right_action_is_adjoint_monad_laws Adj).
Defined.
