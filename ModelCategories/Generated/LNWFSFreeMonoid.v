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

Definition alg_forgetful_functor_right_action_unit_for_limit_data
    {T : LNWFSC} (X : LNWFS_alg T) :
  nat_trans_data (functor_identity _) (LNWFS_alg_right_action X ∙ LNWFS_alg_forgetful_functor T).
Proof.
  intro L.
  exact (LNWFS_tot_l_id_left_rev L · 
        (LNWFS_tot_l_point (pr1 X) Ltot⊗post L)).
Defined.

Definition alg_forgetful_functor_right_action_unit_for_limit_ax
    {T : LNWFSC} (X : LNWFS_alg T) :
  is_nat_trans _ _ (alg_forgetful_functor_right_action_unit_for_limit_data X).
Proof.
  (* intros L L' γ.
  use LNWFS_tot_mor_eq.
  intro f.
  simpl.
  etrans. use pr1_transportf_const.
  etrans. 
  {
    simpl.
    apply maponpaths.
    etrans. use pr1_transportf_const.
    reflexivity.
  }
  apply pathsinv0.
  etrans. use pr1_transportf_const.
  etrans. 
  {
    simpl.
    apply maponpaths_2.
    use pr1_transportf_const.
  }
  simpl.
  etrans. apply assoc'.
  etrans. apply id_left. *)
Admitted.

Definition alg_forgetful_functor_right_action_counit_for_limit_data
    {T : LNWFSC} (X : LNWFS_alg T) :
  nat_trans_data (LNWFS_alg_forgetful_functor T ∙ LNWFS_alg_right_action X) (functor_identity _).
Proof.
  intro L.
  (* X ⊗ L --> L *)
  simpl.
  (* I think the definition of free monoid says that there is a map
     I --> X which induces an iso on the algebras. The inverse should induce
     X ⊗ L --> I ⊗ L --> L *)
Admitted.

Definition alg_forgetful_functor_right_action_counit_for_limit_ax
    {T : LNWFSC} (X : LNWFS_alg T) :
  is_nat_trans _ _ (alg_forgetful_functor_right_action_counit_for_limit_data X).
Proof.

Admitted.

Definition alg_forgetful_functor_right_action_form_adjunction
    {T : LNWFSC} (X : LNWFS_alg T) :
  form_adjunction (LNWFS_alg_right_action X) (LNWFS_alg_forgetful_functor T)
    (_,, alg_forgetful_functor_right_action_unit_for_limit_ax X)
    (_,, alg_forgetful_functor_right_action_counit_for_limit_ax X).
Proof.

Admitted.




Lemma alg_forgetful_functor_right_action_is_adjoint_for_limit
    {T : LNWFSC} (X : LNWFS_alg T) (* seq on I --> X converges *) :
  alg_forgetful_functor_right_action_is_adjoint X.
Proof.
  use make_are_adjoints.
  - exact (_,, alg_forgetful_functor_right_action_unit_for_limit_ax X).
  - exact (_,, alg_forgetful_functor_right_action_counit_for_limit_ax X).
  - exact (alg_forgetful_functor_right_action_form_adjunction X).
Defined.

Definition alg_forgetful_functor_right_action_is_adjoint_induced_mul_data {T : LNWFSC} (X : LNWFS_alg T) 
    (Adj := alg_forgetful_functor_right_action_is_adjoint_for_limit X) :
  nat_trans_data (functor_composite (fact_R (pr11 X)) (fact_R (pr11 X))) (fact_R (pr11 X)).
Proof.
  intro f.
  set (n := Monad_from_adjunction Adj).
  set (μ := μ n LNWFS_tot_lcomp_unit).
  simpl in μ.
  set (μf := pr1 μ f).

  (* todo: make this into three -> arrow (select three_1212) *)
  use mors_to_arrow_mor.
  - exact (three_mor11 μf).
  - exact (identity _).
  - abstract (
      apply pathsinv0;
      exact (pr2 (three_mor_comm μf))
    ).
Defined.

Definition alg_forgetful_functor_right_action_is_adjoint_induced_mul_ax {T : LNWFSC} (X : LNWFS_alg T) 
    (Adj := alg_forgetful_functor_right_action_is_adjoint_for_limit X) :
  is_nat_trans _ _ (alg_forgetful_functor_right_action_is_adjoint_induced_mul_data X).
Proof.
  intros f g γ.

  set (n := Monad_from_adjunction Adj).
  set (μ := μ n LNWFS_tot_lcomp_unit).
  simpl in μ.
  set (μf := pr1 μ f).
  
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  + (* nat_trans_ax from μ *)
    (* cbn.
    unfold three_mor11.
    cbn. *)

    set (μax := nat_trans_ax (pr1 μ) _ _ γ).
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

Definition alg_forgetful_functor_right_action_is_adjoint_induced_mul {T : LNWFSC} (X : LNWFS_alg T) 
    (Adj := alg_forgetful_functor_right_action_is_adjoint_for_limit X) :
  (functor_composite (fact_R (pr11 X)) (fact_R (pr11 X))) ⟹ (fact_R (pr11 X)) :=
    (_,, alg_forgetful_functor_right_action_is_adjoint_induced_mul_ax X).

Lemma eq_section_nat_trans_disp_on_morphism
    {F F' : section_disp (three_disp C)}
    {γ γ' : section_nat_trans_disp F F'} :
  γ = γ' -> ∏ f, γ f = γ' f. 
Proof.
  intro H.
  now rewrite H.
Qed.

Definition pathscomp1 {X : UU} {a b x y : X} (e1 : a = b) (e2 : a = x) (e3 : b = y) : x = y.
Proof.
  induction e1. induction e2. apply e3.
Qed.

Lemma alg_forgetful_functor_right_action_is_adjoint_monad_laws {T : LNWFSC} (X : LNWFS_alg T) 
    (Adj := alg_forgetful_functor_right_action_is_adjoint_for_limit X) :
  Monad_laws (R_monad_data (pr11 X) (alg_forgetful_functor_right_action_is_adjoint_induced_mul X)).
Proof.
  set (n := Monad_from_adjunction Adj).
  set (μ := μ n LNWFS_tot_lcomp_unit).
  simpl in μ.

  (* this assumption is pretty much in line with one of the axioms
     in Grandis and Tholen. We need to know something about the adjunction for this though *)
  assert (HAdj : ∏ f, three_mor11 (#(fact_functor (pr11 X)) (c_10 C (fact_functor (pr11 X) f))) = 
                 (fact_L (pr11 X) (fact_R (pr11 X) f))).
  {
    admit.
  }
  (* transparent assert (frf : (∏ f, f --> fact_R (pr11 X) f)).
  {
    intro f.
    use mors_to_arrow_mor.
    - exact (fact_L (pr11 X) f).
    - exact (identity _).
    - abstract (
        rewrite id_right;
        exact (three_comp (fact_functor (pr11 X) f))
    ).
  } *)
  
  (* set (μax1 := @Monad_law1 _ n).
  set (μax1 := @Monad_law1 _ n).
  set (μax1 := @Monad_law1 _ n).
   *)
  repeat split; (intro f; apply subtypePath; [intro; apply homset_property|]).
  - apply pathsdirprod; [|apply id_left].
    set (μax1 := @Monad_law1 _ n LNWFS_tot_lcomp_unit).
    set (base_μax1 := base_paths _ _ μax1).
    set (μax1f := eq_section_nat_trans_disp_on_morphism base_μax1 f).
    set (μax1f11 := base_paths _ _ μax1f).

    apply pathsinv0.
    etrans. exact (pathsinv0 μax1f11).
    etrans. use pr1_transportf_const.
    apply cancel_postcomposition.

    etrans. use pr1_transportf_const.
    etrans. apply id_left.
    
    cbn.
    unfold three_mor01, three_mor11.
    cbn.

    apply pathsinv0.
    etrans. exact (pathsinv0 (HAdj f)).
    use section_disp_on_eq_morphisms; reflexivity.
  - apply pathsdirprod; [|apply id_left].
    set (μax2 := @Monad_law2 _ n LNWFS_tot_lcomp_unit).
    set (base_μax2 := base_paths _ _ μax2).
    set (μax2f := eq_section_nat_trans_disp_on_morphism base_μax2 f).
    set (μax2f11 := base_paths _ _ μax2f).

    apply pathsinv0.
    etrans. exact (pathsinv0 μax2f11).
    etrans. use pr1_transportf_const.
    apply cancel_postcomposition.

    (* cbn.
    unfold three_mor11.
    cbn. *)

    etrans. use pr1_transportf_const.
    etrans. apply id_left.
    exact (pathsinv0 (HAdj f)).
  - apply pathsdirprod; [|reflexivity].
    set (μax3 := @Monad_law3 _ n LNWFS_tot_lcomp_unit).
    set (base_μax3 := base_paths _ _ μax3).
    set (μax3f := eq_section_nat_trans_disp_on_morphism base_μax3 f).
    set (μax3f11 := base_paths _ _ μax3f).
    
    cbn.
    (* cbn in μax3f11. *)

    (* μax3f11 : pr1 (transportf ...) = pr1 (transportf ...) *)
    (* I think the issue here is that the adjunction does not lie
       over identity, so the functor in the monad is not actually 
       (pr11 X), but rather (pr11X L⊗ I) ... *)
    (* Search (transportf _ _ _ = _ -> _). *)
    use (pathscomp1 μax3f11).
    * etrans. use pr1_transportf_const.
      apply cancel_postcomposition.
      cbn.
      unfold three_mor11.
      simpl.
      
      admit.
    * etrans. use pr1_transportf_const.
      apply cancel_postcomposition.
      cbn.
      unfold three_mor11.
      simpl.

      admit.
    apply (pathscomp0 μax3f11).
    apply pr1_transportf_const in μax3f11.

    
    simpl in μax3f11.

    cbn.
    apply cancel_postcomposition.
    unfold three_mor11.
    cbn.

    unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul_data.
    



    unfold R_monad_data.
    unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul.
    unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul_data.
    


    cbn in μax3f11.
    exact (μax3f11).
    apply pathsinv0.
    etrans. exact (pathsinv0 μax3f11).
    etrans. use pr1_transportf_const.
    apply cancel_postcomposition.

    cbn.
    unfold three_mor11.
    cbn.





  set (μ := pr11 (counit_from_are_adjoints Adj X)).
  cbn in μ.
  (* triangle1 statement *)
  (* base_paths: T-Alg map -> LNWFS map -> FfC map *)
  (* set (tr1 := base_paths _ _ (base_paths _ _ ((pr12 Adj) (pr1 X)))).
  simpl in tr1.
   *)
  (* base_paths: T-Alg map -> LNWFS map -> FfC map *)
  set (tr2 := base_paths _ _ ((pr22 Adj) X)).
  (* simpl in tr2. *)

  assert (∏ f, pr1 (pr11 ((unit_from_are_adjoints Adj) (pr1 X)) f) =
          pr1 (section_disp_on_morphisms (pr111 X) (c_10_data C (f,, (pr111 X) f)))) as HAdj.
  {
    admit.
  }

  repeat split; (intro f; apply subtypePath; [intro; apply homset_property|]).
  - apply pathsdirprod; cbn.
    * unfold three_mor01.
      cbn.
      set (tr2f := eq_section_nat_trans_disp_on_morphism tr2 f).
      set (tr2f11 := base_paths _ _ tr2f).

      apply pathsinv0.
      etrans. exact (pathsinv0 tr2f11).
      etrans. use pr1_transportf_const.
      
      apply cancel_postcomposition.
      etrans. exact (HAdj f).
      
      (* ??? *)
      admit.
    * apply id_left.
  - apply pathsdirprod; cbn.
    * 
      set (tr2f := eq_section_nat_trans_disp_on_morphism tr2 f).
      set (tr2f11 := base_paths _ _ tr2f).

      apply pathsinv0.
      etrans. exact (pathsinv0 tr2f11).
      etrans. use pr1_transportf_const.

      apply cancel_postcomposition.
      cbn.
      unfold three_mor11.
      cbn.
      (* unfold c_10_data, three_mor11.
      cbn. *)

      (* 
        pr1 (pr11 ((unit_from_are_adjoints Adj) (pr1 X)) f)
        (this works to replace)
        pr1 (pr1 ((pr11 Adj) (pr1 X)) f)

        pr1: project from disp_mor (three_disp -->[] three_disp)
             to three_mor11
             
             pr1: select section_nat_trans_disp_data
                  
                  ((unit_from_are_adjoints Adj) (pr1 X))
                  component of unit of the adjunction at pr1 X
                  (this is a morphism of FfC, i.e. a natural transformation
                   of sections)

                      component at f

        must be equal to 
        pr1
          (section_disp_on_morphisms (pr11 X)
            (make_dirprod (three_mor01 (f,, (pr11 X) f)) (identity (pr21 f)),,
              c_10_data_subproof C (f,, (pr11 X) f)))

        pr1: idem

            (underlying Ff C of X) applied to
            (   λf
               ---->
              |     |
            f |     | ρf 
              v     v
               =====
            with λ and ρ corresponding to the 
            functorial factorization underlying X
            )
      ) *)

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
