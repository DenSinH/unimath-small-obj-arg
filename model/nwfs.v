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

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
(* The Structure Identity Principle (HoTT book, chapter 9.8) *)
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.

From Model Require Import morphism_class.
From Model.model Require Import wfs.

Local Open Scope cat.
Local Open Scope mor_disp.

(* This based on an "examples" file, not sure if we want to use
that or just roll our own.
The code in the examples file seems to no longer work... *)
(* UniMath/CategoryTheory/DisplayedCats/Examples.v *)
Section Arrow_Disp.

Context (C:category).

Definition arrow_base := category_binproduct C C.

Definition arrow_disp : disp_cat arrow_base.
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ xy, pr1 xy --> pr2 xy).
  - simpl.
    intros xx' yy' g h ff'.
    exact (pr1 ff' · h = g · pr2 ff').
  - simpl.
    intros.
    use homset_property.
  - simpl. 
    intros.
    now rewrite id_left, id_right.
  - simpl.
    intros.
    rewrite assoc, <- X.
    symmetry.
    now rewrite <- assoc, <- X0, assoc.
Defined.

Definition arrow : category := total_category arrow_disp.

End Arrow_Disp.

Definition arrow_dom {C : category} (f : arrow C) : C := pr11 f.
Definition arrow_cod {C : category} (f : arrow C) : C := pr21 f.
Definition arrow_mor {C : category} (f : arrow C) := pr2 f.

Definition mor_to_arrow_ob {C : category} {x y : C} (f : x --> y) : arrow C :=
    (make_dirprod x y,, f).

Definition mors_to_arrow_mor {C : category} {a b x y : C} (f : a --> b) (g : x --> y) 
    (h : a --> x) (k : b --> y) (H : g ∘ h = k ∘ f) : (mor_to_arrow_ob f) --> (mor_to_arrow_ob g).
Proof.
  use tpair.
  - exact (make_dirprod h k).
  - exact H.
Defined.
    

Section Three_disp.

Context (C:category).

Definition three_base := (category_binproduct C (category_binproduct C C)).
Definition three_disp : disp_cat three_base.
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ xyz, pr1 xyz --> pr12 xyz × pr12 xyz --> pr22 xyz).
  - (* double commutative square *)
    simpl; intros xxx yyy gg hh fff.
    exact ((pr1 fff · pr1 hh = pr1 gg · pr12 fff) × (pr12 fff · pr2 hh = pr2 gg · pr22 fff)).
  - simpl.
    intros.
    apply isapropdirprod; use homset_property.
  - simpl. 
    intros.
    split; now rewrite id_left, id_right.
  - simpl.
    intros.
    destruct X as [X1 X2].
    destruct X0 as [Y1 Y2].
    split.
    * rewrite assoc, <- X1.
      symmetry.
      now rewrite <- assoc, <- Y1, assoc.
    * rewrite assoc, <- X2.
      symmetry.
      now rewrite <- assoc, <- Y2, assoc.
Defined.

Definition three : category := total_category three_disp.

End Three_disp.

Definition three_ob0 {C : category} (xyz : three C) : C := pr11 xyz.
Definition three_ob1 {C : category} (xyz : three C) : C := pr121 xyz.
Definition three_ob2 {C : category} (xyz : three C) : C := pr221 xyz.
Definition three_mor01 {C : category} (xyz : three C) := pr12 xyz.
Definition three_mor12 {C : category} (xyz : three C) := pr22 xyz.
Definition three_mor02 {C : category} (xyz : three C) := (three_mor01 xyz) · (three_mor12 xyz).

Definition three_dom {C : category} (f : three C) : C := three_ob0 f.
Definition three_mid {C : category} (f : three C) : C := three_ob1 f.
Definition three_cod {C : category} (f : three C) : C := three_ob2 f.

Section Face_maps.

Context (C : category).

Definition face_map_0_base : three_base C ⟶ arrow_base C.
Proof.
  use make_functor.
  - use make_functor_data.
    * intro xxx.
      exact (make_dirprod (pr12 xxx) (pr22 xxx)).
    * intros xxx yyy fff.
      exact (make_dirprod (pr12 fff) (pr22 fff)).
  - split.
    * unfold functor_idax; intros.
      apply binprod_id.
    * unfold functor_compax; intros.
      apply binprod_comp.
Defined.

Definition face_map_1_base : three_base C ⟶ arrow_base C.
Proof.
  use make_functor.
  - use make_functor_data.
    * intro xxx.
      exact (make_dirprod (pr1 xxx) (pr22 xxx)).
    * intros xxx yyy fff.
      exact (make_dirprod (pr1 fff) (pr22 fff)).
  - split.
    * unfold functor_idax; intros.
      apply binprod_id.
    * unfold functor_compax; intros.
      apply binprod_comp.
Defined.

Definition face_map_2_base : three_base C ⟶ arrow_base C.
Proof.
  use make_functor.
  - use make_functor_data.
    * intro xxx.
      exact (make_dirprod (pr1 xxx) (pr12 xxx)).
    * intros xxx yyy fff.
      exact (make_dirprod (pr1 fff) (pr12 fff)).
  - split.
    * unfold functor_idax; intros.
      apply binprod_id.
    * unfold functor_compax; intros.
      apply binprod_comp.
Defined.

Definition face_map_0_functor_data : disp_functor_data face_map_0_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - (* map on displayed objects *)
    intros xxx xxx'.
    simpl.
    destruct xxx' as [_ f2].
    exact f2.
  - (* map on displayed arrows *)
    simpl.
    intros xxx yyy ff gg F H.
    destruct H as [_ h2].
    symmetry.
    exact (pathsinv0 h2).
Defined.

Definition face_map_1_functor_data : disp_functor_data face_map_1_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - (* map on displayed objects *)
    intros xxx xxx'.
    simpl.
    destruct xxx' as [f1 f2].
    exact (f2 ∘ f1).
  - (* map on displayed arrows *)
    simpl.
    intros xxx yyy ff gg F H.
    destruct H as [h1 h2].
    symmetry.
    rewrite <- assoc.
    etrans.
    apply maponpaths.
    exact (pathsinv0 h2).
    rewrite assoc, assoc.
    apply cancel_postcomposition.
    exact (pathsinv0 h1).
Defined.

Definition face_map_2_functor_data : disp_functor_data face_map_2_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - (* map on displayed objects *)
    intros xxx xxx'.
    simpl.
    destruct xxx' as [f1 _].
    exact f1.
  - (* map on displayed arrows *)
    simpl.
    intros xxx yyy ff gg F H.
    destruct H as [h1 _].
    exact h1.
Defined.

Definition face_map_0_disp : disp_functor face_map_0_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - exact face_map_0_functor_data.
  (* todo: this is still a bit vague to me *)
  (* can use homset_property of C to show that the morphisms are indeed equal *)
  - repeat split; intros; apply C.
Defined.

Definition face_map_1_disp : disp_functor face_map_1_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - exact face_map_1_functor_data.
  - repeat split; intros; apply C.
Defined.

Definition face_map_2_disp : disp_functor face_map_2_base (three_disp C) (arrow_disp C).
Proof.
  use tpair.
  - exact face_map_2_functor_data.
  - repeat split; intros; apply C.
Defined.

Definition face_map_0 := total_functor face_map_0_disp.
Definition face_map_1 := total_functor face_map_1_disp.
Definition face_map_2 := total_functor face_map_2_disp.

(* verify that they are indeed compatible *)
Lemma face_compatibility (fg : three C) : arrow_mor (face_map_0 fg) ∘ arrow_mor (face_map_2 fg) = arrow_mor (face_map_1 fg).
Proof.
  trivial.
Defined.

(* We can't just define c_21 as a displayed natural transformation like this 
   since we need a natural transformation from d_2 to d_1 in the base categories,
   but we can't do that, as we need a map from 1 --> 2, which we don't have 
   in the base category...
*)
(* 
Definition c_21_map_on_objects : ∏ x, face_map_2_base x --> face_map_1_base x.
Proof.
  intro xxx.
  split.
  - exact (identity _).
  - admit.
Admitted.

Definition c_21_disp_data : disp_nat_trans_data c_21_map_on_objects face_map_2_disp face_map_1_disp.
*)


Definition c_21_data : nat_trans_data face_map_2 face_map_1.
Proof.
  (* this natural transformation boils down to square
    0 ===== 0
    |       |
    |       |
    1 ----> 2
  *)
  intro xxx.
  destruct xxx as [xxx [f1 f2]].
  simpl.
  exists (make_dirprod (identity _) f2).
  simpl.
  now rewrite id_left.
Defined.

Definition c_21 : face_map_2 ⟹ face_map_1.
Proof.
  use make_nat_trans.
  - exact c_21_data.
  - (* natural transformation commutativity axiom *)
    intros xxx yyy ff.

    (* use displayed properties to turn path in total category
    into path in base category, given our displayed properties

    subtypePath: equality on ∑ x : X, P x is the same as equality
    on X if P is a predicate (maps to a prop).
    In the total category, objects are ∑ c : C, D c
    i.e., objects with displayed data. Morphisms are morphisms
    with displayed data. Our morphisms displayed data is indeed 
    propositional: commutative diagram.
    *)
    apply subtypePath.
    * (* For any map in the base category, the induced map
      on the displayed category is a property.
      
      This is because the induced map is a commuting square,
      so an equality between maps. Therefore, the homset property
      says this is a property. *)
      intro f.
      simpl.
      apply homset_property.
    * (* We are left to prove the commutativity in the base category,
      given our displayed properties *)
      cbn.
      rewrite id_left, id_right.
      destruct ff as [[f0 [f1 f2]] [? f1comm]].
      cbn in *.
      (* equality of dirprod, second eq is exactly f1comm *)
      apply pathsdirprod; trivial.
Defined.

Definition c_10_data : nat_trans_data face_map_1 face_map_0.
Proof.
  (* this natural transformation boils down to square
    0 ----> 1
    |       |
    |       |
    2 ===== 2
  *)
  intro xxx.
  destruct xxx as [xxx [f1 f2]].
  simpl.
  exists (make_dirprod f1 (identity _)).
  simpl.
  now rewrite id_right.
Defined.

Definition c_10 : face_map_1 ⟹ face_map_0.
Proof.
  use make_nat_trans.
  - exact c_10_data.
  - intros xxx yyy ff.
    apply subtypePath.
    * intro x.
      apply homset_property.
    * cbn.
      rewrite id_left, id_right.
      destruct ff as [[f0 [f1 f2]] []].
      cbn in *.
      apply pathsdirprod; trivial.
Defined.

End Face_maps.

Arguments face_map_0 {_}.
Arguments face_map_1 {_}.
Arguments face_map_2 {_}.

(* Lemma face_map_1_preserves_dom {C : category} : ∏ g : three C, arrow_dom (face_map_1 g) = three_dom g.
Proof.
  trivial.
Defined.

Lemma face_map_1_preserves_cod {C : category} : ∏ g : three C, arrow_cod (face_map_1 g) = three_cod g.
Proof.
  trivial.
Defined. *)

Definition functorial_factorization (C : category) : UU := 
    ∑ F : (arrow C ⟶ three C), 
        F ∙ face_map_1 = functor_identity (arrow C).

Definition fact_functor {C : category} (F : functorial_factorization C) := pr1 F.
Coercion fact_functor : functorial_factorization >-> functor.
Definition fact_cond {C : category} (F : functorial_factorization C) := pr2 F.

Definition fact_L {C : category} (F : functorial_factorization C) : arrow C ⟶ arrow C:=
    F ∙ face_map_2.
Definition fact_R {C : category} (F : functorial_factorization C) : arrow C ⟶ arrow C :=
    F ∙ face_map_0.

Lemma fact_preserves_dom {C : category} (F : functorial_factorization C) (f : arrow C) :
    (three_dom (F f)) = arrow_dom f.
Proof.
  (* todo: why do I _have_ to use pr1 here (coercion)? *)
  change (arrow_dom (((pr1 F) ∙ face_map_1) f) = arrow_dom f).
  rewrite (fact_cond F).
  trivial.
Defined.

Lemma fact_preserves_cod {C : category} (F : functorial_factorization C) (f : arrow C) :
    (three_cod (F f)) = arrow_cod f.
Proof.
  change (arrow_cod (((pr1 F) ∙ face_map_1) f) = arrow_cod f).
  rewrite (fact_cond F).
  trivial.
Defined.

Lemma LR_compatibility {C : category} (F : functorial_factorization C) (f : arrow C) : 
   Type.
(* coq does not deduce that the resulting morphism has the same domain/codomain *)
(* pr2 (fact_R F f) ∘ pr2 (fact_L F f) = (pr2 f). *)
Proof.
  (* (fact_R F f) ∘ (fact_L F f) = (pr1 F f). *)
  set (lr := pr2 (fact_R F f) ∘ pr2 (fact_L F f)).
  set (id := pr2 f).
  simpl in id.
  simpl in lr.
  assert (three_cod (F f) = arrow_cod f).
  {
    apply fact_preserves_cod.
  }
  assert (three_dom (F f) = arrow_dom f).
  {
    apply fact_preserves_dom.
  }

  unfold three_cod in X.
  unfold arrow_cod in X.
  unfold three_dom in X0.
  unfold arrow_dom in X0.
  admit.
Admitted.

(* without any type specified, we get:
  fact_Φ : ∏ F : functorial_factorization ?C,
       functor_composite_data F face_map_2
       ⟹ functor_composite_data F face_map_1 *)
(* but we want:
  (functor_composite_data F face_map_2) ⟹ (functor_identity_data (arrow C)) *)
(* this should be the same by assumption in F *)
(* first definition: *)
(* Definition fact_Φ {C : category} (F : functorial_factorization C) :=
    pre_whisker F (c_21 C). *)
Definition Φ {C : category} (F : functorial_factorization C) :
    (fact_L F) ⟹ (functor_identity (arrow C)).
Proof.
  (* use the condition in the factorization to rewrite the goal type to that
     of pre_whisker F (c_21 C) *)
  set (fact_condition := fact_cond F).
  simpl in fact_condition.
  change (functor_identity _) with (functor_identity (arrow C)) in fact_condition.
  rewrite <- fact_condition.
  exact (pre_whisker F (c_21 C)).
Defined.

(* similar here *)
(* Definition fact_Λ {C : category} (F : functorial_factorization C) :=
    pre_whisker F (c_10 C). *)
Definition Λ {C : category} (F : functorial_factorization C) :
    (functor_identity (arrow C)) ⟹ (fact_R F).
Proof.
  set (fact_condition := fact_cond F).
  simpl in fact_condition.
  change (functor_identity _) with (functor_identity (arrow C)) in fact_condition.
  rewrite <- fact_condition.
  exact (pre_whisker F (c_10 C)).
Defined.

Definition R_monad_data {C : category} (F : functorial_factorization C) (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) : Monad_data (arrow C).
Proof.
  use tpair.
  - exists (fact_R F).
    exact Π.
  - exact (Λ F).
Defined.

Definition R_monad {C : category} (F : functorial_factorization C) (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) (R : Monad_laws (R_monad_data F Π)) : Monad (arrow C).
Proof.
  exists (R_monad_data F Π).
  exact R.
Defined.

Definition L_monad_data {C : category} (F : functorial_factorization C) (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) : Monad_data (op_cat (arrow C)).
Proof.
  use tpair.
  - exists (functor_opp (fact_L F)).
    exact (op_nt Σ).
  - exact (op_nt (Φ F)).
Defined.

Definition L_monad {C : category} (F : functorial_factorization C) (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) (L : Monad_laws (L_monad_data F Σ)) : Monad (op_cat (arrow C)).
Proof.
  exists (L_monad_data F Σ).
  exact L.
Defined.

(* todo: does this encapsulate the relation between L and R wel enough *)
Definition nwfs (C : category) :=
    ∑ (F : functorial_factorization C) (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) ,
    (Monad_laws (L_monad_data F Σ)) × (Monad_laws (R_monad_data F Π)).

Definition make_nwfs {C : category} (F : functorial_factorization C)
    (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) (L : Monad_laws (L_monad_data F Σ)) 
    (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) (R : Monad_laws (R_monad_data F Π))
        : nwfs C.
Proof.
  exists F, Σ, Π.
  exact (make_dirprod L R).
Defined.

Definition nwfs_fact {C : category} (n : nwfs C) := pr1 n.
Definition nwfs_Σ {C : category} (n : nwfs C) := pr12 n.
Definition nwfs_Π {C : category} (n : nwfs C) := pr122 n.
Definition nwfs_Σ_laws {C : category} (n : nwfs C) := pr1 (pr222 n).
Definition nwfs_Π_laws {C : category} (n : nwfs C) := pr2 (pr222 n).
Definition nwfs_R_monad {C : category} (n : nwfs C) := R_monad (nwfs_fact n) (nwfs_Π n) (nwfs_Π_laws n).
Definition nwfs_L_monad {C : category} (n : nwfs C) := L_monad (nwfs_fact n) (nwfs_Σ n) (nwfs_Σ_laws n).

(* In a monad algebra, we have [[f αf] laws] : nwfs_R_maps n *)
Definition nwfs_R_maps {C : category} (n : nwfs C) :=
    MonadAlg (nwfs_R_monad n).
Definition nwfs_L_maps {C : category} (n : nwfs C) :=
    MonadAlg (nwfs_L_monad n).

Definition isAlgebra {C : category} (M : Monad (arrow C)) {x y : C} (f : x --> y) :=
    ∃ α, Algebra_laws M (mor_to_arrow_ob f,, α).
Definition isCoAlgebra {C : category} (M : Monad (op_cat (arrow C))) {x y : C} (f : x --> y) :=
    ∃ α, Algebra_laws M (mor_to_arrow_ob f,, α).

(* we can obtain a wfs from an nwfs *)
Definition nwfs_R_maps_class {C : category} (n : nwfs C) : morphism_class C :=
    λ (x y : C) (f : x --> y), isAlgebra (nwfs_R_monad n) f.
Definition nwfs_L_maps_class {C : category} (n : nwfs C) : morphism_class C :=
    λ (x y : C) (f : x --> y), isCoAlgebra (nwfs_L_monad n) (opp_mor f).

Lemma nwfs_is_wfs {C : category} (n : nwfs C) : wfs C.
Proof.
  use make_wfs.
  - exact (nwfs_L_maps_class n).
  - exact (nwfs_R_maps_class n).
  - use make_is_wfs.
    * apply morphism_class_subset_antisymm.
      + intros a b f hf'.
        intros c d g hg'.
        intros h k H.

        use (hinhuniv _ hf').
        intro hf.
        destruct hf as [[αf αfcomm] [hαf1 hαf2]].
        destruct αf as [ida s].
        simpl in ida, s.
        cbn in hαf1, hαf2, αfcomm.

        use (hinhuniv _ hg').
        intro hg.
        destruct hg as [[αg αgcomm] [hαg1 hαg2]].
        destruct αg as [p idd].
        simpl in p, idd.
        cbn in hαg1, αgcomm.

        apply hinhpr.
        
        set (hk := mors_to_arrow_mor f g h k H).
        set (Fhk := functor_on_morphisms (fact_functor (nwfs_fact n)) hk).
        (* middle map (todo: wrap this) *)
        set (Khk := pr121 Fhk). (* Kf --> Kg *)

        set (Hhk2 := pr22 Fhk).
        cbn in Hhk2.

        (*    
                    h
         A ==== A ----> C
         |      |       |
         |  αf  |       |
         v      v  Khk  v   p
         B ---> Kf ---> Kg ---> C
            s   |       |       |
                |       |  αg   |
                v       |       v
                B ----> D ===== D
                    k
        *)

        exists (s · Khk · p).
        split.
        -- (* f · (s · Khk · p) = h *)
           admit.
        -- (* s · Khk · p · g = k *)
           rewrite <- (assoc _ p g).
           rewrite αgcomm.
           rewrite (assoc _ _ idd).
           rewrite <- (assoc s _ _).
           cbv [Khk].
           (* rewrite Hhk2. *)
           
           admit.
      + admit.
    * (* this should just be the same as above *)
      admit.
    * intros x y f.
      set (farr := mor_to_arrow_ob f).
      set (fact := nwfs_fact n farr).
      destruct fact as [[x0 [x1 x2]] [f01 f12]].
      simpl in f01, f12.

      (* rewrite <- (fact_preserves_dom (nwfs_fact n) farr) in f01. *)

      apply hinhpr.
      exists x1.
      (* we know that x0 = x and x2 = y, but this is not automatically rewritten *)
      admit.
Defined.
