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
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

From Model Require Import morphism_class arrow three.

Local Open Scope cat.
Local Open Scope mor_disp.

Section Face_maps.

Context (C : category).

(* face map 1 now rolls out just as the projection *)
Definition face_map_1 : three C ⟶ arrow C := pr1_category _.

(* we have to define face maps 0 and 2 as proper functors,
since we need the factorization to obtain an object in the arrow
category. *)
Definition face_map_0_data : functor_data (three C) (arrow C).
Proof.
  use make_functor_data.
  - intro xxx.
    use tpair.
    * exact (make_dirprod (three_ob1 xxx) (three_ob2 xxx)).
    * simpl.
      exact (three_mor12 xxx).
  - intros xxx yyy fff.
    simpl.
    (* for morphisms we simply forget the 0th morphism *)
    use tpair.
    * split; simpl.
      + exact (three_mor11 fff).
      + exact (three_mor22 fff).
    * simpl.
      (* commutativity is just commutativity in the lower diagram *)
      symmetry.
      exact (pr2 (three_mor_comm fff)).
Defined.

Definition face_map_0 : three C ⟶ arrow C.
Proof.
  use make_functor.
  - exact face_map_0_data.
  - split.
    * (* unfold functor_idax. *)
      intro.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
    * (* unfold functor_compax. *)
      intros a b c f g.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
Defined.

Definition face_map_2_data : functor_data (three C) (arrow C).
Proof.
  use make_functor_data.
  - intro xxx.
    use tpair.
    * exact (make_dirprod (three_ob0 xxx) (three_ob1 xxx)).
    * simpl.
      exact (three_mor01 xxx).
  - intros xxx yyy fff.
    simpl.
    use tpair.
    * split; simpl.
      + exact (three_mor00 fff).
      + exact (three_mor11 fff).
    * simpl.
      symmetry.
      exact (pr1 (three_mor_comm fff)).
Defined.

Definition face_map_2 : three C ⟶ arrow C.
Proof.
  use make_functor.
  - exact face_map_2_data.
  - split.
    * (* unfold functor_idax. *)
      intro.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
    * (* unfold functor_compax. *)
      intros a b c f g.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
Defined.

(* verify that they are indeed compatible *)
Lemma face_compatibility (fg : three C) : arrow_mor (face_map_0 fg) ∘ arrow_mor (face_map_2 fg) = arrow_mor (face_map_1 fg).
Proof.
  exact (three_comp fg).
Defined.

Definition c_21_data : nat_trans_data face_map_2 face_map_1.
Proof.
  (* this natural transformation boils down to square
    0 ===== 0
    |       |
    |       |
    1 ----> 2
  *)
  intro xxx.
  simpl.
  exists (make_dirprod (identity _) (three_mor12 xxx)).
  simpl.
  rewrite id_left.
  symmetry.
  exact (three_comp xxx).
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
      given our displayed properties. This is effectively just commutativity
      in the bottom square. *)
      cbn.
      rewrite id_left, id_right.
      apply pathsdirprod; trivial.
      symmetry.
      exact (pr2 (three_mor_comm ff)).
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
  simpl.
  exists (make_dirprod (three_mor01 xxx) (identity _)).
  simpl.
  rewrite id_right.
  exact (three_comp xxx).
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
      apply pathsdirprod; trivial.
      symmetry.
      exact (pr1 (three_mor_comm ff)).
Defined.

End Face_maps.

Arguments face_map_0 {_}.
Arguments face_map_1 {_}.
Arguments face_map_2 {_}.

(* Lemma face_map_1_preserves_dom {C : category} : ∏ g : three C, arrow_dom (face_map_1 g) = three_ob0 g.
Proof.
  trivial.
Defined.

Lemma face_map_1_preserves_cod {C : category} : ∏ g : three C, arrow_cod (face_map_1 g) = three_ob2 g.
Proof.
  trivial.
Defined. *)

(* Definition face_map_1_section_data (C : category) : functor_data (arrow C) (three C).
Proof.
  use tpair.
  - intros
Defined. *)

(* We can't really do this with the "naive definition" of three C, since then we need
the middle object for the section. We would have to define our own theory.  *)
Definition functorial_factorization (C : category) := section_disp (three_disp C).
Definition fact_section {C : category} (F : functorial_factorization C) 
    := section_disp_data_from_section_disp F.
Definition fact_functor {C : category} (F : functorial_factorization C) : arrow C ⟶ three C :=
    section_functor F.
Coercion fact_functor : functorial_factorization >-> functor.

(* Functorial factorizations indeed split face map 1 (d1) *)
Lemma functorial_factorization_splits_face_map_1 {C : category} (F : functorial_factorization C) :
    F ∙ face_map_1 = functor_identity (arrow C).
Proof.
  apply functor_eq; trivial.
  apply homset_property.
Defined.

Definition fact_L {C : category} (F : functorial_factorization C) : arrow C ⟶ arrow C :=
    F ∙ face_map_2.
Definition fact_R {C : category} (F : functorial_factorization C) : arrow C ⟶ arrow C :=
    F ∙ face_map_0.

(* At least now it knows they are compatible *)
Lemma LR_compatibility {C : category} (F : functorial_factorization C) : 
    ∏ (f : arrow C), arrow_mor (fact_L F f) · arrow_mor (fact_R F f) = arrow_mor f.
Proof.
  intro.
  exact (three_comp _).
Defined.

Definition Φ {C : category} (F : functorial_factorization C) :
    (fact_L F) ⟹ (functor_identity (arrow C)) := 
  pre_whisker F (c_21 C).

Definition Λ {C : category} (F : functorial_factorization C) :
    (functor_identity (arrow C)) ⟹ (fact_R F) :=
  pre_whisker F (c_10 C).

Definition R_monad_data {C : category} (F : functorial_factorization C) 
    (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) : Monad_data (arrow C) :=
  ((fact_R F,, Π),, (Λ F)).

Definition R_monad {C : category} (F : functorial_factorization C) 
    (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) 
    (R : Monad_laws (R_monad_data F Π)) : Monad (arrow C) :=
  (R_monad_data F Π,, R).

Definition L_monad_data {C : category} (F : functorial_factorization C) 
    (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) : Monad_data (op_cat (arrow C)) :=
  ((functor_opp (fact_L F),, op_nt Σ),, op_nt (Φ F)).

Definition L_monad {C : category} (F : functorial_factorization C) 
    (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) 
    (L : Monad_laws (L_monad_data F Σ)) : Monad (op_cat (arrow C)) :=
  (L_monad_data F Σ,, L).

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
Coercion nwfs_fact : nwfs >-> functorial_factorization.
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
