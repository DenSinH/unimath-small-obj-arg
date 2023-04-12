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
From Model.model Require Import wfs.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope morcls.

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

(* we can obtain a wfs from an nwfs *)
Definition nwfs_R_maps_class {C : category} (n : nwfs C) : morphism_class C :=
    λ (x y : C) (f : x --> y), isAlgebra (nwfs_R_monad n) f.
Definition nwfs_L_maps_class {C : category} (n : nwfs C) : morphism_class C :=
    λ (x y : C) (f : x --> y), isCoAlgebra (nwfs_L_monad n) (opp_mor f).


(*
Shape of comonad morphism diagram (2.15, Garner)
  A ===== A ===== A  ~~> id_A
  |       |       |
f |   α   |λf  η  | f
  v       v       v
  B ---> Kf ----> B  ~~> id_B
     s       ρ_f
*)
Lemma L_map_section {C : category} {n : nwfs C} {a b : C} {f : a --> b} (hf : nwfs_L_maps_class n _ _ f) :
    ∃ s, f · s = arrow_mor (fact_L n (mor_to_arrow_ob f)) × 
         s · arrow_mor (fact_R n (mor_to_arrow_ob f)) = identity _.
Proof.
  use (hinhuniv _ hf).
  intro hf'.
  destruct hf' as [[[ida s] αfcomm] [hαfη _]].
  cbn in ida, s, αfcomm.
  simpl in hαfη.
  cbn in hαfη.

  apply hinhpr.
  exists s.

  (* top line of hαfη: *)
  assert (ida = identity a) as Hida.
  {
    (* base_paths : equality in pr1 of ∑-type (paths in base category)
       pathsdirprodweq : _ × _ = _ × _ -> equality of terms
    *)
    set (top_line := dirprod_pr1 (pathsdirprodweq (base_paths _ _ hαfη))).
    rewrite id_right in top_line.
    exact top_line.
  }

  split.
  - (* f ⋅ s = λ_f *)
    (* commutativity and ida = identity a *)
    specialize (αfcomm) as αfcomm'. 
    rewrite Hida, id_left in αfcomm'.
    apply pathsinv0.
    exact αfcomm'.
  - (* s · ρ_f = id_b *)
    (* bottom line of hαfη *)
    set (bottom_line := dirprod_pr2 (pathsdirprodweq (base_paths _ _ hαfη))).
    exact bottom_line.
Defined.

(*
Shape of monad morphism diagram (2.15, Garner)
     λg       p
  C ---> Kg ----> C  ~~> id_C
  |       |       |
g |   η   |ρg  α  | g
  v       v       v
  D ===== D ===== D  ~~> id_D
*)
Lemma R_map_section {C : category} {n : nwfs C} {c d : C} {g : c --> d} (hg : nwfs_R_maps_class n _ _ g) :
    ∃ p, p · g = arrow_mor (fact_R n (mor_to_arrow_ob g)) × 
         arrow_mor (fact_L n (mor_to_arrow_ob g)) · p = identity _.
Proof.
  use (hinhuniv _ hg).
  intro hg'.
  destruct hg' as [[[p idd] αgcomm] [hαgη _]].
  cbn in p, idd, αgcomm.
  simpl in hαgη.
  cbn in hαgη.

  apply hinhpr.
  exists p.

  (* bottom line of hαgη: *)
  assert (idd = identity d) as Hidd.
  {
    (* base_paths : equality in pr1 of ∑-type (paths in base category)
       pathsdirprodweq : _ × _ = _ × _ -> equality of terms
    *)
    set (bottom_line := dirprod_pr2 (pathsdirprodweq (base_paths _ _ hαgη))).
    rewrite id_left in bottom_line.
    exact bottom_line.
  }

  split.
  - (* p ⋅ g = ρ_g *)
    (* commutativity and ida = identity a *)
    specialize (αgcomm) as αgcomm'. 
    rewrite Hidd, id_right in αgcomm'.
    exact αgcomm'.
  - (* λg · p = id_c *)
    (* top line of hαfη *)
    set (top_line := dirprod_pr1 (pathsdirprodweq (base_paths _ _ hαgη))).
    exact top_line.
Defined.

Lemma L_map_R_map_llp {C : category} {n : nwfs C} {a b c d : C}
    {f : a --> b} {g : c --> d} (hf : nwfs_L_maps_class n _ _ f)
    (hg : nwfs_R_maps_class n c d g) : lp_hProp f g.
Proof.
  (* want to construct a lift of an L-map and an R-map
     using monad properties *)
  intros h k H.

  use (hinhuniv _ (L_map_section hf)).
  intro Hs.
  destruct Hs as [s [Hs0 Hs1]].

  use (hinhuniv _ (R_map_section hg)).
  intro Hp.
  destruct Hp as [p [Hp0 Hp1]].

  apply hinhpr.

  set (hk := mors_to_arrow_mor f g h k H).
  set (Fhk := functor_on_morphisms (fact_functor n) hk).
  (* Kf --> Kg *)
  set (Khk := three_mor11 Fhk). 

  (* commutativity in diagrams *)
  set (Hhk := three_mor_comm Fhk).
  simpl in Hhk.
  destruct Hhk as [Hhk0 Hhk1].

  (*    
              h
  A ==== A ----> C
  |      |       |
  f |  Lf  |       |
  v      v  Khk  v   p
  B ---> Kf ---> Kg ---> C
      s   |       |       |
          |       |  Rg   | g
          v       |       v
          B ----> D ===== D
              k
  *)

  exists (s · Khk · p).
  split.
  - (* f · (s · Khk · p) = h *)
    rewrite assoc, assoc.
    rewrite Hs0.
    (* λ_f · Khk · p = h *)
    (* rewrite Hhk0 : (λ_f · Hhk = h · λ_g) *)
    etrans.
    apply maponpaths_2.
    exact Hhk0.
    (* h · λ_g · p = h *)
    (* rewrite Hp1 : (λ_g · p = id_C) *)
    rewrite <- assoc.
    etrans.
    apply maponpaths.
    exact Hp1.
    (* h · id_C = h *)
    now rewrite id_right.
  - (* s · Khk · p · g = k *)
    rewrite <- (assoc _ p g).
    rewrite Hp0.
    (* s · Khk · ρ_g = k *)
    (* rewrite Hhk1 : ρ_f · k = Khk · ρ_g *)
    rewrite <- assoc.
    etrans.
    apply maponpaths.
    exact (pathsinv0 Hhk1).
    (* s · ρ_f · k = k *)
    (* rewrite Hs1 : s · ρ_f = id_B *)
    rewrite assoc.
    etrans.
    apply maponpaths_2.
    exact Hs1.
    (* id_B · k = k *)
    now rewrite id_left.
Qed.

Lemma nwfs_L_maps_subs_llp_R_maps {C : category} (n : nwfs C) :
    nwfs_L_maps_class n ⊆ llp (nwfs_R_maps_class n).
Proof.
  intros a b f hf.
  intros c d g hg.
  exact (L_map_R_map_llp hf hg).
Qed.

(* dual to above statement *)
Lemma nwfs_R_maps_subs_rlp_L_maps {C : category} (n : nwfs C) :
    nwfs_R_maps_class n ⊆ rlp (nwfs_L_maps_class n).
Proof.
  intros c d g hg.
  intros a b f hf.
  exact (L_map_R_map_llp hf hg).
Qed.

(* the following lemmas about Σ and Π are from 
   Grandis, Tholen, (6), (7), diagram after (7), (8), (9) *)

(* diagram after (7) *)
Lemma nwfs_Σ_top_map_id {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor00 (nwfs_Σ n f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_L_monad n) f).
  specialize (dirprod_pr1 (pathsdirprodweq (base_paths _ _ law1))) as top.
  apply pathsinv0.
  etrans.
  exact (pathsinv0 top).
  apply id_right.
Qed.

(* σ_f · ρ_{λf} = id (6, 2nd) *)
Lemma nwfs_Σ_bottom_map_inv {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor11 (nwfs_Σ n f) · arrow_mor (fact_R n (fact_L n f)) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_L_monad n) f).
  specialize (dirprod_pr2 (pathsdirprodweq (base_paths _ _ law1))) as bottom.
  exact bottom.
Qed.

(* σ_{λf} · σ_f = F(1_A, σ_f) · σ_f 
  where F(1_a, σ_f) is the map on middle objects of F(Σ_f)
  if we see Σ_f as a morphism in the arrow category 
   (9, top right + cancel_postcomposition) *)
Lemma nwfs_Σ_bottom_map_L_is_middle_map_of_Σ {C : category} (n : nwfs C) (f : arrow C) :
    (arrow_mor11 (nwfs_Σ n f)) · arrow_mor11 (nwfs_Σ n (fact_L n f)) =
    (arrow_mor11 (nwfs_Σ n f)) · three_mor11 (functor_on_morphisms n (nwfs_Σ n f)).
Proof.
  set (law3 := Monad_law3 (T:=nwfs_L_monad n) f).
  specialize (dirprod_pr2 (pathsdirprodweq (base_paths _ _ law3))) as bottom.
  apply pathsinv0.
  exact bottom.
Qed.

(* diagram after (7) *)
Lemma nwfs_Π_bottom_map_id {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor11 (nwfs_Π n f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_R_monad n) f).
  specialize (dirprod_pr2 (pathsdirprodweq (base_paths _ _ law1))) as bottom.
  apply pathsinv0.
  etrans.
  exact (pathsinv0 bottom).
  apply id_left.
Qed.

(* λ_{ρf} · π_f = id (6, 4th) *)
Lemma nwfs_Π_top_map_inv {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor (fact_L n (fact_R n f)) · arrow_mor00 (nwfs_Π n f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_R_monad n) f).
  specialize (dirprod_pr1 (pathsdirprodweq (base_paths _ _ law1))) as top.
  exact top.
Qed.

(* π_{ρf} · π_f = F(π_f, 1_b) · π_f) 
  where F(π_f, 1_b) = map on middle objects of F(Π_f)
  if we see Π_f as a morphism in the arrow category
   (9, bottom right + cancel_precomposition) *)
Lemma nwfs_Π_bottom_map_R_is_middle_map_of_Π {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor00 (nwfs_Π n (fact_R n f)) · arrow_mor00 (nwfs_Π n f) = 
    three_mor11 (functor_on_morphisms n (nwfs_Π n f)) · arrow_mor00 (nwfs_Π n f).
Proof.
  set (law3 := Monad_law3 (T:=nwfs_R_monad n) f).
  specialize (dirprod_pr1 (pathsdirprodweq (base_paths _ _ law3))) as top.
  apply pathsinv0.
  exact top.
Qed.

Lemma nwfs_Lf_is_L_map {C : category} (n : nwfs C) :
    ∏ f : arrow C, (nwfs_L_maps_class n) _ _ (arrow_mor (fact_L n f)).
Proof.
  intro f.

  (* unfold nwfs_L_maps_class, isCoAlgebra. *)
  apply hinhpr.
  exists (nwfs_Σ n f).

  split; use subtypePath; try (intro; apply homset_property); cbn.
  - apply pathsdirprod.
    * etrans.
      apply maponpaths_2.
      exact (nwfs_Σ_top_map_id n f).
      now rewrite id_right.
    * exact (nwfs_Σ_bottom_map_inv n f).
  - apply pathsdirprod.
    * apply cancel_precomposition.
      (* rhs is just pr11 nwfs_Σ n f
         unfold three_mor00; simpl. *)
      apply pathsinv0.
      etrans.
      exact (nwfs_Σ_top_map_id n f).
      apply pathsinv0.
      exact (nwfs_Σ_top_map_id n (mor_to_arrow_ob _)).
    * exact (nwfs_Σ_bottom_map_L_is_middle_map_of_Σ _ _).
Qed.

(* dual statement *)
Lemma nwfs_Rf_is_R_map {C : category} (n : nwfs C) :
    ∏ f : arrow C, (nwfs_R_maps_class n) _ _ (arrow_mor (fact_R n f)).
Proof.
  intro f.

  (* unfold nwfs_R_maps_class, isAlgebra. *)
  apply hinhpr.
  exists (nwfs_Π n f).

  split; use subtypePath; try (intro; apply homset_property); cbn.
  - apply pathsdirprod.
    * exact (nwfs_Π_top_map_inv n f).
    * etrans.
      apply maponpaths.
      exact (nwfs_Π_bottom_map_id n f).
      now rewrite id_right.
  - apply pathsdirprod.
    * exact (nwfs_Π_bottom_map_R_is_middle_map_of_Π _ _).
    * apply cancel_postcomposition.
      (* rhs is just pr21 nwfs_Π n f
        unfold three_mor22; simpl. *)
      apply pathsinv0.
      etrans.
      exact (nwfs_Π_bottom_map_id n f).
      apply pathsinv0.
      exact (nwfs_Π_bottom_map_id n (mor_to_arrow_ob _)).
Qed.

Lemma nwfs_llp_R_maps_subs_L_maps {C : category} (n : nwfs C) :
    llp (nwfs_R_maps_class n) ⊆ nwfs_L_maps_class n.
Proof.
  (* Want to construct α using lift *)
  intros a b f hf.

  set (Lf := arrow_mor (fact_L n (mor_to_arrow_ob f))).
  set (Rf := arrow_mor (fact_R n (mor_to_arrow_ob f))).
  cbn in Rf.

  (* f ∈ llp (R-Map), so has llp with Rf *)
  (* the lift gives us precisely the map we need for α *)
  use (hf _ _ Rf).

  - exact (nwfs_Rf_is_R_map _ _).
  - exact Lf.
  - exact (identity _).
  - rewrite id_right.
    (* or: three_comp (n (mor_to_arrow_ob f)) *)
    exact (LR_compatibility n (mor_to_arrow_ob f)).
  - intro hl.
    destruct hl as [l [hl0 hl1]].

    (* unfold nwfs_L_maps_class, isCoAlgebra. *)
    apply hinhpr.
    use tpair.
    * use mors_to_arrow_mor.
      + exact (identity _).
      + exact l.
      + rewrite id_left.
        apply pathsinv0.
        exact hl0.
    * simpl.
      split.
      + (* η · α = id *)
        simpl.
        apply subtypePath; [intro; apply homset_property|].
        cbn.
        (* top map is just identity for both *)
        apply pathsdirprod; [now rewrite id_left|].
        exact hl1.
      + (* μ · α = T (α) · α  (flipped in comonad)*)
        (* ~ α · Σ = α · L (α)*)
        apply subtypePath; [intro; apply homset_property|].
        cbn.
        apply pathsdirprod.
        -- (* top maps are both identity *)
           apply cancel_precomposition.
           exact (nwfs_Σ_top_map_id n (mor_to_arrow_ob f)).
        -- (* commutativity in bottom maps *)
           apply cancel_precomposition.
           unfold three_mor11.
           simpl.
           (* σ_f = three_map11 (#n (id, l)) *)
           (* since: pr1: three_map11
              section_disp_on_morphisms n : #n
              from f to three_mor01 ... : f -> λ_f
              (internal_paths_rew_r ...) : commutativity *)
           admit.
Admitted.

(* dual statement *)
Lemma nwfs_rlp_L_maps_subs_R_maps {C : category} (n : nwfs C) :
    rlp (nwfs_L_maps_class n) ⊆ nwfs_R_maps_class n.
Proof.
  (* Want to construct α using lift *)
  intros a b f hf.

  set (Lf := arrow_mor (fact_L n (mor_to_arrow_ob f))).
  set (Rf := arrow_mor (fact_R n (mor_to_arrow_ob f))).
  cbn in Lf, Rf.

  (* f ∈ rlp (L-Map), so has rlp with Lf *)
  (* the lift gives us precisely the map we need for α *)
  use (hf _ _ Lf).

  - exact (nwfs_Lf_is_L_map n (mor_to_arrow_ob f)).
  - exact (identity _).
  - exact Rf.
  - rewrite id_left.
    apply pathsinv0.
    (* or: three_comp (n (mor_to_arrow_ob f)) *)
    exact (LR_compatibility n (mor_to_arrow_ob f)).
  - intro hl.
    destruct hl as [l [hl0 hl1]].

    (* unfold nwfs_R_maps_class, isAlgebra. *)
    apply hinhpr.
    use tpair.
    * use mors_to_arrow_mor.
      + exact l.
      + exact (identity _).
      + rewrite id_right.
        exact hl1.
    * simpl.
      split.
      + (* η · α = id *)
        simpl.
        apply subtypePath; [intro; apply homset_property|].
        cbn.
        (* top map is just identity for both *)
        apply pathsdirprod; [|now rewrite id_left].
        exact hl0.
      + (* μ · α = T (α) · α  (flipped in comonad)*)
        (* ~ Π · α = L (α) · α*)
        apply subtypePath; [intro; apply homset_property|].
        cbn.
        apply pathsdirprod.
        -- (* commutativity in top maps *)
           apply cancel_postcomposition.
           unfold three_mor11.
           simpl.
           (* π_f = three_map11 (#n (l, id)) *)
           (* since: pr1: three_map11
              section_disp_on_morphisms n : #n
              from three_mor12 to f ... : ρ_f -> f
              (internal_paths_rew_r ...) : commutativity *)
           admit.
        -- (* bottom maps are both identity *)
           apply cancel_postcomposition.
           exact (nwfs_Π_bottom_map_id n (mor_to_arrow_ob f)).
Admitted.
    
Lemma nwfs_is_wfs {C : category} (n : nwfs C) : wfs C.
Proof.
  use make_wfs.
  - exact (nwfs_L_maps_class n).
  - exact (nwfs_R_maps_class n).
  - use make_is_wfs.
    * apply morphism_class_subset_antisymm.
      + exact (nwfs_L_maps_subs_llp_R_maps _).
      + exact (nwfs_llp_R_maps_subs_L_maps _).
    * apply morphism_class_subset_antisymm.
      + exact (nwfs_R_maps_subs_rlp_L_maps _).
      + exact (nwfs_rlp_L_maps_subs_R_maps _).
    * intros x y f.
      apply hinhpr.

      set (fact := n (mor_to_arrow_ob f)).
      set (f01 := three_mor01 fact).
      set (f12 := three_mor12 fact).
      cbn in f01, f12.

      exists (three_ob1 fact), f01, f12.

      repeat split.
      + exact (nwfs_Lf_is_L_map n (three_mor02 fact)).
      + exact (nwfs_Rf_is_R_map n (three_mor02 fact)).
      + exact (three_comp fact).
Qed.
