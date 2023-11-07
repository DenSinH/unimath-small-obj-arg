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
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.Retract.
Require Import CategoryTheory.ModelCategories.Lifting.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.MonadAlgebras.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.

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
    * exact (three_mor12 xxx).
  - intros xxx yyy fff.
    (* simpl. *)
    (* for morphisms we simply forget the 0th morphism *)
    use mors_to_arrow_mor.
    * exact (three_mor11 fff).
    * exact (three_mor22 fff).
    * (* commutativity is just commutativity in the lower diagram *)
      abstract (
        apply pathsinv0;
        exact (pr2 (three_mor_comm fff))
      ).
Defined.

Definition face_map_0_axioms : is_functor face_map_0_data.
Proof.
  split.
  - (* unfold functor_idax. *)
    intro.
    apply subtypePath; [intro; apply homset_property|].
    reflexivity.
  - (* unfold functor_compax. *)
    intros a b c f g.
    apply subtypePath; [intro; apply homset_property|].
    reflexivity.
Qed.

Definition face_map_0 : three C ⟶ arrow C :=
    (_,, face_map_0_axioms).

Definition face_map_2_data : functor_data (three C) (arrow C).
Proof.
  use make_functor_data.
  - intro xxx.
    use tpair.
    * exact (make_dirprod (three_ob0 xxx) (three_ob1 xxx)).
    * simpl.
      exact (three_mor01 xxx).
  - intros xxx yyy fff.
    use mors_to_arrow_mor.
    * exact (three_mor00 fff).
    * exact (three_mor11 fff).
    * abstract (
        exact (pathsinv0 (pr1 (three_mor_comm fff)))
      ).
Defined.

Definition face_map_2_axioms : is_functor face_map_2_data.
Proof.
  split.
  - (* unfold functor_idax. *)
    intro.
    apply subtypePath; [intro; apply homset_property|].
    trivial.
  - (* unfold functor_compax. *)
    intros a b c f g.
    apply subtypePath; [intro; apply homset_property|].
    trivial.
Qed.

Definition face_map_2 : three C ⟶ arrow C :=
    (_,, face_map_2_axioms).

(* verify that they are indeed compatible *)
Lemma face_compatibility (fg : three C) : 
    arrow_mor (face_map_2 fg) · arrow_mor (face_map_0 fg) 
    = arrow_mor (face_map_1 fg).
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
  abstract (
    simpl;
    rewrite id_left;
    apply pathsinv0;
    exact (three_comp xxx)
  ).
Defined.

Definition c_21_axioms : is_nat_trans _ _ c_21_data.
Proof.
  (* natural transformation commutativity axiom *)
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
    intro.
    apply homset_property.
  * (* We are left to prove the commutativity in the base category,
    given our displayed properties. This is effectively just commutativity
    in the bottom square. *)
    apply pathsdirprod.
    + etrans. apply id_right.
      apply pathsinv0.
      apply id_left.
    + apply pathsinv0.
      exact (pr2 (three_mor_comm ff)).
Qed.

Definition c_21 : face_map_2 ⟹ face_map_1 :=
    (_,, c_21_axioms).

Definition c_10_data : nat_trans_data face_map_1 face_map_0.
Proof.
  (* this natural transformation boils down to square
    0 ----> 1
    |       |
    |       |
    2 ===== 2
  *)
  intro xxx.
  exists (make_dirprod (three_mor01 xxx) (identity _)).
  abstract (
    simpl;
    rewrite id_right;
    exact (three_comp xxx)
  ).
Defined.

Definition c_10_axioms : is_nat_trans _ _ c_10_data.
Proof.
  intros xxx yyy ff.
  apply subtypePath.
  - intro x.
    apply homset_property.
  - apply pathsdirprod.
    * apply pathsinv0.
      exact (pr1 (three_mor_comm ff)).
    * etrans. apply id_right.
      apply pathsinv0.
      apply id_left.
Qed.

Definition c_10 : face_map_1 ⟹ face_map_0 :=
    (_,, c_10_axioms).

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
Coercion fact_section {C : category} (F : functorial_factorization C)
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
Qed.

Definition fact_L {C : category} (F : functorial_factorization C) :
    arrow C ⟶ arrow C :=
  F ∙ face_map_2.
Definition fact_R {C : category} (F : functorial_factorization C) : 
    arrow C ⟶ arrow C :=
  F ∙ face_map_0.

(* At least now it knows they are compatible *)
Lemma LR_compatibility {C : category} (F : functorial_factorization C) :
    ∏ (f : arrow C), arrow_mor (fact_L F f) · arrow_mor (fact_R F f) = arrow_mor f.
Proof.
  intro.
  exact (three_comp _).
Qed.

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

Definition lnwfs_over {C : category} (F : functorial_factorization C) :=
    ∑ (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)), Monad_laws (L_monad_data F Σ).

Definition rnwfs_over {C : category} (F : functorial_factorization C) :=
    ∑ (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)), Monad_laws (R_monad_data F Π).

Definition nwfs_over {C : category} (F : functorial_factorization C) :=
    (lnwfs_over F) × (rnwfs_over F).

Definition nwfs (C : category) :=
    ∑ (F : functorial_factorization C), nwfs_over F.

Definition nwfs_over_to_nwfs {C : category} {F : functorial_factorization C} (n : nwfs_over F) : nwfs C :=
    (_,, n).
Coercion nwfs_over_to_nwfs : nwfs_over >-> nwfs.
Definition nwfs_over_to_fact {C : category} {F : functorial_factorization C} (n : nwfs_over F) : functorial_factorization C :=
    F.
Coercion nwfs_over_to_fact : nwfs_over >-> functorial_factorization.

Definition make_nwfs {C : category} (F : functorial_factorization C)
    (Σ : (fact_L F) ⟹ (fact_L F) ∙ (fact_L F)) (L : Monad_laws (L_monad_data F Σ))
    (Π : (fact_R F) ∙ (fact_R F) ⟹ (fact_R F)) (R : Monad_laws (R_monad_data F Π))
        : nwfs C.
Proof.
  exists F.
  split.
  - exists Σ. exact L.
  - exists Π. exact R.
Defined.

Definition nwfs_fact {C : category} (n : nwfs C) := pr1 n.
Coercion nwfs_fact : nwfs >-> functorial_factorization.
Definition nwfs_lnwfs {C : category} (n : nwfs C) := pr12 n.
Coercion nwfs_lnwfs : nwfs >-> lnwfs_over.
Definition nwfs_rnwfs {C : category} (n : nwfs C) := pr22 n.
Coercion nwfs_rnwfs : nwfs >-> rnwfs_over.
Definition nwfs_Σ {C : category} (n : nwfs C) := pr1 (nwfs_lnwfs n).
Definition nwfs_Π {C : category} (n : nwfs C) := pr1 (nwfs_rnwfs n).
Definition nwfs_Σ_laws {C : category} (n : nwfs C) := pr2 (nwfs_lnwfs n).
Definition nwfs_Π_laws {C : category} (n : nwfs C) := pr2 (nwfs_rnwfs n).
Definition rnwfs_R_monad {C : category} {F : functorial_factorization C} (n : rnwfs_over F) := R_monad F (pr1 n) (pr2 n).
Definition lnwfs_L_monad {C : category} {F : functorial_factorization C} (n : lnwfs_over F) := L_monad F (pr1 n) (pr2 n).
Definition nwfs_R_monad {C : category} (n : nwfs C) := rnwfs_R_monad (nwfs_rnwfs n).
Definition nwfs_L_monad {C : category} (n : nwfs C) := lnwfs_L_monad (nwfs_lnwfs n).

(* the following lemmas about Σ and Π are from
   Grandis, Tholen, (6), (7), diagram after (7), (8), (9) *)
(* diagram after (7) *)
Lemma nwfs_Σ_top_map_id {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor00 (nwfs_Σ n f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_L_monad n) f).
  set (top := arrow_mor00_eq law1).
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
  set (bottom := arrow_mor11_eq law1).
  exact bottom.
Qed.

(* σ_f · σ_{λf} = σ_f · F(1_A, σ_f)
  where F(1_a, σ_f) is the map on middle objects of F(Σ_f)
  if we see Σ_f as a morphism in the arrow category
   (9, top right + cancel_postcomposition) *)
Lemma nwfs_Σ_bottom_map_L_is_middle_map_of_Σ {C : category} (n : nwfs C) (f : arrow C) :
    (arrow_mor11 (nwfs_Σ n f)) · arrow_mor11 (nwfs_Σ n (fact_L n f)) =
    (arrow_mor11 (nwfs_Σ n f)) · three_mor11 (functor_on_morphisms n (nwfs_Σ n f)).
Proof.
  set (law3 := Monad_law3 (T:=nwfs_L_monad n) f).
  set (bottom := arrow_mor11_eq law3).
  apply pathsinv0.
  exact bottom.
Qed.

(* diagram after (7) *)
Lemma nwfs_Π_bottom_map_id {C : category} (n : nwfs C) (f : arrow C) :
    arrow_mor11 (nwfs_Π n f) = identity _.
Proof.
  set (law1 := Monad_law1 (T:=nwfs_R_monad n) f).
  set (bottom := arrow_mor11_eq law1).
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
  set (top := arrow_mor00_eq law1).
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
  set (top := arrow_mor00_eq law3).
  apply pathsinv0.
  exact top.
Qed.

(*
 * L-Map AND R-Map FOR AN NWFS n
 **)

(* In a monad algebra, we have [[f αf] laws] : nwfs_R_maps n *)
Definition nwfs_R_maps {C : category} (n : nwfs C) :=
    MonadAlg_disp (nwfs_R_monad n).
Definition nwfs_L_maps {C : category} (n : nwfs C) :=
    MonadAlg_disp (nwfs_L_monad n).
    
(*
Shape of comonad morphism diagram (2.15, Garner)
  A ===== A ===== A  ~~> id_A
  |       |       |
f |   α   |λf  η  | f
  v       v       v
  B ---> Kf ----> B  ~~> id_B
     s       ρ_f
*)
Lemma L_map_section_comm {C : category} {n : nwfs C} {a b : C} {f : a --> b} 
    (hf : nwfs_L_maps n f) (s := pr211 hf) :
  f · s = arrow_mor (fact_L n f) × 
     s · arrow_mor (fact_R n f) = identity _.
Proof.
  set (ida := pr111 hf).
  set (αfcomm := pr21 hf).
  set (hαfη := pr12 hf).
  
  cbn in ida, s, αfcomm.
  simpl in hαfη.

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
    unfold ida in Hida.
    rewrite Hida, id_left in αfcomm'.
    apply pathsinv0.
    exact αfcomm'.
  - (* s · ρ_f = id_b *)
    (* bottom line of hαfη *)
    set (bottom_line := dirprod_pr2 (pathsdirprodweq (base_paths _ _ hαfη))).
    exact bottom_line.
Qed.

Lemma L_map_section {C : category} {n : nwfs C} {a b : C} {f : a --> b} 
    (hf : nwfs_L_maps n f) :
  ∑ s, f · s = arrow_mor (fact_L n f) × 
      s · arrow_mor (fact_R n f) = identity _.
Proof.
  exists (pr211 hf).
  apply L_map_section_comm.
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
Lemma R_map_retraction_comm {C : category} {n : nwfs C} {c d : C} {g : c --> d} 
    (hg : nwfs_R_maps n g) (p := pr111 hg) :
  p · g = arrow_mor (fact_R n g) × 
      arrow_mor (fact_L n g) · p = identity _.
Proof.
  set (idd := pr211 hg).
  set (αgcomm := pr21 hg).
  set (hαgη := pr12 hg).
  
  cbn in p, idd, αgcomm.
  simpl in hαgη.

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
    unfold idd in Hidd.
    rewrite Hidd, id_right in αgcomm'.
    exact αgcomm'.
  - (* λg · p = id_c *)
    (* top line of hαfη *)
    set (top_line := dirprod_pr1 (pathsdirprodweq (base_paths _ _ hαgη))).
    exact top_line.
Qed.

Lemma R_map_section {C : category} {n : nwfs C} {c d : C} {g : c --> d} 
    (hg : nwfs_R_maps n g) :
  ∑ p, p · g = arrow_mor (fact_R n g) × 
      arrow_mor (fact_L n g) · p = identity _.
Proof.
  exists (pr111 hg).
  apply R_map_retraction_comm.
Defined.

Lemma L_map_R_map_elp {C : category} {n : nwfs C} {a b c d : C}
    {f : a --> b} {g : c --> d} (hf : nwfs_L_maps n f)
    (hg : nwfs_R_maps n g) : elp f g.
Proof.
  (* want to construct a lift of an L-map and an R-map
     using monad properties *)
  intros h k H.

  destruct (L_map_section hf) as [s [Hs0 Hs1]].
  destruct (R_map_retraction hg) as [p [Hp0 Hp1]].

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
        s  |       |       |
           |       |  Rg   | g
           v       |       v
           B ----> D ===== D
                k
  *)

  exists (s · Khk · p).
  
  abstract (
    split; [
      (* f · (s · Khk · p) = h *)
      rewrite assoc, assoc;
      rewrite Hs0;
      (* λ_f · Khk · p = h *)
      (* rewrite Hhk0 : (λ_f · Hhk = h · λ_g) *)
      etrans; [apply maponpaths_2;
               exact Hhk0|];
      (* h · λ_g · p = h *)
      (* rewrite Hp1 : (λ_g · p = id_C) *)
      rewrite <- assoc;
      etrans; [apply maponpaths;
               exact Hp1|];
      (* h · id_C = h *)
      now rewrite id_right
    | (* s · Khk · p · g = k *)
      rewrite <- (assoc _ p g);
      rewrite Hp0;
      (* s · Khk · ρ_g = k *)
      (* rewrite Hhk1 : ρ_f · k = Khk · ρ_g *)
      rewrite <- assoc;
      etrans; [apply maponpaths;
               exact (pathsinv0 Hhk1)|];
      (* s · ρ_f · k = k *)
      (* rewrite Hs1 : s · ρ_f = id_B *)
      rewrite assoc;
      etrans; [apply maponpaths_2;
               exact Hs1|];
      (* id_B · k = k *)
      now rewrite id_left
    ]
  ).
Defined.


(*
 * CATEGORY OF NWFS's ON A CATEGORY C
 **)

Section NWFS_cat.

Definition fact_mor {C : category} (F F' : functorial_factorization C) :=
    section_nat_trans_disp F F'.

Definition fact_mor_nt {C : category} {F F' : functorial_factorization C} (α : fact_mor F F') :=
    section_nat_trans α.
Coercion fact_mor_nt : fact_mor >-> nat_trans.

Lemma isaset_fact_mor {C : category} (F F' : functorial_factorization C) : isaset (fact_mor F F').
Proof.
  apply isaset_section_nat_trans_disp.
Qed.

(* verify that indeed, whiskering with d1 yields id_{C^2} ⟹ id_{C^2} *)
Lemma fact_mor_whisker_d1_is_id {C : category} {F F' : functorial_factorization C}
    (α : fact_mor F F') :
    post_whisker α face_map_1 = nat_trans_id (functor_identity _).
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro. (* ~~> identity x = identity x *)
    trivial.
Qed.

Definition Ff_precategory_ob_mor (C : category) : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (functorial_factorization C).
  - intros F F'.
    exact (fact_mor F F').
Defined.

Definition Ff_precategory_id {C : category} (F : functorial_factorization C) : fact_mor F F :=
    section_nat_trans_id F.

Definition Ff_precategory_comp {C : category} (F F' F'' : functorial_factorization C) :
    (fact_mor F F') -> (fact_mor F' F'') -> (fact_mor F F'').
Proof.
  intros α α'.
  exact (section_nat_trans_comp α α').
Defined.

Definition Ff_precategory_data (C : category) : precategory_data.
Proof.
  use make_precategory_data.
  - exact (Ff_precategory_ob_mor C).
  - exact Ff_precategory_id.
  - exact Ff_precategory_comp.
Defined.

Definition Ff_is_precategory (C : category) : is_precategory (Ff_precategory_data C).
Proof.
  use make_is_precategory_one_assoc; intros.
  - apply section_nat_trans_id_left.
  - apply section_nat_trans_id_right.
  - apply section_nat_trans_assoc.
Qed.

Definition Ff_precategory (C : category) : precategory := (_,, Ff_is_precategory C).

Definition has_homsets_Ff (C : category) : has_homsets (Ff_precategory C).
Proof.
  intros F F'.
  use isaset_fact_mor.
Qed.

Definition Ff (C : category) : category := (Ff_precategory C,, has_homsets_Ff C).

Definition lnwfs_mor {C : category} {F F' : functorial_factorization C}
    (n : lnwfs_over F) (n' : lnwfs_over F')
    (α : fact_mor F F') : (lnwfs_L_monad n') ⟹ (lnwfs_L_monad n) :=
  post_whisker (op_nt α) (functor_opp face_map_2).
Definition rnwfs_mor {C : category} {F F' : functorial_factorization C}
    (n : rnwfs_over F) (n' : rnwfs_over F')
    (α : fact_mor F F') : (rnwfs_R_monad n) ⟹ (rnwfs_R_monad n') :=
  post_whisker α face_map_0.

Definition lnwfs_mor_axioms {C : category} {F F' : functorial_factorization C}
    (n : lnwfs_over F) (n' : lnwfs_over F')
    (α : fact_mor F F') :=
  Monad_Mor_laws (lnwfs_mor n n' α).

Lemma isaprop_lnwfs_mor_axioms {C : category} {F F' : functorial_factorization C}
    (n : lnwfs_over F) (n' : lnwfs_over F')
    (α : fact_mor F F') : 
  isaprop (lnwfs_mor_axioms n n' α).
Proof.
  apply isaprop_Monad_Mor_laws, homset_property.
Qed.

Definition rnwfs_mor_axioms {C : category} {F F' : functorial_factorization C}
    (n : rnwfs_over F) (n' : rnwfs_over F')
    (α : fact_mor F F') :=
  Monad_Mor_laws (rnwfs_mor n n' α).

Lemma isaprop_rnwfs_mor_axioms {C : category} {F F' : functorial_factorization C}
    (n : rnwfs_over F) (n' : rnwfs_over F')
    (α : fact_mor F F') : 
  isaprop (rnwfs_mor_axioms n n' α).
Proof.
  apply isaprop_Monad_Mor_laws, homset_property.
Qed.
  
Definition nwfs_mor_axioms {C : category} (n n' : nwfs C) (α : fact_mor n n') :=
    lnwfs_mor_axioms n n' α × rnwfs_mor_axioms n n' α.

Lemma isaprop_nwfs_mor_axioms {C : category} (n n' : nwfs C) (α : fact_mor n n') :
  isaprop (nwfs_mor_axioms n n' α).
Proof.
  apply isapropdirprod.
  - apply isaprop_lnwfs_mor_axioms.
  - apply isaprop_rnwfs_mor_axioms.
Qed.

Definition lnwfs_L_monad_mor {C : category}
    {F F' : functorial_factorization C}
    {n : lnwfs_over F}
    {n' : lnwfs_over F'}
    (α : fact_mor F F')
    (ax : lnwfs_mor_axioms n n' α) : 
      Monad_Mor (lnwfs_L_monad n') (lnwfs_L_monad n) :=
  (lnwfs_mor n n' α,, ax).
  
Definition rnwfs_R_monad_mor {C : category}
    {F F' : functorial_factorization C}
    {n : rnwfs_over F}
    {n' : rnwfs_over F'}
    (α : fact_mor F F')
    (ax : rnwfs_mor_axioms n n' α) :
      Monad_Mor (rnwfs_R_monad n) (rnwfs_R_monad n') :=
  (rnwfs_mor n n' α,, ax).

Context (C : category).

(* We just show that fact_id corresponds with the identity monad morphisms
   on L and R. *)
Lemma fact_id_is_lnwfs_mor {F : functorial_factorization C} (n : lnwfs_over F) : lnwfs_mor_axioms n n (Ff_precategory_id F).
Proof.
  assert (H : lnwfs_mor _ _ (Ff_precategory_id F) = nat_trans_id (lnwfs_L_monad n)).
  {
    use nat_trans_eq; [apply homset_property|].
    intro.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; cbn; trivial.
  }
  unfold lnwfs_mor_axioms.
  rewrite H.
  exact (Monad_identity_laws _).
Qed.

Lemma fact_id_is_rnwfs_mor {F : functorial_factorization C} (n : rnwfs_over F) : rnwfs_mor_axioms n n (Ff_precategory_id F).
Proof.
  assert (H : rnwfs_mor _ _ (Ff_precategory_id F) = nat_trans_id (rnwfs_R_monad n)).
  {
    use nat_trans_eq; [apply homset_property|].
    intro.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; cbn; trivial.
  }
  unfold rnwfs_mor_axioms.
  rewrite H.
  exact (Monad_identity_laws _).
Qed.

(* Lemma fact_id_is_nwfs_mor (n : nwfs C) : nwfs_mor_axioms n n (Ff_precategory_id (nwfs_fact n)).
Proof.
  split.
  - apply fact_id_is_lnwfs_mor.
  - apply fact_id_is_rnwfs_mor.
Qed. *)

Lemma lnwfs_mor_comp {F F' F'' : Ff C}
    {n : lnwfs_over F}
    {n' : lnwfs_over F'}
    {n'' : lnwfs_over F''}
    {α : F --> F'}
    {α' : F' --> F''}
    (ax : lnwfs_mor_axioms n n' α)
    (ax' : lnwfs_mor_axioms n' n'' α') :
  lnwfs_mor_axioms n n'' (α · α').
Proof.
  (* Like for identity, we just show that the composition of the morphisms
     corresponds with the composition of the corresponding L and R monad
     morphisms. *)
  assert (lnwfs_mor n n'' (α · α') =
          nat_trans_comp _ _ _ (lnwfs_L_monad_mor α' ax') (lnwfs_L_monad_mor α ax)) as H.
  {
    use nat_trans_eq.
    - (* for some reason this definition is completely unfolded *)
      exact (homset_property (op_cat (arrow C))).
    - intro x.
      use arrow_mor_eq.
      * apply pathsinv0. 
        apply id_left.
      * cbn.
        unfold three_mor11.
        simpl.
        unfold mor_disp; simpl.
        (* todo: understand what I have done here *)
        rewrite pr1_transportf.
        (* transport along constant function -> just idfun *)
        rewrite transportf_const.
        trivial.
  }
  unfold lnwfs_mor_axioms.
  rewrite H.
  exact (Monad_composition_laws (lnwfs_L_monad_mor α' ax') (lnwfs_L_monad_mor α ax)).
Qed.

Lemma rnwfs_mor_comp {F F' F'' : Ff C}
    {n : rnwfs_over F}
    {n' : rnwfs_over F'}
    {n'' : rnwfs_over F''}
    {α : F --> F'}
    {α' : F' --> F''}
    (ax : rnwfs_mor_axioms n n' α)
    (ax' : rnwfs_mor_axioms n' n'' α') :
  rnwfs_mor_axioms n n'' (α · α').
Proof.
  assert (rnwfs_mor n n'' (α · α') =
          nat_trans_comp _ _ _ (rnwfs_R_monad_mor α ax) (rnwfs_R_monad_mor α' ax')) as H.
  {
    simpl.
    use nat_trans_eq.
    - (* for some reason this definition is completely unfolded *)
      exact (homset_property (arrow C)).
    - intro x; simpl in x.
      apply subtypePath; [intro; apply homset_property|].
      simpl.
      apply pathsdirprod; cbn.
      * unfold three_mor11.
        simpl.
        unfold mor_disp; simpl.
        rewrite pr1_transportf.
        rewrite transportf_const.
        trivial.
      * now rewrite id_left.
  }
  unfold rnwfs_mor_axioms.
  rewrite H.
  exact (Monad_composition_laws (rnwfs_R_monad_mor α ax) (rnwfs_R_monad_mor α' ax')).
Qed.

Definition LNWFS : disp_cat (Ff C).
Proof.
  use disp_cat_from_SIP_data.
  - exact lnwfs_over.
  - exact (@lnwfs_mor_axioms C).
  - intros.
    apply isaprop_lnwfs_mor_axioms.
  - intros.
    apply fact_id_is_lnwfs_mor.
  - intros F F' F'' n n' n'' α α' ax ax'.
    apply (lnwfs_mor_comp ax ax').
Defined.

Definition RNWFS : disp_cat (Ff C).
Proof.
  use disp_cat_from_SIP_data.
  - exact rnwfs_over.
  - exact (@rnwfs_mor_axioms C).
  - intros.
    apply isaprop_rnwfs_mor_axioms.
  - intros.
    apply fact_id_is_rnwfs_mor.
  - intros F F' F'' n n' n'' α α' ax ax'.
    apply (rnwfs_mor_comp ax ax').
Defined.

Definition NWFS : disp_cat (Ff C) :=
    dirprod_disp_cat LNWFS RNWFS.

End NWFS_cat.
