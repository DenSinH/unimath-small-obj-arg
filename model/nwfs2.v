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

(* Can't use SIP since morphism data is not propositional (∑-type)
   For example in SET, we could have a map in
   the arrow category sending everything to one element, factorize
   it through (self, id), we may have multiple morphisms in the middle,
   so long as the one element maps properly... 
   
   So we have to do things the long way: *)

Definition three_disp_ob_mor : disp_cat_ob_mor (arrow C).
Proof.
  use make_disp_cat_ob_mor.
  - exact ((λ xy, ∑ z (xz : (arrow_dom xy) --> z) (zy : z --> (arrow_cod xy)), xz · zy = arrow_mor xy)).
  - (* double commutative square *)
    simpl.
    intros xy ab H0 H1 fff.
    destruct H0 as [z [xz [zy]]].
    destruct H1 as [c [ac [cb]]].
    destruct fff as [[f0 f1]].
    exact (∑ (f : z --> c), (xz · f = f0 · ac) × (zy · f1 = f · cb)).
Defined.

Definition three_id_comp : disp_cat_id_comp _ three_disp_ob_mor.
Proof.
  split.
  - simpl.
    intros.
    (* middle morphism is also identity *)
    exists (identity _).
    split; now rewrite id_left, id_right.
  - simpl.
    intros.
    destruct X as [f0 [H0 H1]].
    destruct X0 as [g0 [K0 K1]].
    (* middle map of composite is composite of middle maps *)
    exists (f0 · g0).
    split.
    * rewrite assoc, H0, <- assoc.
      etrans. apply maponpaths.
      exact K0.
      now rewrite assoc.
    * rewrite <- assoc, <- K1, assoc, assoc.
      apply cancel_postcomposition.
      exact H1.
Defined.

Definition three_data : disp_cat_data _ :=
    (three_disp_ob_mor,, three_id_comp).

Definition three_axioms : disp_cat_axioms _ three_data.
Proof.
  repeat apply tpair; intros.
  (* very cool from CategoryTheory/DisplayedCats/Codomain.v: cod_disp_axioms *)
  - (* subtypePath: equality in ∑-types if pr2 is a predicate *)
    apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }

    (* left identity in base category *)
    simpl.
    etrans. apply id_left.

    destruct ff as [ff H].
    apply pathsinv0.
    
    (* todo: understand this *)
    etrans. 
    use (pr1_transportf (A := x --> y)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }
    simpl.
    etrans. apply id_right.
    destruct ff as [ff H].
    apply pathsinv0.
    etrans. use (pr1_transportf (A := x --> y)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply subtypePath.
    { intro. apply isapropdirprod; apply homset_property. }
    simpl.
    etrans. apply assoc.
    destruct ff as [ff H].
    apply pathsinv0.
    etrans. use (pr1_transportf (A := x --> w)).
    cbn; apply (eqtohomot (transportf_const _ _)).
  - apply isaset_total2.
    * apply homset_property.
    * intro.
      apply isasetdirprod; apply isasetaprop; apply homset_property.    
Defined.

Definition three_disp : disp_cat (arrow C) :=
    (three_data,, three_axioms).

Definition three : category := total_category three_disp.

End Three_disp.

Definition three_ob0 {C : category} (xyz : three C) : C := pr111 xyz.
Definition three_ob1 {C : category} (xyz : three C) : C := pr12 xyz.
Definition three_ob2 {C : category} (xyz : three C) : C := pr211 xyz.
Definition three_mor01 {C : category} (xyz : three C) := pr122 xyz.
Definition three_mor12 {C : category} (xyz : three C) := pr1 (pr222 xyz).
Definition three_mor02 {C : category} (xyz : three C) := arrow_mor (pr1 xyz).
Definition three_comp {C : category} (xyz : three C) := pr2 (pr222 xyz).
Definition three_mor00 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr111 fff.
Definition three_mor11 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr12 fff.
Definition three_mor22 {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr211 fff.
Definition three_mor_comm {C : category} {xxx yyy : three C} (fff : xxx --> yyy) := pr22 fff.

Section Disp_cat_self.

Context (C : category).

Definition self_disp : disp_cat C.
Proof.
  use disp_cat_from_SIP_data; simpl; intros.
  - exact unit.
  - exact unit.
  - apply isapropunit.
  - exact tt.
  - exact tt.
Defined.

Definition self : category := total_category self_disp.

End Disp_cat_self.

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
    * unfold functor_idax.
      intro.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
    * unfold functor_compax.
      intros.
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
    * unfold functor_idax.
      intro.
      apply subtypePath.
      + intro; apply homset_property.
      + trivial.
    * unfold functor_compax.
      intros.
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
      given our displayed properties *)
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
    (three_ob0 (F f)) = arrow_dom f.
Proof.
  (* todo: why do I _have_ to use pr1 here (coercion)? *)
  change (arrow_dom (((pr1 F) ∙ face_map_1) f) = arrow_dom f).
  rewrite (fact_cond F).
  trivial.
Defined.

Lemma fact_preserves_cod {C : category} (F : functorial_factorization C) (f : arrow C) :
    (three_ob2 (F f)) = arrow_cod f.
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
  assert (three_ob2 (F f) = arrow_cod f).
  {
    apply fact_preserves_cod.
  }
  assert (three_ob0 (F f) = arrow_dom f).
  {
    apply fact_preserves_dom.
  }

  unfold three_ob2 in X.
  unfold arrow_cod in X.
  unfold three_ob0 in X0.
  unfold arrow_dom in X0.
  unfold three_ob2 in X.
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
  rewrite <- (fact_cond F).
  exact (pre_whisker F (c_21 C)).
Defined.

(* similar here *)
(* Definition fact_Λ {C : category} (F : functorial_factorization C) :=
    pre_whisker F (c_10 C). *)
Definition Λ {C : category} (F : functorial_factorization C) :
    (functor_identity (arrow C)) ⟹ (fact_R F).
Proof.
  rewrite <- (fact_cond F).
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



(*
Diagram in NWFS to WFS for "weak" definition of NWFS:
            h
  A ~~~~ A ----> ? ~~~~ C~
  |      |       |      |  ~
f |  αf  |       |      |    ~
  v      v  Khk  v      v   p  ~
  B ---> Kf ---> ? ~~~~ Kg ---> C
   ~ s   |       |      |       |
     ~   |       |      |  αg   | g
       ~ v       v      |       v
         B ----> ? ~~~~ D ~~~~~ D
             k
*)


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
        (* Kf --> Kg *)
        (* set (Khk := three_mor11 Fhk).  *)

        (* commutativity in bottom diagram *)
        set (Hhk2 := three_mor_comm Fhk).
        cbn in Hhk2.

        (*    
                    h
         A ==== A ----> C
         |      |       |
       f |  αf  |       |
         v      v  Khk  v   p
         B ---> Kf ---> Kg ---> C
            s   |       |       |
                |       |  αg   | g
                v       |       v
                B ----> D ===== D
                    k
        *)

        exists (s · (three_mor11 Fhk) · p).
        split.
        -- (* f · (s · Khk · p) = h *)
           admit.
        -- (* s · Khk · p · g = k *)
           rewrite <- (assoc _ p g).
           rewrite αgcomm.
           rewrite <- (assoc s _ _).
           etrans.
           apply maponpaths_1.
           rewrite (assoc _ _ idd).
           apply maponpaths_2.
           exact (pathsinv0 (pr2 Hhk2)).
           (* now the LHS goes along the bottom of the
              above diagram *)
           set (Fhkk := three_mor22 Fhk).
           simpl in Fhkk.
           
           (* domain of Fhkk *)
           assert (three_ob2 (nwfs_fact n (mor_to_arrow_ob g)) = d) as codg.
           {
             exact (fact_preserves_cod (nwfs_fact n) (mor_to_arrow_ob g)).
           }

           (* codomain of Fhkk *)
           assert (three_ob2 (nwfs_fact n (mor_to_arrow_ob f)) = b) as codf.
           {
             exact (fact_preserves_cod (nwfs_fact n) (mor_to_arrow_ob f)).
           }
           
           unfold three_ob2 in codf, codg.
           rewrite codf in Fhkk.
           (* assert ((pr211 Fhk) = k). *)
           admit.
      + admit.
    * (* this should just be the same as above *)
      admit.
    * intros x y f.
      set (farr := mor_to_arrow_ob f).
      set (fact := nwfs_fact n farr).
      (* destruct fact as [[x0 [x1 x2]] [f01 f12]]. *)
      (* simpl in f01, f12. *)

      (* rewrite <- (fact_preserves_dom (nwfs_fact n) farr) in f01. *)

      apply hinhpr.
      exists (three_ob1 fact).
      (* we know that x0 = x and x2 = y, but this is not automatically rewritten *)
      set (f01 := three_mor01 fact).
      fold (three_ob0 (C:=C) fact) in f01.
      assert ((three_ob0 fact) = x) as Hx.
      {
        exact (fact_preserves_dom (nwfs_fact n) farr).
      }
      unfold three_ob0 in Hx.
      unfold arrow_dom in f01.
      rewrite Hx in f01.
      exists f01.

      set (f12 := three_mor12 fact).
      simpl in f12.
      assert ((three_ob2 fact) = y) as Hy.
      {
        exact (fact_preserves_cod (nwfs_fact n) farr).
      }
      unfold three_ob2 in Hy.
      unfold arrow_cod in f12.
      rewrite Hy in f12.
      exists f12.

      repeat split.
      + unfold nwfs_L_maps_class.
        unfold isCoAlgebra.
        admit.
      + admit.
      + set (test := fact_cond (nwfs_fact n)).
        (* this is precisely fact_cond (nwfs_fact n) applied to f *)
        admit.
Admitted.
