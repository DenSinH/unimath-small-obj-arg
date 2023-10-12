Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.Retract.
Require Import CategoryTheory.ModelCategories.Lifting.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.NWFSisWFS.
Require Import CategoryTheory.ModelCategories.Generated.Helpers.

Require Import CategoryTheory.DisplayedCats.Examples.MonadAlgebras.
Require Import CategoryTheory.limits.coproducts.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.
Local Open Scope morcls.

Arguments CoproductArrow {_} {_} {_} _ {_}.
Arguments CoproductIn {_} {_} {_} _.
Arguments CoproductInCommutes {_} {_} {_} _ {_}.


Section preliminaries.

Context {C : category}.

Definition morcls_disp (J : morphism_class C) : disp_cat (arrow C) :=
    disp_full_sub (arrow C) (λ g, J _ _ g).

Coercion total_morcls_disp_arrow
    {J : morphism_class C} (f : total_category (morcls_disp J)) :=
  pr1 f.

Definition right_lifting_data (J : morphism_class C) (g : arrow C) : UU :=
    ∏ (f : arrow C), (J _ _ (arrow_mor f)) -> elp f g.

Lemma right_lifting_data_retract (J : morphism_class C) {g g' : arrow C}
    (Rgg' : retract g g') : 
  right_lifting_data J g -> right_lifting_data J g'.
Proof.
  intros rldJg f Jf.
  apply (elp_of_retracts (retract_self f) (Rgg')).
  exact (rldJg f Jf).
Defined.

(* filler lifting problem f --> g commutes with mn and the filler of
   f --> g --> g' in the right way *)
Definition right_lifting_data_comp {J : morphism_class C} {g g' : arrow C}
    (δ : right_lifting_data J g) (δ' : right_lifting_data J g') (mn : g --> g') : UU :=
  ∏ (f : arrow C) (H : J _ _ (arrow_mor f)) (S : f --> g),
  (filler_map (δ f H _ _ (arrow_mor_comm S))) · (arrow_mor00 mn) = 
    filler_map (δ' f H _ _ (arrow_mor_comm (S · mn))).

Lemma isaprop_lifting_data_comp {J : morphism_class C} {g g'} 
    (δ : right_lifting_data J g) (δ' : right_lifting_data J g') (mn : g --> g') :
  isaprop (right_lifting_data_comp δ δ' mn).
Proof.
  do 3 (apply impred; intro).
  apply homset_property.
Qed.

Definition rlp_morcls_disp (J : morphism_class C) : disp_cat (arrow C).
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ g, right_lifting_data J g).
  - intros g g' δ δ' mn. 
    simpl in *.

    (* commutativity of lifting data:
       solution of lifting problem S must commute with mn: g --> g':
                   m
       a ----> x ----> x'
       |       |       |
     f |  S   g|       |
       v       v       v
       b ----> y ----> y'
                   n
      δ : b --> x
      δ': b --> x'
    *)
    exact (right_lifting_data_comp δ δ' mn).
  - (* propositional morphism data *)
    intros.
    apply isaprop_lifting_data_comp.
  - (* identity *)
    intros x a f H S.
    do 2 rewrite id_right.
    reflexivity.
  - (* associativity *)
    intros g g' g'' δ δ' δ'' S0 S1 mn mn' g2 g2' S2.
    
    (* associativity of taking the 00 morphism of an arrow morphism *)
    assert (arrow_mor00 (S0 · S1) = arrow_mor00 S0 · arrow_mor00 S1) as X.
    {
      trivial.
    }
    abstract (
      rewrite X, assoc;
      rewrite mn, mn', assoc;
      reflexivity
    ).
Defined.

Definition rlp_morcls (J : morphism_class C) : category := 
    total_category (rlp_morcls_disp J).

(* needed later *)
(* all lifting problems of J wrt. g *)
Definition morcls_lp (J : morphism_class C) (g : arrow C) : UU :=
    ∑ (f : total_category (morcls_disp J)), (pr1 f) --> g.

Coercion morcls_lp_diagram {J : morphism_class C} {g : arrow C} (lp : morcls_lp J g) := pr2 lp.
Definition morcls_lp_map {J : morphism_class C} {g : arrow C} (lp : morcls_lp J g) := pr1 lp.

Context (n : nwfs C).
Definition morcls_L_map_structure (J : morphism_class C) : UU := 
  disp_functor (functor_identity _) (op_disp_cat (morcls_disp J)) (nwfs_L_maps n).

Context {J : morphism_class C}.

Definition R_map_rlp_morcls_structure_on_objects (η : morcls_L_map_structure J) : 
    ∏ x, (nwfs_R_maps n) x -> (rlp_morcls_disp J) ((functor_identity _) x).
Proof.
  (* map on displayed objects (send arrow to itself, with lifting data) *)
  intros f Rf.
  intros g hg h k S.

  (* add structure to f through η *)
  unfold morcls_L_map_structure in η.
  set (Lg := η g hg).
  
  intros.
  (* since η lies over (identity _), 
     Lg is actually just g (with structure), and it is an L-Map
     the filler follows from the fact that NWFS L-Maps and R-Maps
     form a WFS *)
  apply (L_map_R_map_elp Lg Rf).
Defined.

Definition R_map_rlp_morcls_structure_on_displayed_mors (η : morcls_L_map_structure J) : 
    ∏ x y (xx : (nwfs_R_maps n) x) (yy : (nwfs_R_maps n) y) (f : x --> y),
      (xx -->[f] yy) -> (R_map_rlp_morcls_structure_on_objects η _ xx -->[ f ] R_map_rlp_morcls_structure_on_objects η _ yy).
Proof.
  (* map on displayed objects respects morphism property *)
  intros f f' ff ff' S Sisalg g Jg Sgf.
  unfold morcls_L_map_structure in η.
  simpl.
  unfold three_mor11.
  simpl.
  (* cancel precomposition with  
    pr211 η g Jg := Lift of g vs ρg (map from cod g --> three_ob1 (n g)) *)
  do 3 rewrite assoc'.
  apply cancel_precomposition.

  (* cancel precomposition with 
    three_mor11 (#n Sgf)*)
  (* first "fix" the morphisms, since the (propositional) 
     commutativity is not equal *)
  etrans. apply maponpaths_2.
  use (section_disp_on_eq_morphisms' (nwfs_fact n) (γ := Sgf)).

  apply pathsinv0.
  etrans. apply maponpaths_2.
          use (section_disp_on_eq_morphisms' (nwfs_fact n) (γ := Sgf · S)).
  etrans. apply maponpaths_2, maponpaths.
          apply (section_disp_comp (nwfs_fact n)).
  simpl.

  rewrite assoc'.
  apply cancel_precomposition.

  destruct ff as [αf αflaws].
  destruct ff' as [αf' αf'laws].
  set (S11 := three_mor11 ((# n)%Cat S)).
  change (S11 · arrow_mor00 αf' = arrow_mor00 αf · arrow_mor00 S).

  (*         S00
      ++++> +++++>
    |      |      |
    |   λf |      |λf'
    |      v S11  v
 ρf | αf    +++++> +++++++>
    |      |      |        |
    |   ρf |      |ρf' αf' | f'
    v      v      v        v
      ===== -----> ========
            S22
  Need to show that the +++> maps are equal
  This follows from the fact that S is an algebra map (Sisalg)
  *)

  simpl in Sisalg.
  unfold is_Algebra_mor in Sisalg.
  set (top_line := arrow_mor00_eq Sisalg).
  simpl in top_line.
  exact (pathsinv0 top_line).
Qed.


(* "this assignation extends to a functor θ: R-Map ⟶ J□", Garner 2007, p18 *)
Definition R_map_rlp_morcls_structure_data (η : morcls_L_map_structure J) : 
    disp_functor_data (functor_identity _) (nwfs_R_maps n) (rlp_morcls_disp J) :=
  (R_map_rlp_morcls_structure_on_objects η,, R_map_rlp_morcls_structure_on_displayed_mors η).

Definition R_map_rlp_morcls_structure_axioms (η : morcls_L_map_structure J) :
    disp_functor_axioms (R_map_rlp_morcls_structure_data η).
Proof.
  unfold disp_functor_axioms.
  split; intros; apply isaprop_lifting_data_comp.
Qed.

Definition R_map_rlp_morcls_structure (η : morcls_L_map_structure J) : 
    disp_functor (functor_identity _) (nwfs_R_maps n) (rlp_morcls_disp J) :=
  (_,, R_map_rlp_morcls_structure_axioms η).

(* Garner 2008, Definition 3.9 / Garner 2007, p18*)
(* we say that n := (L, R, Δ) is cofibrantly generated by (J, η) if θ is
   an isomorphism of categories *)
Definition cofibrantly_generated (η : morcls_L_map_structure J) :=
    is_equiv_over (_,, identity_functor_is_adj_equivalence) (R_map_rlp_morcls_structure η).

Definition algebraically_free : UU :=
    ∑ η : morcls_L_map_structure J, cofibrantly_generated η.


(* Garner 2008, Proposition 3.12 / Garner 2007, p18 *)
Lemma algebraically_free_nwfs_gives_cofibrantly_generated_wfs :
  algebraically_free -> 
    (nwfs_R_maps_class n)^cl = λ x y f, ∥rlp_morcls_disp J f∥.
Proof.
  intro H.
  destruct H as [η cofibη].
  unfold cofibrantly_generated in cofibη.

  (* suffices to show R = J□ *)
  apply morcls_eq_impl_morcls_cl_eq.
  {
    (* J□ is closed under retracts *)
    intros x' y' g' x y g Hg.
    destruct Hg as [Jg Rgg'].
    use (hinhuniv _ Jg).
    clear Jg; intro Jg.

    apply hinhpr.
    intros f Jf.
    simpl in Jg.
    apply (@right_lifting_data_retract J g g').
    - exact Rgg'.
    - exact Jg.
    - exact Jf.
  }

  apply morphism_class_subset_antisymm; 
    intros x y f Hf;
    use (hinhuniv _ Hf);
    clear Hf; intro Hf;
    apply hinhpr.
  - (* R-Map ⊆ J□ *)
    set (θ := R_map_rlp_morcls_structure η).
    (* θ is a functor that lies over identity *)
    exact (θ f Hf).
  - (* J□ ⊆ R-Map *)
    (* the "inverse" of θ also lies over identity *)
    set (θinv := right_adjoint_of_is_equiv_over _ cofibη).
    exact (θinv f Hf).
Qed.

End preliminaries.


(* Garner 2007, p19 *)

Section lifting_with_J.
Context {C : category} (n : nwfs C) (J : morphism_class C).
Context (g : arrow C) (CC : Coproducts (morcls_lp J g) C) (POs : Pushouts C).

Definition morcls_lp_dom_coprod :=
  CC (λ (f : morcls_lp J g), arrow_dom (pr1 (morcls_lp_map f))).
Definition morcls_lp_cod_coprod :=
  CC (λ (f : morcls_lp J g), arrow_cod (pr1 (morcls_lp_map f))).

Definition morcls_lp_coprod :=
 (CoproductOfArrows' _ _ 
   morcls_lp_dom_coprod morcls_lp_cod_coprod
   (λ (f : morcls_lp J g), arrow_mor (pr1 (morcls_lp_map f)))).

(* the canonical diagram capturing all lifting problems in J *)
Definition morcls_lp_coprod_diagram : morcls_lp_coprod --> g.
Proof.
  use mors_to_arrow_mor.
  - exact (CoproductArrow (morcls_lp_dom_coprod) (λ j, arrow_mor00 j)).
  - exact (CoproductArrow (morcls_lp_cod_coprod) (λ j, arrow_mor11 j)).
  - abstract (
      unfold morcls_lp_coprod;
      simpl;
      rewrite postcompWithCoproductArrow;
      rewrite precompWithCoproductArrow;
      apply maponpaths;
      apply funextsec;
      intro j;
      exact (arrow_mor_comm j)
    ).
Defined.

(* It is possible to show this more generally for _any_
   coproduct of maps in J, but this is not really necessary or useful
   for us.
   
   The proof of this lemma is practically the same as that of 
   wfs_closed_coproducts, but we do _not_ need the axiom of choice here,
   since we know the actual lifting data. *)
Lemma lifting_data_impl_lifting_coprod_lp : 
  right_lifting_data J g -> elp (morcls_lp_coprod) g.
Proof.
  intro rldJg.
  intros h k S.

  set (hj := λ (j : morcls_lp J g), (CoproductIn _ j) · h).
  set (kj := λ (j : morcls_lp J g), (CoproductIn _ j) · k).

  (* fill-in for each square *)
  assert (∏ (j : morcls_lp J g), ∑ lj, ((pr1 (morcls_lp_map j)) · lj = hj j) × (lj · g = kj j)) as jlift.
  { 
    intro j.
    (* use lifting data of j with respect to g *)
    use (rldJg (pr1 (morcls_lp_map j)) (pr2 (morcls_lp_map j))).
    unfold hj, kj.
    rewrite <- assoc.
    etrans. apply maponpaths. exact S.
    rewrite assoc, assoc.
    etrans. apply maponpaths_2.
    unfold morcls_lp_coprod.
    exact (CoproductOfArrows'In _ _ _ _ _ j).
    reflexivity.
  }

  set (jlifts := foralltototal _ _ jlift).
  destruct jlifts as [lj hlj].
  set (hl := isCoproduct_Coproduct _ _ (morcls_lp_cod_coprod) _ lj).
  destruct hl as [[l hl] uniqueness].
  
  exists l.
  split; rewrite CoproductArrowEta, (CoproductArrowEta _ _ _ _ _ l).
  - (* factor f as well *)
    unfold morcls_lp_coprod.
    rewrite (precompWithCoproductArrow).

    (* maps are equal if maps through coproduct are equal *)
    apply CoproductArrowUnique.

    (* now we can reason in separate diagrams again *)
    intro j.
    rewrite (CoproductInCommutes (morcls_lp_dom_coprod)).

    (* this is basically exactly the relation we want to prove: *)
    destruct (hlj j) as [hljcomm _].

    (* by definition *)
    change (CoproductIn _ _ · h) with (hj j).
    rewrite (hl j).
    exact hljcomm.
  - (* factor through coproduct object *)
    apply CoproductArrowUnique.

    (* reason about separate diagrams again *)
    intro j.
    rewrite assoc.
    rewrite (CoproductInCommutes (morcls_lp_cod_coprod)).

    (* the relation we want to prove *)
    destruct (hlj j) as [_ kljcomm].

    (* by definition *)
    change (CoproductIn _ _ · k) with (kj j).
    rewrite (hl j).
    exact kljcomm.
Qed.

(* we need the actual diagram for the other direction 
   (this does not hold for just any coproduct) *)
Lemma lifting_coprod_lp_impl_lifting_data : 
  filler (arrow_mor_comm (morcls_lp_coprod_diagram)) ->
      right_lifting_data J g.
Proof.
  intro l.
  intros f Jf h k H.

  (* obtain maps in total diagram *)
  destruct l as [ltot [Hl1 Hl2]].
  simpl in Hl1, Hl2, ltot.

  (* The lift we are looking for is formed using the  
     inclusion of arrow_cod f into the coproduct of all domains *)
  set (Jtot := total_category (morcls_disp J)).

    (* f as object of the total category of the morphism class J *)
  set (f' := (f,, Jf) : Jtot).
    (* H as lifting problem J --> g *)
  set (Hlp := (f',, (make_dirprod h k,, H)) : morcls_lp J g).
    (* inclusion of arrow_cod/dom f into coproduct of all domains *)
  set (codf_in := (CoproductIn (morcls_lp_cod_coprod) Hlp)).
  set (domf_in := (CoproductIn (morcls_lp_dom_coprod) Hlp)).

  exists (codf_in · ltot).
  split.
  - (* h = (inclusion of arrow_dom f) · (top morphism of canonical diagram) *)
    assert (h = domf_in · (arrow_mor00 (morcls_lp_coprod_diagram))) as Hh.
    {
      unfold domf_in.
      symmetry.
      
      exact (CoproductInCommutes (morcls_lp_dom_coprod) _ Hlp).
    }
    rewrite Hh.

    (* commutativity of f with inclusions of domain / codomain *)
    assert (f · codf_in = domf_in · (morcls_lp_coprod)) as Hf.
    {
      unfold codf_in, domf_in, morcls_lp_coprod.
      rewrite (CoproductOfArrows'In _ _ (morcls_lp_dom_coprod)).
      reflexivity.
    }
    rewrite assoc.
    etrans. apply maponpaths_2.
            exact Hf.
    rewrite <- assoc.
    now rewrite Hl1.
  - rewrite <- assoc.
    etrans. apply maponpaths.
            exact Hl2.

    apply pathsinv0.

    (* k = codf_in · kj *)
    unfold codf_in.
    symmetry.
    exact (CoproductInCommutes (morcls_lp_cod_coprod) _ Hlp).
Qed.

Lemma lifting_data_Jg_iff_lifting_coprod_lp : 
  right_lifting_data J g <->
    filler (arrow_mor_comm (morcls_lp_coprod_diagram)).
Proof.
  split.
  - intro rldJg.
    apply lifting_data_impl_lifting_coprod_lp.
    exact rldJg.
  - apply lifting_coprod_lp_impl_lifting_data.
Qed.

(*
We turn the diagram
          h_x
    ∑A_x ----> C
     |         |
∑f_x |         | g
     v         v
    ∑B_x ----> D
          k_x

into the pushout diagram
         h_x
    ∑A_x ----> C--\ 
     |         |  |
∑f_x |     λ1g |  \
     v         v   |
    ∑B_x ---> E1g  | id · g
      \__       \  |
         \_   ρ1g|
      k_x  \_____ \|
                   D
using the pushout property. Inserting an identity morphism gives a diagram
          h_x
    ∑A_x ----> C ====== C
     |         |        |
∑f_x |         | λ1g    |
     v         v        v
    ∑B_x ---> E1g ----> D  ~~> k_x
                   ρ1g
*)

Definition morcls_lp_coprod_diagram_pushout :
    Pushout (morcls_lp_coprod) (arrow_mor00 morcls_lp_coprod_diagram) :=
  POs _ _ _ (morcls_lp_coprod) (arrow_mor00 morcls_lp_coprod_diagram).

Definition E1 : C :=
  PushoutObject morcls_lp_coprod_diagram_pushout.
Definition λ1 : (arrow_dom g) --> E1 :=
  PushoutIn2 morcls_lp_coprod_diagram_pushout.
Definition ρ1 : E1 --> (arrow_cod g) :=
  PushoutArrow 
    morcls_lp_coprod_diagram_pushout
    _ (arrow_mor11 morcls_lp_coprod_diagram)
    g (pathsinv0 (arrow_mor_comm morcls_lp_coprod_diagram)).

Definition λ1_ρ1_compat : λ1 · ρ1 = g.
Proof.
  etrans. apply PushoutArrow_PushoutIn2.
  reflexivity.
Qed.

(*
    C ===== C
    |       |
 λ1g|       | g
    v       v
   E1g ---> D
       ρ1g
*)
Definition morcls_lp_coprod_diagram_red : λ1 --> g.
Proof.
  use mors_to_arrow_mor.
  - exact (identity _).
  - exact ρ1.
  - abstract (
      rewrite id_left;
      exact (pathsinv0 λ1_ρ1_compat)
    ).
Defined.

(*
    λ1g
  C ---> E1g
  |       |
 g|       | ρ1g
  v       v
  D ===== D
*)
Definition morcls_lp_coprod_diagram_red_flipped : g --> ρ1.
Proof.
  use mors_to_arrow_mor.
  - exact λ1.
  - exact (identity _).
  - abstract (
      rewrite id_right;
      exact (λ1_ρ1_compat)
    ).
Defined.

(* Lifting w.r.t. the coproduct diagram of J is the same as lifting
   w.r.t. this reduced diagram (follows from pushout properties) *)
Lemma lifting_coprod_lp_red_impl_lifting_coprod_lp :
    filler (arrow_mor_comm (morcls_lp_coprod_diagram_red)) ->
  filler (arrow_mor_comm (morcls_lp_coprod_diagram)).
Proof.
  intro H.
  destruct H as [l [Hl1 Hl2]].
  simpl in Hl1, Hl2.
  exists ((PushoutIn1 morcls_lp_coprod_diagram_pushout) · l).
  split; simpl.
  - (* ∑fx · (PushoutIn1 · l) = ∑hx *)
    rewrite assoc.
    rewrite (PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout)).
    
    (* ∑hx · λ1g · l = ∑hx *)
    rewrite <- assoc.
    etrans. apply maponpaths. exact Hl1.
    now rewrite id_right.
  - (* (PushoutIn1 · l) · g = ∑kx *)
    rewrite <- assoc.
    etrans. apply maponpaths. exact Hl2.
    
    (* PushoutIn1 · ρ1g = ∑kx *)
    use PushoutArrow_PushoutIn1.
Qed.

Lemma lifting_coprod_lp_impl_lifting_coprod_lp_red :
    filler (arrow_mor_comm (morcls_lp_coprod_diagram)) ->
  filler (arrow_mor_comm (morcls_lp_coprod_diagram_red)).
Proof.
  intro H.
  destruct H as [l [Hl1 Hl2]].
  simpl in Hl1, Hl2.
  
  (* commutativity of f · l = ∑hx · id *)
  assert (H : morcls_lp_coprod · l = 
            arrow_mor00 morcls_lp_coprod_diagram · identity _).
  {
    rewrite id_right.
    exact Hl1.
  }

  (* obtain lift using pushout property on lift *)
  set (lred := PushoutArrow 
                  morcls_lp_coprod_diagram_pushout
                  _ l (identity _) H).
  exists lred.
  split.
  - (* λ1g · lred = identity *)
    apply PushoutArrow_PushoutIn2.
  - (* lred · g = ρ1g *)
    simpl.
    use PushoutArrowUnique; simpl.
    * (* PushoutIn1 · (lred · g) = ∑kx*)
      rewrite assoc.
      etrans. apply maponpaths_2.
      apply PushoutArrow_PushoutIn1.
      exact Hl2.
    * (* PushoutIn2 · (lred · g) = g*)
      rewrite assoc.
      etrans. apply maponpaths_2.
      apply PushoutArrow_PushoutIn2.
      now rewrite id_left.
Qed.

(* almost proposition 12 in Garner, 2007 *)
Lemma lifting_coprod_lp_iff_lifting_coprod_lp_red :
    filler (arrow_mor_comm (morcls_lp_coprod_diagram)) <->
  filler (arrow_mor_comm (morcls_lp_coprod_diagram_red)).
Proof.
  split.
  - exact lifting_coprod_lp_impl_lifting_coprod_lp_red.
  - exact lifting_coprod_lp_red_impl_lifting_coprod_lp.
Qed.

Definition Λ1 : g --> ρ1.
Proof.
  use mors_to_arrow_mor.
  - exact λ1.
  - exact (identity _).
  - abstract (
      rewrite id_right, <- id_left;
      apply pathsinv0;
      exact (arrow_mor_comm morcls_lp_coprod_diagram_red)
    ).
Defined.

(* Proposition 12 *)
Lemma lifting_data_Jg_iff_maps :
    right_lifting_data J g <->
      ∑ (γ : ρ1 --> g), Λ1 · γ = identity _.
Proof.
  apply (logeq_trans lifting_data_Jg_iff_lifting_coprod_lp).
  apply (logeq_trans lifting_coprod_lp_iff_lifting_coprod_lp_red).

  split; intro H.
  - destruct H as [l [lcomm1 lcomm2]].
    use tpair.
    * use mors_to_arrow_mor.
      + exact l.
      + exact (identity _).
      + rewrite id_right.
        exact lcomm2.
    * simpl.
      apply subtypePath; [intro; apply homset_property|].
      apply pathsdirprod.
      + exact lcomm1.
      + now rewrite id_left.
  - destruct H as [γ γcomm].
    exists (arrow_mor00 γ).
    set (γcomm1 := arrow_mor00_eq γcomm).
    set (γcomm2 := arrow_mor11_eq γcomm).
    split.
    * exact γcomm1.
    * etrans. exact (arrow_mor_comm γ).
      simpl in γcomm2.
      rewrite id_left in γcomm2.
      now rewrite γcomm2, id_right.
Qed.

End lifting_with_J.