(* Can be found on nlab:
    https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras
Or in G. M. Kelly. A unified treatment of transfinite constructions for free algebras, free
monoids, colimits, associated sheaves
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import CategoryTheory.whiskering.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import CategoryTheory.Monads.PointedEndofunctors.

Local Open Scope Cat.
Local Open Scope cat.

Definition ω_graph : graph.
Proof. 
  use make_graph.
  - exact nat.
  - intros m n.
    (* only arrows m -> m + 1 *)
    exact (n = S m).
Defined.

(* todo: up to isomorphism? *)
Definition ω_sequence_converges {C : category} {d : diagram ω_graph C} (CC : ColimCocone d) : UU :=
    ∑ (a : vertex ω_graph), colim CC = dob d a.

(*
  Inspired by lecture notes by Egbert Rijke linked at
  https://ncatlab.org/nlab/show/sequential+limit, then
  just removed it when I saw what was already in UniMath *)

(* Definition increasing_cat_sequence (C : category) : UU :=
    ∑ (ob : nat -> C), ∏ (n : nat), ob n --> ob (n + 1). *)
(* this definition is the same as diagram ω_graph C. *)

Section ptd_endo_colim.

(* We will end up requiring that C is cocomplete anyway *)
Context {C : category}.
Context (CL : Colims C).
Context (T : pointed_endofunctor C).

Local Definition CLF := ColimsFunctorCategory C C CL.
Local Definition CE := Coequalizers_from_Colims _ CL.
Local Definition CEF := Coequalizers_from_Colims _ CLF.

Local Notation "F □ G" := (functor_composite F G) (at level 35).

(* the horizontal map can be constructed from the vertical map:
              TXβ
                |
                | xβ
                v
  Xβ --------> Xβ1
     τXβ · xβ
  where τ is the unit of our pointed endofunctor (T, τ).
*)
Local Definition pair_diagram : UU :=
    ∑ (x0 x1 : (functor_category C C)), ([C, C]⟦ T □ x0, x1 ⟧).

Local Definition pair_diagram_lob (X : pair_diagram) : functor_category C C :=
    pr1 X.
Local Definition pair_diagram_rob (X : pair_diagram) : functor_category C C :=
    pr12 X.
Coercion pair_diagram_arr (X : pair_diagram) :=
    pr22 X.

Local Definition pair_diagram_horizontal_arrow (X : pair_diagram) : (pair_diagram_lob X) --> (pair_diagram_rob X).
Proof.
  destruct X as [Xβ [Xβ1 xβ]].
  cbn.
  set (τX := post_whisker (ptd_endo_unit T) Xβ : [C, C]⟦Xβ, T □ Xβ⟧).
  exact (τX · xβ).
Defined.

Definition next_pair_diagram (xβ : pair_diagram) : pair_diagram.
Proof.
  destruct xβ as [Xβ [Xβ1 xβ]].
  (* Part of the sequence that we are considering:
    TXβ-1 --> TXβ ----> TXβ1
      |        |         |
      |     xβ |         | xβ1
      v        v         v
      Xβ ----> Xβ1 ----> Xβ2
          fβ
  *)
  (* the next "left object" is Xβ1 *)
  exists Xβ1.

  set (TXβ := T □ Xβ).
  set (TXβ1 := T □ Xβ1).

  set (Tt := pre_whisker T (ptd_endo_unit T) :
                [C, C]⟦_, (T □ T)⟧).
  set (TtXβ := post_whisker Tt Xβ : 
                [C, C]⟦T □ Xβ, (T □ T) □ Xβ⟧).
  set (tT := post_whisker (ptd_endo_unit T) T : 
                [C, C]⟦_, T □ T⟧).
  set (tTXβ := post_whisker tT Xβ : 
                [C, C]⟦T □ Xβ, (T □ T) □ Xβ⟧).
  set (Txβ := pre_whisker T xβ : 
                [C, C]⟦T □ (T □ Xβ), T □ Xβ1⟧).
  (* 
  We define xβ1: TXβ1 ---> Xβ2 by the coequalizer of the two
  composites
      tT        Txβ
  TXβ ===> T2 Xβ --> TXβ1
      Tt
  *)
  rewrite <- functor_assoc in Txβ.
  set (coeq := CEF _ _ (tTXβ · Txβ) (TtXβ · Txβ)).
  set (Xβ2 := CoequalizerObject _ coeq).
  exists Xβ2.

  set (xβ1 := CoequalizerArrow _ coeq).
  exact xβ1.
Defined.

Definition ptd_endo_coeq_sequence_on (A : [C, C]) :
    nat -> pair_diagram.
Proof.
  intro n.
  induction n as [|β xβ].
  - exists A, (T □ A).
    exact (post_whisker (nat_trans_id _) A).
    (* initial arrow is I ⟹ T *)
    (* exists (functor_identity _), (ptd_endo_functor T).
    exact (nat_trans_id _). *)
  - exact (next_pair_diagram xβ).
    (* destruct xβ as [Xβ [Xβ1 xβ]].
    (* Part of the sequence that we are considering:
       TXβ-1 --> TXβ ----> TXβ1
         |        |         |
         |     xβ |         | xβ1
         v        v         v
        Xβ ----> Xβ1 ----> Xβ2
             fβ
    *)
    (* the next "left object" is Xβ1 *)
    exists Xβ1.

    set (TXβ := T □ Xβ).
    set (TXβ1 := T □ Xβ1).
    
    set (Tt := pre_whisker T (ptd_endo_unit T) :
                  [C, C]⟦_, (T □ T)⟧).
    set (TtXβ := post_whisker Tt Xβ : 
                  [C, C]⟦T □ Xβ, (T □ T) □ Xβ⟧).
    set (tT := post_whisker (ptd_endo_unit T) T : 
                  [C, C]⟦_, T □ T⟧).
    set (tTXβ := post_whisker tT Xβ : 
                  [C, C]⟦T □ Xβ, (T □ T) □ Xβ⟧).
    set (Txβ := pre_whisker T xβ : 
                  [C, C]⟦T □ (T □ Xβ), T □ Xβ1⟧).
    (* 
    We define xβ1: TXβ1 ---> Xβ2 by the coequalizer of the two
    composites
         tT        Txβ
    TXβ ===> T2 Xβ --> TXβ1
         Tt
    *)
    rewrite <- functor_assoc in Txβ.
    set (coeq := CEF _ _ (tTXβ · Txβ) (TtXβ · Txβ)).
    set (Xβ2 := CoequalizerObject _ coeq).
    exists Xβ2.
    
    set (xβ1 := CoequalizerArrow _ coeq).
    exact xβ1. *)
Defined.

Definition ptd_endo_coeq_sequence_diagram_on (A : [C, C]) :
    diagram ω_graph (functor_category C C).
Proof.
  set (seq := ptd_endo_coeq_sequence_on A).
  use tpair.
  - intro n.
    exact (pair_diagram_lob (seq n)).
  - simpl.
    intros m n H.
    rewrite H.
    exact (pair_diagram_horizontal_arrow (seq m)).
Defined.

Definition ptd_endo_coeq_sequence_colim_on (A : [C, C]) : 
  ColimCocone (ptd_endo_coeq_sequence_diagram_on A) :=
    CLF _ (ptd_endo_coeq_sequence_diagram_on A).

(* using Proposition 23 in Garner, 2007 (long), can construct
   free monoid from T-Mod that is left adjoint to forgetful functor.
   
   using Proposition*)


(* 
The rest of the construction:
  - Want to create "T-module on A", in our case, we only care if
    A = I (= id_C), since that is the sequence we are going to use
    with R1.
    This can be done with Proposition 27 in Garner, 2007 (long).
    However, we need to construct a map T □ T∞ --> T∞. In 
    Proposition 27, we assume that the module sequence converges
    for some α (as we assume the limit ordinal is α-small).
    I guess in our case, this would boil down to only having a 
    finite number of steps? As ω is not ω-small.
    Garner gives the construction of the required map as 
               θα       Xαα+^{-1}
      T ⊗ Xα ----> Xα+ ---------> Xα
    Where I am assuming the first map is one of the two branches
    for the equalizer in the successor ordinal case, and the second
    map exists because the sequence converges. Just using the 
    colimits as they are in UniMath would give me T∞, but then I 
    cannot use it as if it was an element in this sequence so to say...

    One thing I thought might be possible, but is not what we want to do,
    is that for any β : ℕ, we have this cocone
          Xβ ---> Xβ+1
          |  \     / |
          |   \   /  |
          |    T∞    |
           \    |   /
             \  |  /
               Xβ+1
    which we can apply T to, to obtain a transformation
    T □ T∞ --> T □ Xβ+1
    which we can compose with xβ+1 and the inclusion of Xβ+2 into
    T∞ to obtain a map, but this would factor though a chosen
    Xβ, which seems odd, and not what we want.

    He constructs the universal map from A (so I) to T∞ as X0α,
    which is just the inclusion into the colimit, so that is 
    easy to define.
  - I'm guessing the next step is using Proposition 24, which says
    that if the sequence on I (which is precisely the one we want) exists,
    and we have some condition on the module action, then
    we get an adjoint to the forgetful functor T-alg --> [C, C],
    which I think gives us the fact that T∞-Alg = T-Alg?
    
  - Then the last step is giving the multiplication on (T∞, τ∞).
    This should follow from the proof of Proposition 23, where we 
    get a unit (which I guess should be the same as the one
    we would find from the first point, the universal map from 
    A (so I) to T∞).
    
    The multiplication comes from the adjunction, 
    in combination with the action ⋆ described
    before. To define this action, I may need to first add some 
    more tools to work with whiskering. I can see how (X, x) ⋆ X
    would give the map for the multiplication, and I guess the
    adjunction gives us functorality of the map, but I am not 
    entirely sure why the adjunction even works:

    For (X, x) the free T-monoid over I (which is actually the one we
    want), we define [C, C] --> T-Alg as (X, x) ⋆ (-): A ↦ (X ⊗ A, x ⊗ A)
    Applying the forgetful functor would yield X ⊗ A, which is not the same
    as A, unless X = I, which is not the case, since X would be T∞ in
    our case. Okay, maybe these objects are isomorphic, but why?

  Like before with Garner's construction, using this construction
  may be too "generic" again. It seems like
  in our specific case, with our specific ω-sequence, we
  might be able to construct the unit and multiplication
  on T∞ more directly, and show that the Algebra's are preserved.
  I guess we'd still need to use the idea of the adjunction we obtain,
  but thinking about it, I don't really see how we would obtain the
  map T∞ ⊗ T∞ --> T∞...

*)

(* Definition ptd_endo_coeq_sequence_monad_data : Monad_data C.
Proof.
  set (Tinf := colim ptd_endo_coeq_sequence_colim).
  use tpair.
  - exists Tinf.
    
  - (* unit is inclusion of 0 term (id) into colimit *)
    exact (colimIn ptd_endo_coeq_sequence_colim 0).
Defined. *)

Definition is_ptd_endo_module (X : [C, C]) (x : [C, C]⟦ T □ X, X ⟧) : UU :=
  let τX := post_whisker (ptd_endo_unit T) X : [C, C]⟦ X, T □ X ⟧ in
    x · τX = identity _.

Definition ptd_endo_module : UU :=
    ∑ (X : [C, C]) (x : [C, C]⟦ T □ X, X ⟧), is_ptd_endo_module X x.

Coercion ptd_endo_module_functor (X : ptd_endo_module) : C ⟶ C := pr1 X.
Definition ptd_endo_module_trans (X : ptd_endo_module) := pr12 X.
Definition ptd_endo_module_rel (X : ptd_endo_module) := pr22 X.

Lemma action_is_ptd_endo_module (X : ptd_endo_module) (A : [C, C]) :
    is_ptd_endo_module ((ptd_endo_module_functor X) □ A) (post_whisker (ptd_endo_module_trans X) A).
Proof.
  unfold is_ptd_endo_module.
  rewrite post_whisker_functor_comp.
  etrans. apply pathsinv0.
          exact (post_whisker_composition _ _ _ A _ _ _ (ptd_endo_module_trans X) (post_whisker (ptd_endo_unit T) (ptd_endo_module_functor X))).

  etrans. exact (maponpaths (λ x : (T □ X ⟹ T □ X), post_whisker x A) (ptd_endo_module_rel X)).

  apply nat_trans_eq; [apply homset_property|].
  intro x.
  cbn.
  apply functor_id.
Qed.

Definition ptd_endo_module_action (X : ptd_endo_module) (A : [C, C]) : ptd_endo_module :=
    ((ptd_endo_module_functor X) □ A,, (_,, action_is_ptd_endo_module X A)).

Local Definition ptd_endo_coeq_sequence_colim_unit := 
    ptd_endo_coeq_sequence_colim_on (functor_identity _).
Local Definition Tinf := colim ptd_endo_coeq_sequence_colim_unit.

(* todo: up to iso? *)
Definition preserves_ω_sequences (A : [C, C]) :=
    colim (ptd_endo_coeq_sequence_colim_on A) = 
      Tinf □ A.


Definition ptd_endo_coeq_sequence_Tmod : ptd_endo_module.
Proof.
  exists Tinf.
  assert (H : ω_sequence_converges ptd_endo_coeq_sequence_colim_unit). admit.
  destruct H as [α H].
  change (colim ptd_endo_coeq_sequence_colim_unit) with Tinf in H.
  set (dα := ptd_endo_coeq_sequence_on (functor_identity _) α).
  set (uprop := colimUnivProp ptd_endo_coeq_sequence_colim_unit).
  set (cin := colimIn ptd_endo_coeq_sequence_colim_unit).
  use tpair.
  - apply (postcompose (cin (S α))).
    rewrite H.
    exact (pair_diagram_arr dα).
  - simpl.
    unfold is_ptd_endo_module.
    
    admit.
Admitted.


Definition test (n : nat) : [C, C] ⟦ pair_diagram_rob (ptd_endo_coeq_sequence_on Tinf n), Tinf ⟧.
Proof.
  induction n.
  - change ([C, C]⟦ T □ Tinf, Tinf ⟧).
    (* exact (ptd_endo_module_trans ptd_endo_coeq_sequence_Tmod). *)
    admit.
  - use CoequalizerOut.
    * 

Defined.


Definition test : [C, C]⟦Tinf □ Tinf, Tinf⟧.
Proof.
  assert (H : preserves_ω_sequences Tinf). admit.
  
  rewrite <- H.
  use colimArrow.
  use make_cocone.
  - intro n.
    induction n as [|n Hn].
    * exact (nat_trans_id _).
    * set (test := ptd_endo_module_trans ptd_endo_coeq_sequence_Tmod).
      
      set (Xn := pair_diagram_rob ((ptd_endo_coeq_sequence_on Tinf n))).
      change ([C, C]⟦ Xn , Tinf ⟧).
      unfold Xn.
      admit.
      (* use (CoequalizerOut). *)
  - cbn.
     
  use colimOfArrows.
  - intro n.
    simpl.

Defined.

End ptd_endo_colim.

(* Kelly: chapte 23, see prop 23.2 *)