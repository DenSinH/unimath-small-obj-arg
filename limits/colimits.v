Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Local Open Scope cat.
Local Open Scope stn.


Definition graph_zig_zag_of_length
           {g : graph}
           (n : ℕ)
  : ∏ (x y : vertex g), UU.
Proof.
  induction n as [ | n IHn ].
  - exact (λ x y, x = y).
  - exact (λ x y, ∑ (z : vertex g), ((edge x z) ⨿ (edge z x)) × IHn z y).
Defined.

Definition graph_zig_zag
          {g : graph}
          (x y : vertex g)
  : UU
  := ∑ (n : ℕ), graph_zig_zag_of_length n x y.

Definition length_of_graph_zig_zag
           {g : graph}
           {x y : vertex g}
           (gs : graph_zig_zag x y)
  : ℕ
  := pr1 gs.

Definition empty_graph_zig_zag
           {g : graph}
           (x : vertex g)
  : graph_zig_zag x x
  := 0 ,, idpath x.

Definition left_cons_graph_zig_zag
           {g : graph}
           {x z y : vertex g}
           (f : edge x z)
           (gs : graph_zig_zag z y)
  : graph_zig_zag x y
  := 1 + length_of_graph_zig_zag gs ,, (z ,, (inl f ,, pr2 gs)).

Definition right_cons_graph_zig_zag
           {g : graph}
           {x z y : vertex g}
           (f : edge z x)
           (gs : graph_zig_zag z y)
  : graph_zig_zag x y
  := 1 + length_of_graph_zig_zag gs ,, (z ,, (inr f ,, pr2 gs)).

Definition append_graph_zig_zag_of_length
           {g : graph}
           {n m : ℕ}
           {x y z : vertex g}
           (fs : graph_zig_zag_of_length n x y)
           (gs : graph_zig_zag_of_length m y z)
  : graph_zig_zag_of_length (n + m) x z.
Proof.
  revert x y z fs gs.
  induction n as [ | n IHn ].
  - intros x y z fs gs.
    rewrite fs.
    exact gs.
  - intros x y z fs gs.
    induction fs as [ w fs ].
    induction fs as [ f fs ].
    induction f as [ f | f ].
    + exact (w ,, inl f ,, IHn w y z fs gs).
    + exact (w ,, inr f ,, IHn w y z fs gs).
Defined.

Definition append_graph_zig_zag
           {g : graph}
           {x y z : vertex g}
           (fs : graph_zig_zag x y)
           (gs : graph_zig_zag y z)
  : graph_zig_zag x z
  := length_of_graph_zig_zag fs + length_of_graph_zig_zag gs
     ,,
     append_graph_zig_zag_of_length (pr2 fs) (pr2 gs).

(**
 5. Reversing zig-zags
 *)
Definition post_cons_left_graph_zig_zag_of_length
           {g : graph}
           {n : ℕ}
           {x y z : vertex g}
           (gs : graph_zig_zag_of_length n x y)
           (f : edge y z)
  : graph_zig_zag_of_length (S n) x z.
Proof.
  revert x y z gs f.
  induction n as [ | n IHn ].
  - intros x y z gs f.
    exists z.
    split.
    * rewrite <- gs in f.
      exact (inl f).
    * reflexivity.
  - intros x y z gs f.
    induction gs as [ w gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (w ,, inl g' ,, IHn _ _ _ gs f).
    + exact (w ,, inr g' ,, IHn _ _ _ gs f).
Defined.

Definition post_cons_right_graph_zig_zag_of_length
           {g : graph}
           {n : ℕ}
           {x y z : vertex g}
           (gs : graph_zig_zag_of_length n x y)
           (f : edge z y)
  : graph_zig_zag_of_length (S n) x z.
Proof.
  revert x y z gs f.
  induction n as [ | n IHn ].
  - intros x y z gs f.
    exists z.
    split.
    * rewrite <- gs in f.
      exact (inr f).
    * reflexivity.
  - intros x y z gs f.
    induction gs as [ w gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (w ,, inl g' ,, IHn _ _ _ gs f).
    + exact (w ,, inr g' ,, IHn _ _ _ gs f).
Defined.

Definition reverse_graph_zig_zag_of_length
           {g : graph}
           {n : ℕ}
           {x y : vertex g}
           (gs : graph_zig_zag_of_length n x y)
  : graph_zig_zag_of_length n y x.
Proof.
  revert x y gs.
  induction n as [ | n IHn ].
  - intros x y gs.
    exact (pathsinv0 gs).
  - intros x y gs.
    induction gs as [ z gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (post_cons_right_graph_zig_zag_of_length (IHn _ _ gs) g').
    + exact (post_cons_left_graph_zig_zag_of_length (IHn _ _ gs) g').
Defined.

Definition reverse_graph_zig_zag
           {g : graph}
           {x y : vertex g}
           (gs : graph_zig_zag x y)
  : graph_zig_zag y x
  := length_of_graph_zig_zag gs ,, reverse_graph_zig_zag_of_length (pr2 gs).

(* this assumes the induction hypothesis for all 
   edges, not just those in the path *)
Lemma graph_zig_zag_strong_induction_helper 
    {g : graph}
    {P : vertex g -> UU} :
  ∏ n, ∏ (x y : vertex g), 
      (P x) -> 
      (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) -> 
      graph_zig_zag_of_length n x y -> 
      P y.
Proof.
  intro n.
  induction n as [|n Hn].
  - intros x y Hx _ gs.
    now rewrite <- gs.
  - intros x y Hx eind gs.
    destruct gs as [z [xz gs]].
    use (Hn _ _ _ eind gs).
    exact (eind x z Hx xz).
Defined.

Lemma graph_zig_zag_strong_induction 
    {g : graph}
    {x y : vertex g}
    (gs : graph_zig_zag x y) :
  ∏ (P : vertex g -> UU),
    (P x) ->
    (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) ->
  P y.
Proof.
  intros P Hx Hind.
  destruct gs as [n gs].
  use graph_zig_zag_strong_induction_helper.
  - exact n.
  - exact x.
  - exact Hx.
  - exact Hind.
  - exact gs.
Defined.

Definition is_connected (g : graph) : UU :=
    ∏ (v1 v2 : vertex g), graph_zig_zag v1 v2.

Lemma connected_graph_zig_zag_strong_induction 
    {g : graph}
    (x : vertex g)
    {y : vertex g}
    (H : is_connected g) :
  ∏ (P : vertex g -> UU),
    (P x) ->
    (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) ->
  P y.
Proof.
  apply graph_zig_zag_strong_induction.
  apply H.
Defined.

Lemma is_connected_pointed (g : graph) (v0 : vertex g) :
    (∏ (v : vertex g), graph_zig_zag v0 v) ->
        is_connected g.
Proof.
  intro H.
  intros v1 v2.
  use (append_graph_zig_zag (y := v0)).
  - exact (reverse_graph_zig_zag (H v1)).
  - exact (H v2).
Defined.