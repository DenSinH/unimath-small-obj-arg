Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.Opp.

Require Import CategoryTheory.ModelCategories.Retract.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope retract.
(* Local Open Scope set. *)

(* in a category, we know that homs are sets, so equality must be a prop *)
(* Lean: lp @ https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L14 *)
(* Normal ∑-type is not a proposition, we need it to be to use it to create morphism classes *)
Definition filler {M : category} {a x e b : M} {i : a --> x} {p : e --> b}
    {g : a --> e} {f : x --> b} (H : p ∘ g = f ∘ i) := 
  ∑ l : x --> e, (l ∘ i = g) × (p ∘ l = f).

Definition filler_map {M : category} {a x e b : M} {i : a --> x} {p : e --> b}
    {g : a --> e} {f : x --> b} {H : p ∘ g = f ∘ i} (l : filler H) := pr1 l.
Definition filler_comm {M : category} {a x e b : M} {i : a --> x} {p : e --> b}
    {g : a --> e} {f : x --> b} {H : p ∘ g = f ∘ i} (l : filler H) := pr2 l.

Definition lp {M : category} {a x e b : M} (i : a --> x) (p : e --> b) : hProp := 
  ∀ (g : a --> e) (f : x --> b) (H : p ∘ g = f ∘ i), ∥filler H∥.

(* "existential" lifting property *)
Definition elp {M : category} {a x e b : M} (i : a --> x) (p : e --> b) : UU := 
  ∏ (g : a --> e) (f : x --> b) (H : p ∘ g = f ∘ i), filler H.

Lemma hinh_elp_impl_lp {M : category} {a x e b : M} (i : a --> x) (p : e --> b) :
    ∥elp i p∥ -> lp i p.
Proof.
  intros elp_ip h k Hhk.
  use (elp_ip); clear elp_ip; intro elp_ip.
  apply hinhpr.
  exact (elp_ip h k Hhk).
Qed.

(* Lean: llp @ https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L18 *)
(* 
       g
    A ---> E
    |     /|
  i |  λ/  | p
    v /    v
    X ---> B
       f 
*)
Definition llp {M : category} (R : morphism_class M) : (morphism_class M) :=
    λ {a x : M} (i : a --> x), ∀ (e b : M) (p : e --> b), ((R _ _) p ⇒ lp i p)%logic.

Definition rlp {M : category} (L : morphism_class M) : (morphism_class M) :=
    λ {e b : M} (p : e --> b), ∀ (a x : M) (i : a --> x), ((L _ _) i ⇒ lp i p)%logic.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L24 *)
(* MCAT: Lemma 14.1.9 *)
Lemma llp_anti {M : category} {R R' : morphism_class M} (h : R ⊆ R') : llp R' ⊆ llp R.
Proof.
  unfold "⊆" in *.
  intros a x i H.
  intros e b p K.
  (* LLP for i in R' *)
  apply (H e b p).
  (* R ⊆ R' *)
  apply (h e b p).
  (* i in R *)
  exact K.
Defined.

(* not in Lean file *)
Lemma opp_rlp_is_llp_opp {M : category} (L : morphism_class M) : 
    morphism_class_opp (rlp L) = (llp (morphism_class_opp L)).
Proof.
  apply morphism_class_subset_antisymm; intros a b f.
  (* todo: these proofs are the same *)
  - intro rlpf.
    intros x y g hg.
    intros top bottom H.
    (* extract lift fro rlp of f with respect to the opposite morphism of g *)
    use (rlpf _ _ (rm_opp_mor g)).
    * exact hg.
    (* flip diagram *)
    * exact (rm_opp_mor bottom).
    * exact (rm_opp_mor top).
    (* commutativity *)
    * symmetry.
      exact H.
    * (* extract lift *)
      intros hl.
      destruct hl as [l [hlg hlf]].
      apply hinhpr.

      (* the opposite morphism of the lift is the lift of the opposite diagram *)
      exists (opp_mor l).
      split; assumption.
  - intro rlpf.
    intros x y g hg.
    intros top bottom H.
    use (rlpf _ _ (rm_opp_mor g)).
    * exact hg.
    * exact (rm_opp_mor bottom).
    * exact (rm_opp_mor top).
    * symmetry.
      exact H.
    * intro hl.
      destruct hl as [l [hlg hlf]].
      apply hinhpr.

      exists (opp_mor l).
      split; assumption.
Defined.

(* dual statement *)
Lemma opp_llp_is_rlp_opp {M : category} (L : morphism_class M) : 
    morphism_class_opp (llp L) = rlp (morphism_class_opp L).
Proof.
  rewrite <- (morphism_class_opp_opp (rlp _)).
  rewrite (opp_rlp_is_llp_opp _).
  trivial.
Defined.

Lemma elp_of_retracts {M : category} {a b x y a' b' x' y' : M} 
    {f : a --> b} {f' : a' --> b'}
    {g : x --> y} {g' : x' --> y'}
    (rf : retract f' f) (rg : retract g' g) :
  (elp f' g') -> (elp f g).
Proof.
  intros Hlp h k Hcomm.
  destruct rf as [ia [ra [ib [rb [ha [hb [hif hrf]]]]]]].
  destruct rg as [ix [rx [iy [ry [hx [hy [hig hrg]]]]]]].

  destruct (Hlp (ra · h · ix) (rb · k · iy)) as [l [H1 H2]].
  {
    rewrite <- assoc, hig, assoc, <- (assoc _ h g), Hcomm, assoc, hrf, assoc, assoc.
    reflexivity.
  }

  exists (ib · l · rx).
  split.
  * rewrite assoc, assoc, <- hif, <- (assoc _ f' l), H1, assoc, assoc.
    now rewrite ha, id_left, <- assoc, hx, id_right.
  * rewrite <- assoc, hrg, assoc, <- (assoc _ l g'), H2, assoc, assoc.
    now rewrite hb, id_left, <- assoc, hy, id_right.
Defined.

(* todo: use elp_of_retracts for this?  *)
Lemma lp_of_retracts {M : category} {a b x y a' b' x' y' : M} 
    {f : a --> b} {f' : a' --> b'}
    {g : x --> y} {g' : x' --> y'}
    (rf : retract f' f) (rg : retract g' g) :
  (lp f' g') -> (lp f g).
Proof.
  intros Hlp h k Hcomm.
  destruct rf as [ia [ra [ib [rb [ha [hb [hif hrf]]]]]]].
  destruct rg as [ix [rx [iy [ry [hx [hy [hig hrg]]]]]]].

  use Hlp.
  - exact (ra · h · ix).
  - exact (rb · k · iy).
  - rewrite <- assoc, hig, assoc, <- (assoc _ h g), Hcomm, assoc, hrf, assoc, assoc.
    reflexivity.
  - intro Hl.
    destruct Hl as [l [H1 H2]].
    
    apply hinhpr.
    exists (ib · l · rx).
    split.
    * rewrite assoc, assoc, <- hif, <- (assoc _ f' l), H1, assoc, assoc.
      now rewrite ha, id_left, <- assoc, hx, id_right.
    * rewrite <- assoc, hrg, assoc, <- (assoc _ l g'), H2, assoc, assoc.
      now rewrite hb, id_left, <- assoc, hy, id_right.
Defined.