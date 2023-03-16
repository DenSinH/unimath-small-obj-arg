
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

From Model Require Import morphism_class retract.


Section wfs.

Local Open Scope cat.
Local Open Scope subtype.
(* Local Open Scope set. *)

Variables M : category.

Notation "S ⊆ T" := (morphism_class_containedIn M S T) (at level 70).

(* in a category, we know that homs are sets, so equality must be a prop *)
(* Lean: lp @ https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L14 *)
(* Normal ∑-type is not a proposition, we need it to be to use it to create morphism classes *)
Definition lp {a b x y : M} (f : a --> b) (g : x --> y) : UU := 
    ∏ (h : a --> x) (k : b --> y), 
        g ∘ h = k ∘ f -> ∃ l : b --> x, (l ∘ f = h) × (g ∘ l = k).

Definition isaprop_lp {a b x y : M} (f : a --> b) (g : x --> y) : isaprop (lp f g).
Proof.
  apply impred_isaprop.
  intro.
  apply impred_isaprop.
  intro.
  apply impred_isaprop.
  intro.
  apply propproperty.
Defined.

Definition lp_hProp {a b x y : M} (f : a --> b) (g : x --> y) : hProp :=
    make_hProp (lp f g) (isaprop_lp f g).

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
(* Messing with hProps gets a bit annoying at times *)
Definition llp (R : morphism_class M) : (morphism_class M) :=
    λ (a x : M) (i : a --> x), ∀ (e b : M) (p : e --> b), ((R _ _) p ⇒ lp_hProp i p)%logic.

Definition rlp (L : morphism_class M) : (morphism_class M) :=
    λ (e b : M) (p : e --> b), ∀ (a x : M) (i : a --> x), ((L _ _) i ⇒ lp_hProp i p)%logic.

  
(* There is stuff in 
  https://unimath.github.io/doc/UniMath/4dd5c17/UniMath.MoreFoundations.Subtypes.html
to do this, but I don't know if we want to use this or not...
I figured I'd define my own, it should be mostly compatible
*)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L24 *)
Lemma llp_anti {R R' : morphism_class M} (h : R ⊆ R') : llp R' ⊆ llp R.
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

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L27 *)
(* todo: in lean this is also a Prop? *)
Record is_wfs (L R : morphism_class M) (* : Prop *) := {
  wfs_llp  : L = llp R;
  wfs_rlp  : R = rlp L;
  (* Any map can be factored through maps in L and R *)
  wfs_fact : ∀ x y (f : x --> y), ∃ z (g : x --> z) (h : z --> y),
             (L _ _) g × (R _ _) h × h ∘ g = f
}.

Arguments wfs_llp {_ _}.
Arguments wfs_rlp {_ _}.
Arguments wfs_fact {_ _}.

(* Can't do dot notation like in lean (is_wfs.lp)*)
(* any two maps in a wfs have the lifting property with respect to each other *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L33 *)
Lemma is_wfs'lp {L R : morphism_class M} (w : is_wfs L R)
  {a b x y} {f : a --> b} {g : x --> y} (hf : (L _ _) f) (hg : (R _ _) g) : lp_hProp f g.
Proof.
  rewrite w.(wfs_llp) in hf.
  exact (hf _ _ _ hg). 
Defined.

(* if f' is a retract of f and f is in L for some WFS, then so is f'  *)
(* proposition 14.1.13 in More Concise AT *)
Lemma is_wfs'retract {L R : morphism_class M} (w : is_wfs L R)
  {a b a' b'} {f : a --> b} {f' : a' --> b'} (r : retract M f f') (hf : (L _ _) f) : (L _ _) f'.
Proof.
  rewrite w.(wfs_llp).
  intros x y g hg h k s.
  specialize (is_wfs'lp w hf hg (h ∘ r.(ra _ _ _)) (k ∘ r.(rb _ _ _))) as test.
  rewrite <- assoc in test.
  rewrite s in test.
  rewrite assoc in test.
  rewrite assoc in test.
  rewrite (r.(hr _ _ _)) in test.
  (* At this point, we want to get the conclusion of test
  destruct it to get an l 
  and precompose it with the right function from the retract
  to obtain the function we are looking for *)
  admit.
Admitted.

End wfs.