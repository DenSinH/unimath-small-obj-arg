Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Section retract.

Local Open Scope cat.

(* structure retract {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') : Type v :=
(ia : a' ⟶ a) (ra : a ⟶ a')
(ib : b' ⟶ b) (rb : b ⟶ b')
(ha : ia ≫ ra = 𝟙 a')
(hb : ib ≫ rb = 𝟙 b')
(hi : ia ≫ f = f' ≫ ib)
(hr : ra ≫ f' = f ≫ rb) *)
(*
        f
    a ----> b
  ^ ^       ^ ^
 ia | ra rb | ib
    v v   v v
    a'----> b'
        f'
*)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L15 *)
Record retract {C : category} {a b a' b' : C} (f : a --> b) (f' : a' --> b') : UU := {
    ia : a' --> a;
    ra : a  --> a';
    ib : b' --> b;
    rb : b  --> b';
    ha : ra ∘ ia = identity a';
    hb : rb ∘ ib = identity b';
    hi : f  ∘ ia = ib ∘ f';
    hr : f' ∘ ra = rb ∘ f
}.

Arguments ia {_ _ _ _ _ _ _}.
Arguments ra {_ _ _ _ _ _ _}.
Arguments ib {_ _ _ _ _ _ _}.
Arguments rb {_ _ _ _ _ _ _}.
Arguments ha {_ _ _ _ _ _ _}.
Arguments hb {_ _ _ _ _ _ _}.
Arguments hi {_ _ _ _ _ _ _}.
Arguments hr {_ _ _ _ _ _ _}.

Variable C : category.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L23 *)
(* Lemma 14.1.2 in MCAT *)
Lemma retract_is_iso {a b a' b' : C} {f : a --> b} {f' : a' --> b'} (r : retract f f')
  (h : is_iso f) : is_iso f'.
Proof.
  (* we construct an explicit inverse from the retract diagram *)  
  apply is_iso_from_is_z_iso.
  remember (make_iso _ h) as fiso.
  replace f with (morphism_from_iso fiso) in *.

  (* inverse is ra ∘ f^{-1} ∘ ib *)
  exists (r.(ra) ∘ (inv_from_iso fiso) ∘ r.(ib)).
  split.
  (* diagram chasing *)
  - rewrite assoc, <- r.(hi), assoc.
    rewrite <- (assoc (r.(ia)) _ _).
    rewrite iso_inv_after_iso, id_right.
    exact (r.(ha)).
  - rewrite <- assoc, <- assoc, r.(hr), assoc, assoc.
    rewrite <- (assoc (r.(ib)) _ _).
    rewrite iso_after_iso_inv, id_right.
    exact (r.(hb)).
  - (* f is indeed fiso *)
    rewrite Heqfiso.
    trivial.
Defined.

Variable D : category.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/retract.lean#L36 *)
Lemma functor_on_retract (F : functor C D) {a b a' b' : C} {f : a --> b} {f' : a' --> b'} (r : retract f f') :
  retract (#F f) (#F f').
Proof.
  split with (#F r.(ia)) (#F r.(ra)) (#F r.(ib)) (#F r.(rb)); 
      repeat rewrite <- functor_comp; try rewrite <- functor_id.
  - now rewrite (r.(ha)).
  - now rewrite (r.(hb)).
  - now rewrite (r.(hi)).
  - now rewrite (r.(hr)).
Defined.

End retract.