Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Section retract.

Local Open Scope cat.
Variable C : category.

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

Record retract {a b a' b' : C} (f : a --> b) (f' : a' --> b') : UU := {
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

(* there is more in the lean file *)

End retract.