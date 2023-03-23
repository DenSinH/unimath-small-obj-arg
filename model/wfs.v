Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.pullbacks.

From Model Require Import morphism_class retract.


Section wfs.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope retract.
(* Local Open Scope set. *)

(* todo: rlp/llp arguments *)
(* todo: morphism class arguments *)

(* in a category, we know that homs are sets, so equality must be a prop *)
(* Lean: lp @ https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L14 *)
(* Normal ∑-type is not a proposition, we need it to be to use it to create morphism classes *)
Definition lp {M : category} {a b x y : M} (f : a --> b) (g : x --> y) : UU := 
    ∏ (h : a --> x) (k : b --> y), 
        g ∘ h = k ∘ f -> ∃ l : b --> x, (l ∘ f = h) × (g ∘ l = k).

Definition isaprop_lp {M : category} {a b x y : M} (f : a --> b) (g : x --> y) : isaprop (lp f g).
Proof.
  do 3 (apply impred_isaprop; intro).
  apply propproperty.
Defined.

Definition lp_hProp {M : category} {a b x y : M} (f : a --> b) (g : x --> y) : hProp :=
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
Definition llp {M : category} (R : morphism_class M) : (morphism_class M) :=
    λ {a x : M} (i : a --> x), ∀ (e b : M) (p : e --> b), ((R _ _) p ⇒ lp_hProp i p)%logic.

Definition rlp {M : category} (L : morphism_class M) : (morphism_class M) :=
    λ {e b : M} (p : e --> b), ∀ (a x : M) (i : a --> x), ((L _ _) i ⇒ lp_hProp i p)%logic.

(* There is stuff in 
  https://unimath.github.io/doc/UniMath/4dd5c17/UniMath.MoreFoundations.Subtypes.html
to do this, but I don't know if we want to use this or not...
I figured I'd define my own, it should be mostly compatible
*)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L24 *)
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

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L27 *)
Record is_wfs {M : category} (L R : morphism_class M) := {
  wfs_llp  : L = llp R;
  wfs_rlp  : R = rlp L;
  (* Any map can be factored through maps in L and R *)
  wfs_fact : ∀ x y (f : x --> y), ∃ z (g : x --> z) (h : z --> y),
             (L _ _) g × (R _ _) h × h ∘ g = f
}.

Arguments wfs_llp {_ _ _}.
Arguments wfs_rlp {_ _ _}.
Arguments wfs_fact {_ _ _}.

(* todo: in lean this is also a Prop? *)
Lemma isaprop_is_wfs {M : category} (L R : morphism_class M) : isaprop (is_wfs L R).
Proof.
  admit.
Admitted.

(* Can't do dot notation like in lean (is_wfs.lp)*)
(* any two maps in a wfs have the lifting property with respect to each other *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L33 *)
Lemma is_wfs'lp {M : category} {L R : morphism_class M} (w : is_wfs L R)
  {a b x y} {f : a --> b} {g : x --> y} (hf : (L _ _) f) (hg : (R _ _) g) : lp_hProp f g.
Proof.
  rewrite w.(wfs_llp) in hf.
  exact (hf _ _ _ hg). 
Defined.

(* if f' is a retract of f and f is in L for some WFS, then so is f' *)
(* proposition 14.1.13 in More Concise AT *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L40 *)
Lemma is_wfs'retract {M : category} {L R : morphism_class M} (w : is_wfs L R)
  {a b a' b'} {f : a --> b} {f' : a' --> b'} (r : retract f f') (hf : (L _ _) f) : (L _ _) f'.
Proof.
  rewrite w.(wfs_llp).
  intros x y g hg h k s.
  (* existence of lift in part of diagram *)
  specialize (is_wfs'lp w hf hg (h ∘ r.(ra)) (k ∘ r.(rb))) as ehl.

  unshelve epose proof (ehl _) as ehl.
  {
    rewrite <- assoc, s, assoc, assoc, (r.(hr)).
    reflexivity.
  }
  
  (* extract lift and turn proof into normal ∑-type *)
  use (hinhuniv _ ehl).
  intro hl.
  destruct hl as [l [hlh hlk]].
  apply hinhpr.
  (* composition in diagram *)
  exists (l ∘ r.(ib)).
  (* diagram chasing *)
  split.
  * rewrite assoc, <- (r.(hi)), <- assoc, hlh, assoc, r.(ha), id_left.
    reflexivity.
  * rewrite <- assoc, hlk, assoc, r.(hb), id_left.
    reflexivity.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L52 *)
(* Lemma 14.1.9 in MCAT *)
Lemma llp_rlp_self {M : category} (L : morphism_class M) : L ⊆ llp (rlp L).
Proof.
  intros a b f hf x y g hg.
  apply (hg _ _ _).
  exact hf.
Defined.

(* no counterpart in lean *)
Lemma rlp_llp_self {M : category} (L : morphism_class M) : L ⊆ rlp (llp L).
Proof.
  intros a b f hf x y g hg.
  apply (hg _ _ _).
  exact hf.
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
    specialize (rlpf _ _ (rm_opp_mor g)) as test.
    simpl in test.
    unshelve epose proof (test _) as test.
    {
      exact hg.
    }

    specialize (test (rm_opp_mor bottom) (rm_opp_mor top)) as t.
    unshelve epose proof (t _) as t.
    {
      symmetry.
      exact H.
    }

    use (hinhuniv _ t).
    intro hl.
    destruct hl as [l [hlg hlf]].
    apply hinhpr.

    exists (opp_mor l).
    split; assumption.
  - intro rlpf.
    intros x y g hg.
    intros top bottom H.
    specialize (rlpf _ _ (rm_opp_mor g)) as test.
    simpl in test.
    unshelve epose proof (test _) as test.
    {
      exact hg.
    }

    specialize (test (rm_opp_mor bottom) (rm_opp_mor top)) as t.
    unshelve epose proof (t _) as t.
    {
      symmetry.
      exact H.
    }

    use (hinhuniv _ t).
    intro hl.
    destruct hl as [l [hlg hlf]].
    apply hinhpr.

    exists (opp_mor l).
    split; assumption.
Defined.

Lemma opp_llp_is_rlp_opp {M : category} (L : morphism_class M) : 
    morphism_class_opp (llp L) = rlp (morphism_class_opp L).
Proof.
  rewrite <- (morphism_class_opp_opp (rlp _)).
  rewrite (opp_rlp_is_llp_opp _).
  trivial.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L55 *)
(* No counterpart in MCAT, (□(I□), I□) is a WFS *)
Lemma wfs_of_factorization {M : category} (I : morphism_class M) 
  (h : ∀ {x y} (f : x --> y), ∃ z (g : x --> z) (h : z --> y), (llp (rlp I) _ _ g) × (rlp I _ _ h) × (h ∘ g = f)) :
  is_wfs (llp (rlp I)) (rlp I).
Proof.
  constructor.
  - reflexivity.
  - apply morphism_class_subset_antisymm; intros x y g hg.
    * exact (rlp_llp_self _ _ _ _ hg).
    * intros a b f hf.
      apply (hg _ _ _).
      exact (llp_rlp_self _ _ _ _ hf).
  - exact h.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L67 *)
(* same name as Lemma 14.1.12 in MCAT, but a different phrasing 
In MCAT, the statement is in reference of a single morphism, not a whole class
*)
Lemma retract_argument {M : category} {L R L' : morphism_class M} (w : is_wfs L R)
  (H : ∀ {x y} (f : x --> y), ∃ z (g : x --> z) (h : z --> y), (L' _ _) g × (R _ _) h × h ∘ g = f) :
  ∏ {a b} (f : a --> b), (L _ _) f -> ∃ {x' y'} (f' : x' --> y') (r : retract f' f), (L' _ _) f'.
Proof.
  intros a b f hf.

  (* rcases H f with ⟨z, g, h, hg, hh, hgh⟩, *)
  (* Get factorization for f from H *)
  specialize (H _ _ f) as eHf.
  simpl in eHf.
  use (hinhuniv _ eHf).
  intro Hf.
  destruct Hf as [z [g [h [hg [hh hgh]]]]].

  (* rcases w.lp hf hh g (𝟙 _) (by rw hgh; simp) with ⟨l, hl₁, hl₂⟩, *)
  (* Use lifting property to get map l in diagram *)
  specialize (is_wfs'lp w hf hh g (identity _)) as ehl.
  unshelve epose proof (ehl _) as ehl.
  {
    rewrite hgh, id_right.
    reflexivity.
  }
  use (hinhuniv _ ehl).
  intro hl.
  destruct hl as [l [hl1 hl2]].

  (* Show that f is a retract of g *)
  assert (r : retract g f).
  {
    split with (identity a) (identity a) l h.
    - now rewrite id_left.
    - assumption.
    - rewrite id_left. now symmetry.
    - rewrite id_left. now symmetry.
  }

  (* convert goal to normal ∑-type *)
  apply hinhpr.
  
  (* finish proof *)
  exists a, z, g, r.
  exact hg.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L82 *)
Lemma lp_isos_univ {M : category} {a b x y} (f : a --> b) (g : x --> y) : 
  (morphism_class_isos M _ _) f -> lp f g.
Proof.
  intro H.
  intros h k s.

  (* Turn f into the corresponding coerced isomorphism type *)
  simpl in H.
  remember (make_iso _ H) as fiso.
  replace f with (morphism_from_iso fiso) in *.
  - (* todo: this in hexists tactic? *)
    (* lift we are looking for is h ∘ f^{-1} *)
    apply hinhpr.
    exists (h ∘ (inv_from_iso fiso)).
    (* diagram chasing *)
    split.
    * rewrite assoc, iso_inv_after_iso, id_left.
      reflexivity.
    * rewrite <- assoc, s, assoc.
      rewrite iso_after_iso_inv, id_left.
      reflexivity.
  - (* todo: by clause in replace? *)
    (* prove that f is indeed fiso *)
    rewrite Heqfiso.
    trivial.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L91 *)
Lemma llp_univ {M : category} : llp (morphism_class_univ M) = morphism_class_isos M.
Proof.
  apply morphism_class_subset_antisymm; intros a b f H.
  - (* apply llp of f with itself *)
    specialize ((H _ _ f) tt).
    (* choose horizontal maps to be identity *)
    specialize (H (identity _) (identity _)).
    (* commutativity of diagram *)
    unshelve epose proof (H _) as H.
    {
      rewrite id_left, id_right.
      reflexivity.
    }
    (* todo: turn this use / destruct into an Ltac *)
    (* extract lift l from diagram *)
    use (hinhuniv _ H).
    intro hl.
    destruct hl as [l [hfl hlf]].
    unfold morphism_class_isos.
    
    (* show f is a z_iso (we have its inverse, the lift l) *)
    assert (is_z_isomorphism f) as f_z_iso.
    {
      exists l.
      split; assumption.
    }
    (* finish proof *)
    apply is_iso_from_is_z_iso.
    exact f_z_iso.
  - intros x y g _.
    (* other inclusion is exactly the previous Lemma *)
    exact (lp_isos_univ f g H).
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L101 *)
Lemma rlp_isos {M : category} : rlp (morphism_class_isos M) = morphism_class_univ M.
Proof.
  (* This proof is slightly different *)
  apply morphism_class_subset_antisymm.
  - (* an iso is a morphism *)
    intros x y g H.
    unfold morphism_class_univ.
    exact tt.
  - (* other inclusion is easy with previous Lemmas *)
    rewrite <- llp_univ.
    exact (rlp_llp_self _).
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L109 *)
Lemma wfs_isos_univ {M : category} : is_wfs (morphism_class_isos M) (morphism_class_univ M).
Proof.
  (* apply symmetry to immediately exact the previous Lemmas *)
  constructor; try symmetry.
  - exact llp_univ.
  - exact rlp_isos.
  - (* factorize a morphism through identity and itself *)
    intros x y f.
    apply hinhpr.
    exists x, (identity x), f.

    (* this solves the second subgoal, stating that f is a morphism *)
    split; repeat try split.
    * exact (identity_is_iso M x).
    * rewrite id_left.
      reflexivity.
Defined.

Lemma wfs_gives_opp_wfs {M : category} {L R : morphism_class M} (w : is_wfs L R) : is_wfs (morphism_class_opp R) (morphism_class_opp L).
Proof.
  split.
  - rewrite (w.(wfs_rlp)).
    exact (opp_rlp_is_llp_opp _).
  - rewrite (w.(wfs_llp)).
    exact (opp_llp_is_rlp_opp _).
  - intros x y f.
    specialize (w.(wfs_fact) _ _ (rm_opp_mor f)) as test.
    simpl in test.
    use (hinhuniv _ test).
    intro H.
    destruct H as [z [g [h [? [? ?]]]]].

    apply hinhpr.
    exists (opp_ob z), (opp_mor h), (opp_mor g).
    split; try split; assumption.
Defined.

Lemma wfs_contains_isos {M : category} {L R : morphism_class M} (w : is_wfs L R) : (morphism_class_isos M) ⊆ L.
Proof.
  (* isos are the llp of univ *)
  rewrite <- llp_univ.
  (* rewrite llp property *)
  rewrite (w.(wfs_llp)).

  apply llp_anti.
  (* every morphism is a morphism *)
  intros x y f hf.
  exact tt.
Defined.

(* https://ncatlab.org/nlab/show/weak+factorization+system#ClosuredPropertiesOfWeakFactorizationSystem *)
Lemma wfs_closed_pullbacks {M : category} {L R : morphism_class M} (w : is_wfs L R) 
  {x y z : M} {p : x --> y} {f : z --> y} (Pb : Pullback f p) : ((R _ _) p) -> ((R _ _) (PullbackPr1 Pb)).
Proof.
  intro p_r.

  destruct Pb as [[zfx [f'p p2]] [H isPb]].
  simpl in *.
  change (R zfx z f'p).

  (* need to show that f'p has rlp w.r.t. all i ∈ L *)
  rewrite (w.(wfs_rlp)).
  intros a b i i_l.

  (* commutative diagram *)
  intros p1 g Hp1g.

  (* obtain diagram
      p1     p2
    a --> Pb --> x
   i|     |f'p   |p
    v     v      v
    b --> z  --> y
       g      f
  *)

  (* use rlp of p to get lift  in outer diagram*)
  rewrite (w.(wfs_rlp)) in p_r.
  unshelve epose proof (p_r _ _ i i_l (p2 ∘ p1) (f ∘ g) _) as iplift.
  {
    rewrite <- assoc, <- H, assoc, Hp1g, assoc.
    reflexivity. 
  }
  
  (* extract lift *)
  use (hinhuniv _ iplift).
  intro hl.
  destruct hl as [l [hl1 hl2]].
  symmetry in hl2.
  
  (* use pullback property to get lift gh in
          Pb --> x
    gh  /  |f'p  |p
      /    v     v
     b --> z --> y
        g     f
  *)
  destruct (isPb _ g l hl2) as [[gh [hgh1 hgh2]] _].
  
  (* gh is the lift in the inner diagram *)
  apply hinhpr.
  exists gh.
  split.
  - (* use uniqueness of maps into pullback to show commutativity
       in top triangle *)
    apply (MorphismsIntoPullbackEqual (isPb)).
    * rewrite <-assoc, hgh1, Hp1g.
      reflexivity.
    * rewrite <- assoc, hgh2, hl1.
      reflexivity.
  - (* commutativity in lower triangle is trivial by pullback property *)
    exact hgh1.
Defined.


End wfs.