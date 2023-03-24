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

(* Any map can be factored through maps in L and R *)
Definition wfs_fact_ax {M : category} (L R : morphism_class M) := 
    (∀ x y (f : x --> y), ∃ z (g : x --> z) (h : z --> y), (L _ _) g × (R _ _) h × h ∘ g = f).

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L27 *)
Definition is_wfs {M : category} (L R : morphism_class M) :=
  (L = llp R) × (R = rlp L) × (wfs_fact_ax L R).

Definition make_is_wfs {M : category} {L R : morphism_class M}
    (llp : L = llp R) (rlp : R = rlp L) (fact : wfs_fact_ax L R) : is_wfs L R :=
  make_dirprod llp (make_dirprod rlp fact).

Definition wfs (M : category) :=
  ∑ (L R : morphism_class M), is_wfs L R.

Definition make_wfs {M : category} (L R : morphism_class M) (w : is_wfs L R) : wfs M :=
  tpair _ L (tpair _ R w).

Definition wfs_L {M : category} (w : wfs M) := (pr1 w).
Definition wfs_R {M : category} (w : wfs M) := pr1 (pr2 w).
Definition is_wfs_llp  {M : category} {L R : morphism_class M} (w : is_wfs L R) := pr1 w.
Definition is_wfs_rlp  {M : category} {L R : morphism_class M} (w : is_wfs L R) := pr1 (pr2 w).
Definition is_wfs_fact {M : category} {L R : morphism_class M} (w : is_wfs L R) := pr2 (pr2 w).
Definition wfs_is_wfs {M : category} (w : wfs M) := pr2 (pr2 w).
Definition wfs_llp  {M : category} (w : wfs M) := is_wfs_llp (wfs_is_wfs w).
Definition wfs_rlp  {M : category} (w : wfs M) := is_wfs_rlp (wfs_is_wfs w).
Definition wfs_fact {M : category} (w : wfs M) := is_wfs_fact (wfs_is_wfs w).

(* todo: in lean this is also a Prop? *)
Lemma isaprop_is_wfs {M : category} (L R : morphism_class M) : isaprop (is_wfs L R).
Proof.
  apply isapropdirprod.
  - admit.
  - apply isapropdirprod.
    * admit.
    * do 3 (apply impred_isaprop; intro).
      apply propproperty.
Admitted.

(* Can't do dot notation like in lean (is_wfs.lp)*)
(* any two maps in a wfs have the lifting property with respect to each other *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L33 *)
Lemma wfs'lp {M : category} (w : wfs M)
  {a b x y} {f : a --> b} {g : x --> y} (hf : (wfs_L w _ _) f) (hg : (wfs_R w _ _) g) : lp_hProp f g.
Proof.
  unfold wfs_L in hf.
  rewrite (wfs_llp w) in hf.
  exact (hf _ _ _ hg). 
Defined.

(* if f' is a retract of f and f is in L for some WFS, then so is f' *)
(* proposition 14.1.13 in More Concise AT *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L40 *)
Lemma wfs'retract {M : category} (w : wfs M)
  {a b a' b'} {f : a --> b} {f' : a' --> b'} (r : retract f f') (hf : (wfs_L w _ _) f) : (wfs_L w _ _) f'.
Proof.
  destruct r as [ia [ra [ib [rb [ha [hb [hi hr]]]]]]].

  unfold wfs_L.
  rewrite (wfs_llp w).
  intros x y g hg h k s.
  (* existence of lift in part of diagram *)
  use (wfs'lp w hf hg (h ∘ ra) (k ∘ rb) _).
  {
    rewrite <- assoc, s, assoc, assoc, hr.
    reflexivity.
  }
  (* extract lift *)
  intro hl.
  destruct hl as  [l [hlh hlk]].
  
  (* turn proof into normal ∑-type *)
  apply hinhpr.
  (* composition in diagram *)
  exists (l ∘ ib).
  (* diagram chasing *)
  split.
  * rewrite assoc, <- hi, <- assoc, hlh, assoc, ha, id_left.
    reflexivity.
  * rewrite <- assoc, hlk, assoc, hb, id_left.
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
    use test.
    * exact hg.
    * exact (rm_opp_mor bottom).
    * exact (rm_opp_mor top).
    * symmetry.
      exact H.
    * intros hl.
      destruct hl as [l [hlg hlf]].
      apply hinhpr.

      exists (opp_mor l).
      split; assumption.
  - intro rlpf.
    intros x y g hg.
    intros top bottom H.
    specialize (rlpf _ _ (rm_opp_mor g)) as test.
    simpl in test.
    use test.
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
  use make_is_wfs.
  - trivial.
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
Lemma retract_argument {M : category} {L' : morphism_class M} (w : wfs M)
  (H : ∀ {x y} (f : x --> y), ∃ z (g : x --> z) (h : z --> y), (L' _ _) g × (wfs_R w _ _) h × h ∘ g = f) :
  ∏ {a b} (f : a --> b), (wfs_L w _ _) f -> ∃ {x' y'} (f' : x' --> y') (r : retract f' f), (L' _ _) f'.
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
  use (wfs'lp w hf hh g (identity _)).
  {
    rewrite hgh, id_right.
    reflexivity.
  }
  intro hl.
  destruct hl as [l [hl1 hl2]].

  (* Show that f is a retract of g *)
  assert (r : retract g f).
  {
    use (make_retract (identity a) (identity a) l h).
    use make_is_retract.
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
  (* todo: get rid of remember here *)
  simpl in H.
  remember (make_iso _ H) as fiso.
  replace f with (morphism_from_iso fiso) in *.

  - (* lift we are looking for is h ∘ f^{-1} *)
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
    use (H (identity _) (identity _)).
    {
      (* commutativity of diagram *)
      rewrite id_left, id_right.
      reflexivity.
    }
    (* extract lift l from diagram *)
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
  use make_is_wfs; try symmetry.
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

Lemma is_wfs_gives_opp_is_wfs {M : category} {L R : morphism_class M} (w : is_wfs L R) : is_wfs (morphism_class_opp R) (morphism_class_opp L).
Proof.
  use make_is_wfs.
  - rewrite (is_wfs_rlp w).
    exact (opp_rlp_is_llp_opp _).
  - rewrite (is_wfs_llp w).
    exact (opp_llp_is_rlp_opp _).
  - intros x y f.
    specialize ((is_wfs_fact w) _ _ (rm_opp_mor f)) as test.
    simpl in test.
    use (hinhuniv _ test).
    intro H.
    destruct H as [z [g [h [? [? ?]]]]].
    
    apply hinhpr.
    exists (opp_ob z), (opp_mor h), (opp_mor g).
    split; try split; assumption.
Defined.

Lemma wfs_gives_opp_wfs {M : category} (w : wfs M) : wfs (op_cat M).
Proof.
  exists (morphism_class_opp (wfs_R w)), (morphism_class_opp (wfs_L w)).
  exact (is_wfs_gives_opp_is_wfs (wfs_is_wfs w)).
Defined.

Lemma wfs_contains_isos {M : category} (w : wfs M) : (morphism_class_isos M) ⊆ (wfs_L w).
Proof.
  (* isos are the llp of univ *)
  rewrite <- llp_univ.
  (* rewrite llp property *)
  unfold wfs_L.
  rewrite (wfs_llp w).

  apply llp_anti.
  (* every morphism is a morphism *)
  intros x y f hf.
  exact tt.
Defined.

(* https://ncatlab.org/nlab/show/weak+factorization+system#ClosuredPropertiesOfWeakFactorizationSystem *)
Lemma wfs_closed_pullbacks {M : category} (w : wfs M) 
  {x y z : M} {p : x --> y} {f : z --> y} (Pb : Pullback f p) : ((wfs_R w _ _) p) -> ((wfs_R w _ _) (PullbackPr1 Pb)).
Proof.
  intro p_r.

  destruct Pb as [[zfx [f'p p2]] [H isPb]].
  simpl in *.
  change (wfs_R w zfx z f'p).

  (* need to show that f'p has rlp w.r.t. all i ∈ L *)
  unfold wfs_R.
  rewrite (wfs_rlp w).
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
  unfold wfs_R in p_r.
  rewrite (wfs_rlp w) in p_r.

  use (p_r _ _ i i_l (p2 ∘ p1) (f ∘ g) _).
  {
    rewrite <- assoc, <- H, assoc, Hp1g, assoc.
    reflexivity. 
  }
  
  (* extract lift *)
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