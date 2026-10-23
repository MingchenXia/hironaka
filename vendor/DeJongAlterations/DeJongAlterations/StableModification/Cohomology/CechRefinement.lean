/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechAcyclic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Data.Sum.Order

/-!
# Independence of the cover for Čech cohomology of quasi-coherent modules

Let `F` be a quasi-coherent module on a scheme `X` and `W : κ → X.Opens` a finite family all of
whose nonempty finite intersections are affine. If `e : ι ↪o κ` is an order embedding such that the
subfamily `W ∘ e` still covers `X`, the restriction `Č(W, F) ⟶ Č(W ∘ e, F)` is a
quasi-isomorphism (`isIso_homologyMap_cechRestrict`). Consequently two finite covers `U`, `V` with
affine intersections (for instance finite affine covers of a separated scheme) have canonically
isomorphic Čech cohomology, through the cover `U ⊔ V` indexed by `ι ⊕ₗ κ`
(`cechCohomologyIsoOfCovers`, `cechCohomologyIsoOfAffineCovers`). Blueprint:
`sm-cohomology-cech.tex`, `prop:sm-cech-refine`, `thm:sm-cech-independence`
(`lem:sm-cech-basic`, independence of the cover).

## The argument

This replaces the usual double complex (Hartshorne III.4.5 compares with derived functors; Stacks
01FM uses refinement homotopies) by adding one open at a time. If `κ = ι ⊔ {a}`, restriction to
`ι` is degreewise surjective with kernel the cochains supported on subsets containing `a`
(`kerComplex`). Sending such a cochain `x` to `S ↦ ε(S) x_{S ∪ {a}}`, with the sign
`ε(S) = (-1)^{#{i ∈ S | a < i}}`, identifies the kernel with the augmented Čech complex of the
cover `(W_a ∩ W_i)_{i ∈ ι}` of the affine `W_a` (`twistCube`), which is exact by
`linkDiagram_exact`. The long exact sequence then shows that the restriction is a
quasi-isomorphism (`isIso_homologyMap_cechRestrict_of_oneVertex`); induction on `#κ - #ι`
handles general embeddings.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section HomologyLES

variable {C : Type*} [Category C] [Abelian C]

/-- In a short exact sequence of `ℕ`-indexed cochain complexes whose first term is acyclic, the
second map is a quasi-isomorphism. -/
theorem isIso_homologyMap_g_of_acyclic {S : ShortComplex (CochainComplex C ℕ)}
    (hS : S.ShortExact) (h : ∀ p, Limits.IsZero (S.X₁.homology p)) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap S.g p) := by
  have hmono : Mono (HomologicalComplex.homologyMap S.g p) :=
    (hS.homology_exact₂ p).mono_g ((h p).eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap S.g p) :=
    (hS.homology_exact₃ p (p + 1) (by simp)).epi_f ((h (p + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end HomologyLES

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

section Kernel

variable (F : X.Modules) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] (W : κ → X.Opens)
  (j : ι ↪o κ) (a : κ) (c : R →+* Γ(X, ⊤))

/-- The cochains of cardinality `n` supported on subsets containing `a`. -/
def kerPiece (n : ℕ) : Submodule R (subsetCechCardPiece (cechDiagram F W c) n) where
  carrier := {x | ∀ T, a ∉ T → x.val T = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy T hT := by
    change x.val T + y.val T = 0
    rw [hx T hT, hy T hT, add_zero]
  smul_mem' r x hx T hT := by
    change r • x.val T = 0
    rw [hx T hT, smul_zero]

lemma kerPiece_differential (n : ℕ) (x : subsetCechCardPiece (cechDiagram F W c) n)
    (hx : x ∈ kerPiece F W a c n) :
    subsetCechCardDifferential (cechDiagram F W c) n x ∈ kerPiece F W a c (n + 1) := by
  intro T hT
  change subsetCechDifferential _ x.val T = 0
  rw [subsetCechDifferential_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [hx (T.erase i) (fun h => hT (Finset.mem_of_mem_erase h)), map_zero, smul_zero]

/-- The kernel complex: cochains supported on subsets containing `a`. -/
def kerComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R (kerPiece F W a c (p + 1)))
    (fun p => ModuleCat.ofHom ((subsetCechCardDifferential (cechDiagram F W c) (p + 1)).restrict
      (kerPiece_differential F W a c (p + 1))))
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact subsetCechDifferential_squared _ x.val.val)

lemma kerComplex_d (p : ℕ) :
    (kerComplex F W a c).d p (p + 1) =
      ModuleCat.ofHom ((subsetCechCardDifferential (cechDiagram F W c) (p + 1)).restrict
        (kerPiece_differential F W a c (p + 1))) :=
  CochainComplex.of_d (fun p => ModuleCat.of R (kerPiece F W a c (p + 1)))
    (fun p => ModuleCat.ofHom ((subsetCechCardDifferential (cechDiagram F W c) (p + 1)).restrict
      (kerPiece_differential F W a c (p + 1)))) p

/-- The inclusion of the kernel complex. -/
def kerComplexι : kerComplex F W a c ⟶ cechComplex F W c :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (kerPiece F W a c (p + 1)).subtype) (by
    intro p
    simp only [kerComplex, cechComplex, subsetCechComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

variable {a j}

/-- The kernel complex, the Čech complex and the restriction to the subfamily form a short
complex. -/
def kerShortComplex (ha : a ∉ Set.range j) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (kerComplexι F W a c) (cechRestrict F W j c) (by
    ext p x
    apply Subtype.ext
    funext S
    change F.presheaf.map _ (x.val.val (S.map j.toEmbedding)) = 0
    rw [x.property (S.map j.toEmbedding) (by simpa using fun i _ h => ha ⟨i, h⟩)]
    exact map_zero _)

theorem kerShortComplex_shortExact (ha : a ∉ Set.range j)
    (hall : ∀ x, x ≠ a → x ∈ Set.range j) :
    (kerShortComplex F W c ha).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    intro T hT
    have hT' : T = (T.preimage j j.injective.injOn).map j.toEmbedding := by
      rw [Finset.map_eq_image]
      refine (Finset.image_preimage_of_bij _ _ ?_).symm
      refine ⟨fun _ hx => hx, j.injective.injOn, fun y hy => ?_⟩
      obtain ⟨i, hi⟩ := hall y (fun h => hT (h ▸ hy))
      refine ⟨i, ?_, hi⟩
      change j i ∈ (T : Set κ)
      rw [hi]
      exact hy
    have h0 := congrArg (fun z => z.val (T.preimage j j.injective.injOn)) hx
    change F.presheaf.map _ (x.val _) = 0 at h0
    have hinj := sectionsRestrict_bijective_of_eq F c
      (le_top : ((T.preimage j j.injective.injOn).map j.toEmbedding).inf W ≤ ⊤)
      (le_top : (T.preimage j j.injective.injOn).inf (W ∘ j) ≤ ⊤)
      (inf_map_orderEmbedding W j _).symm
    have h1 : x.val ((T.preimage j j.injective.injOn).map j.toEmbedding) = 0 :=
      hinj.1 (h0.trans (map_zero _).symm)
    rw [← hT'] at h1
    exact h1
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    exact cechRestrict_f_surjective F W j c p

end Kernel

section Twist

variable (F : X.Modules) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] (W : κ → X.Opens)
  (j : ι ↪o κ) (a : κ) (c : R →+* Γ(X, ⊤))

/-- The sign `(-1)^{#{i ∈ S | a < j i}}`. -/
def twistSign (S : Finset ι) : ℤ := (-1) ^ (S.filter (fun i => a < j i)).card

lemma twistSign_mul_self (S : Finset ι) : twistSign j a S * twistSign j a S = 1 := by
  unfold twistSign
  rw [← mul_pow]
  norm_num

lemma twistSign_erase {S : Finset ι} {i : ι} (hi : i ∈ S) :
    twistSign j a (S.erase i) = (if a < j i then -1 else 1) * twistSign j a S := by
  unfold twistSign
  rw [Finset.filter_erase]
  split_ifs with h
  · have hmem : i ∈ S.filter (fun k => a < j k) := Finset.mem_filter.mpr ⟨hi, h⟩
    have hcard := Finset.card_erase_add_one hmem
    rw [← hcard, pow_succ]
    ring
  · rw [Finset.erase_eq_of_notMem (by simp [h])]
    ring

lemma inf_insert_map (S : Finset ι) :
    (insert a (S.map j.toEmbedding)).inf W = W a ⊓ S.inf (W ∘ j) := by
  classical
  rw [Finset.inf_insert, inf_map_orderEmbedding]

/-- The twisted comparison of the cube of `W` with the cube of the link diagram of `W_a`:
`(Φ x)_S = ε(S) · x_{S ∪ {a}}`. -/
def twistCube (x : subsetCechCube (cechDiagram F W c)) :
    subsetCechCube (linkDiagram F (W ∘ j) (W a)) := fun S =>
  twistSign j a S • sectionsRestrictAdd F c (RingHom.id Γ(X, W a)) le_top inf_le_left
    (inf_insert_map W j a S).ge (x (insert a (S.map j.toEmbedding)))

lemma twistCube_zero : twistCube F W j a c 0 = 0 := by
  funext S
  simp only [twistCube]
  change twistSign j a S • sectionsRestrictAdd F c _ _ _ _ 0 = 0
  rw [map_zero, smul_zero]

lemma twistCube_card (n : ℕ) (x : subsetCechCube (cechDiagram F W c))
    (hx : x ∈ subsetCechCardPiece (cechDiagram F W c) (n + 1)) (ha : a ∉ Set.range j) :
    twistCube F W j a c x ∈ subsetCechCardPiece (linkDiagram F (W ∘ j) (W a)) n := by
  classical
  intro S hS
  have haS : a ∉ S.map j.toEmbedding := by simpa using fun i _ h => ha ⟨i, h⟩
  simp only [twistCube]
  rw [hx _ (by rw [Finset.card_insert_of_notMem haS, Finset.card_map]; omega), map_zero,
    smul_zero]

/-- The twisted comparison commutes with the differentials on cochains supported on subsets
containing `a`. -/
lemma twistCube_differential (ha : a ∉ Set.range j) (x : subsetCechCube (cechDiagram F W c))
    (hx : ∀ T, a ∉ T → x T = 0) :
    twistCube F W j a c (subsetCechDifferential _ x) =
      subsetCechDifferential _ (twistCube F W j a c x) := by
  classical
  funext S
  have haS : a ∉ S.map j.toEmbedding := by simpa using fun i _ h => ha ⟨i, h⟩
  simp only [twistCube]
  rw [subsetCechDifferential_apply (c := x) (S := insert a (S.map j.toEmbedding)),
    Finset.sum_insert haS]
  rw [subsetCechRestriction_value_congr _ x (Finset.erase_subset a _)
    (Finset.subset_insert a _) (Finset.erase_insert haS), hx _ haS, map_zero, smul_zero,
    zero_add, Finset.sum_map, map_sum, Finset.smul_sum, subsetCechDifferential_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : a ≠ j.toEmbedding i := fun h => ha ⟨i, h.symm⟩
  change _ = subsetCechSign S i • subsetCechRestriction (linkDiagram F (W ∘ j) (W a))
    (Finset.erase_subset i S) (twistSign j a (S.erase i) •
    sectionsRestrictAdd F c (RingHom.id Γ(X, W a)) le_top inf_le_left
      (inf_insert_map W j a (S.erase i)).ge (x (insert a ((S.erase i).map j.toEmbedding))))
  simp only [map_zsmul, smul_smul]
  congr 1
  · rw [subsetCechSign_insert_of_notMem a haS, subsetCechSign_map, twistSign_erase j a hi]
    simp only [RelEmbedding.coe_toEmbedding]
    ring
  · simp only [subsetCechRestriction]
    rw [sectionsRestrictAdd_sectionsRestrict, sectionsRestrict_sectionsRestrictAdd]
    have hidx : (insert a (S.map j.toEmbedding)).erase (j.toEmbedding i) =
        insert a ((S.erase i).map j.toEmbedding) := by
      rw [Finset.erase_insert_of_ne hne, Finset.map_erase]
    exact sectionsRestrictAdd_congr_index F c _ (fun _ => le_top) x hidx _ _ _

variable {j a}

/-- The indices of `T ∖ {a}` in `ι`. -/
def preIdx (T : Finset κ) : Finset ι := (T.erase a).preimage j j.injective.injOn

lemma map_preIdx (hall : ∀ x, x ≠ a → x ∈ Set.range j) (T : Finset κ) :
    (preIdx (j := j) (a := a) T).map j.toEmbedding = T.erase a := by
  classical
  rw [Finset.map_eq_image]
  apply Finset.image_preimage_of_bij
  refine ⟨fun _ hx => hx, j.injective.injOn, fun y hy => ?_⟩
  obtain ⟨i, hi⟩ := hall y (Finset.ne_of_mem_erase hy)
  refine ⟨i, ?_, hi⟩
  change j i ∈ ((T.erase a : Finset κ) : Set κ)
  rw [hi]
  exact hy

lemma insert_map_preIdx (hall : ∀ x, x ≠ a → x ∈ Set.range j) {T : Finset κ} (hT : a ∈ T) :
    insert a ((preIdx (j := j) (a := a) T).map j.toEmbedding) = T := by
  classical
  rw [map_preIdx hall, Finset.insert_erase hT]

lemma preIdx_insert_map (ha : a ∉ Set.range j) (S : Finset ι) :
    preIdx (j := j) (a := a) (insert a (S.map j.toEmbedding)) = S := by
  classical
  ext i
  simp only [preIdx, Finset.mem_preimage, Finset.mem_erase, Finset.mem_insert, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨-, h | ⟨i', hi', h⟩⟩
    · exact (ha ⟨i, h⟩).elim
    · rwa [← j.injective h]
  · intro hi
    exact ⟨fun h => ha ⟨i, h⟩, Or.inr ⟨i, hi, rfl⟩⟩

lemma inf_le_preIdx (hall : ∀ x, x ≠ a → x ∈ Set.range j) {T : Finset κ} (hT : a ∈ T) :
    T.inf W ≤ W a ⊓ (preIdx (j := j) (a := a) T).inf (W ∘ j) := by
  rw [← inf_insert_map W j a, insert_map_preIdx hall hT]

/-- The inverse of the twisted comparison: `(Ψ m)_T = ε(T ∖ a) · m_{T ∖ a}` for `a ∈ T`. -/
def untwistCube (hall : ∀ x, x ≠ a → x ∈ Set.range j)
    (m : subsetCechCube (linkDiagram F (W ∘ j) (W a))) :
    subsetCechCube (cechDiagram F W c) := fun T =>
  if h : a ∈ T then twistSign j a (preIdx (j := j) (a := a) T) •
    sectionsRestrictAdd F (RingHom.id Γ(X, W a)) c inf_le_left le_top (inf_le_preIdx W hall h)
      (m (preIdx T))
  else 0

lemma untwistCube_zero (hall : ∀ x, x ≠ a → x ∈ Set.range j) :
    untwistCube F W c hall 0 = 0 := by
  funext T
  simp only [untwistCube]
  split_ifs
  · change twistSign j a _ • sectionsRestrictAdd F _ c _ _ _ 0 = 0
    rw [map_zero, smul_zero]
  · rfl

lemma untwistCube_mem (hall : ∀ x, x ≠ a → x ∈ Set.range j) (p : ℕ)
    (m : subsetCechCube (linkDiagram F (W ∘ j) (W a)))
    (hm : m ∈ subsetCechCardPiece (linkDiagram F (W ∘ j) (W a)) p) :
    untwistCube F W c hall m ∈ subsetCechCardPiece (cechDiagram F W c) (p + 1) := by
  classical
  intro T hT
  simp only [untwistCube]
  split_ifs with h
  · have hcard : (preIdx (j := j) (a := a) T).card ≠ p := by
      have h1 := congrArg Finset.card (map_preIdx (j := j) (a := a) hall T)
      rw [Finset.card_map] at h1
      have h2 := Finset.card_erase_add_one h
      omega
    rw [hm _ hcard, map_zero, smul_zero]
  · rfl

lemma untwistCube_support (hall : ∀ x, x ≠ a → x ∈ Set.range j)
    (m : subsetCechCube (linkDiagram F (W ∘ j) (W a))) (T : Finset κ) (hT : a ∉ T) :
    untwistCube F W c hall m T = 0 := by
  simp only [untwistCube, dif_neg hT]

lemma twistCube_untwistCube (ha : a ∉ Set.range j) (hall : ∀ x, x ≠ a → x ∈ Set.range j)
    (m : subsetCechCube (linkDiagram F (W ∘ j) (W a))) :
    twistCube F W j a c (untwistCube F W c hall m) = m := by
  classical
  funext S
  have hmem : a ∈ insert a (S.map j.toEmbedding) := Finset.mem_insert_self _ _
  simp only [twistCube, untwistCube, dif_pos hmem]
  have hsign : twistSign j a S * twistSign j a (preIdx (j := j) (a := a)
      (insert a (S.map j.toEmbedding))) = 1 := by
    rw [preIdx_insert_map ha, twistSign_mul_self]
  rw [map_zsmul, smul_smul, hsign, one_smul, sectionsRestrictAdd_sectionsRestrictAdd']
  rw [sectionsRestrictAdd_congr_index F (RingHom.id Γ(X, W a)) (RingHom.id Γ(X, W a))
    (B := fun S => W a ⊓ S.inf (W ∘ j)) (fun _ => inf_le_left) m (preIdx_insert_map ha S)
    inf_le_left _ le_rfl, sectionsRestrictAdd_self]

lemma untwistCube_twistCube (hall : ∀ x, x ≠ a → x ∈ Set.range j)
    (x : subsetCechCube (cechDiagram F W c)) (hx : ∀ T, a ∉ T → x T = 0) :
    untwistCube F W c hall (twistCube F W j a c x) = x := by
  classical
  funext T
  by_cases hT : a ∈ T
  · simp only [untwistCube, twistCube, dif_pos hT]
    rw [map_zsmul, smul_smul, twistSign_mul_self, one_smul, sectionsRestrictAdd_sectionsRestrictAdd']
    rw [sectionsRestrictAdd_congr_index F c c (B := fun T => T.inf W) (fun _ => le_top) x
      (insert_map_preIdx hall hT) le_top _ le_rfl, sectionsRestrictAdd_self]
  · simp only [untwistCube, dif_neg hT]
    exact (hx T hT).symm

variable [F.IsQuasicoherent]

/-- The kernel complex is acyclic: it is the augmented Čech complex of the link of `a`. -/
theorem kerComplex_acyclic [Finite ι] (ha : a ∉ Set.range j)
    (hall : ∀ x, x ≠ a → x ∈ Set.range j) (hcov : W a ≤ ⨆ i, W (j i))
    (haff : ∀ S : Finset ι, IsAffineOpen (W a ⊓ S.inf (W ∘ j))) (p : ℕ) :
    Limits.IsZero ((kerComplex F W a c).homology p) := by
  have hVa : IsAffineOpen (W a) := by
    have := haff ∅
    rwa [Finset.inf_empty, inf_top_eq] at this
  have hexL := linkDiagram_exact F (W ∘ j) (W a) hVa hcov haff
  have htw : ∀ x : subsetCechCube (cechDiagram F W c), (∀ T, a ∉ T → x T = 0) →
      subsetCechDifferential _ x = 0 →
      ∃ y, subsetCechDifferential _ y = twistCube F W j a c x := by
    intro x hx hd
    apply (hexL _).mp
    rw [← twistCube_differential F W j a c ha x hx, hd, twistCube_zero]
  rcases p with _ | p
  · rw [isZero_homology_zero_iff, kerComplex_d, injective_iff_map_eq_zero]
    intro x hx
    have hd : subsetCechDifferential _ x.val.val = 0 := congrArg (fun z => z.val.val) hx
    obtain ⟨y, hy⟩ := htw x.val.val x.property hd
    have htw0 : twistCube F W j a c x.val.val = 0 := by
      funext S
      by_cases hS : S = ∅
      · subst hS
        rw [← hy, subsetCechDifferential_apply, Finset.sum_empty]
        rfl
      · exact twistCube_card F W j a c 0 x.val.val x.val.property ha S
          (fun h => hS (Finset.card_eq_zero.mp h))
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val = 0
    rw [← untwistCube_twistCube F W c hall x.val.val x.property, htw0, untwistCube_zero]
  · rw [isZero_homology_succ_iff]
    intro x hx
    rw [kerComplex_d] at hx
    have hd : subsetCechDifferential _ x.val.val = 0 := congrArg (fun z => z.val.val) hx
    obtain ⟨y, hy⟩ := htw x.val.val x.property hd
    let m := cubeCardProj (linkDiagram F (W ∘ j) (W a)) p y
    have hm : m ∈ subsetCechCardPiece (linkDiagram F (W ∘ j) (W a)) p := cubeCardProj_mem _ p y
    have htwx := twistCube_card F W j a c (p + 1) x.val.val x.val.property ha
    have hdm : subsetCechDifferential _ m = twistCube F W j a c x.val.val := by
      rw [subsetCechDifferential_cubeCardProj, hy]
      funext S
      simp only [cubeCardProj]
      split_ifs with hS
      · rfl
      · exact (htwx S hS).symm
    let z := untwistCube F W c hall m
    have hz : z ∈ subsetCechCardPiece (cechDiagram F W c) (p + 1) := untwistCube_mem F W c hall p m hm
    have hzK : (⟨z, hz⟩ : subsetCechCardPiece (cechDiagram F W c) (p + 1)) ∈
        kerPiece F W a c (p + 1) := untwistCube_support F W c hall m
    refine ⟨⟨⟨z, hz⟩, hzK⟩, ?_⟩
    rw [kerComplex_d]
    apply Subtype.ext
    apply Subtype.ext
    change subsetCechDifferential _ z = x.val.val
    have hdzK : ∀ T, a ∉ T → subsetCechDifferential _ z T = 0 :=
      kerPiece_differential F W a c (p + 1) ⟨z, hz⟩ hzK
    rw [← untwistCube_twistCube F W c hall _ hdzK, twistCube_differential F W j a c ha z
      (untwistCube_support F W c hall m), twistCube_untwistCube F W c ha hall, hdm,
      untwistCube_twistCube F W c hall _ x.property]

/-- **Adding one open** (blueprint `prop:sm-cech-refine`): if `κ = ι ⊔ {a}`, the opens `W_i`,
`i ∈ ι`, cover `W_a`, and all `W_a ∩ W_S` are affine, then restricting to the subfamily indexed by
`ι` is a quasi-isomorphism. -/
theorem isIso_homologyMap_cechRestrict_of_oneVertex [Finite ι] (ha : a ∉ Set.range j)
    (hall : ∀ x, x ≠ a → x ∈ Set.range j) (hcov : W a ≤ ⨆ i, W (j i))
    (haff : ∀ S : Finset ι, IsAffineOpen (W a ⊓ S.inf (W ∘ j))) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cechRestrict F W j c) p) :=
  isIso_homologyMap_g_of_acyclic (kerShortComplex_shortExact F W c ha hall)
    (kerComplex_acyclic F W c ha hall hcov haff) p

end Twist

section Independence

variable (F : X.Modules) [F.IsQuasicoherent] (c : R →+* Γ(X, ⊤))

/-- **Refinement by a covering subfamily** (blueprint `thm:sm-cech-independence`): let `W` be a
finite family with affine nonempty intersections and `e : ι ↪o κ` an order embedding such that
`W ∘ e` covers `X`. Then `Č(W, F) ⟶ Č(W ∘ e, F)` is a quasi-isomorphism. -/
theorem isIso_homologyMap_cechRestrict {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] [Finite κ]
    (W : κ → X.Opens) (e : ι ↪o κ) (hcov : ⨆ i, W (e i) = ⊤)
    (haff : ∀ T : Finset κ, T.Nonempty → IsAffineOpen (T.inf W)) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cechRestrict F W e c) p) := by
  classical
  have : Finite ι := Finite.of_injective e e.injective
  have key : ∀ n : ℕ, ∀ {κ : Type u} [LinearOrder κ] [Finite κ] (W : κ → X.Opens)
      (e : ι ↪o κ), Nat.card κ = Nat.card ι + n → ⨆ i, W (e i) = ⊤ →
      (∀ T : Finset κ, T.Nonempty → IsAffineOpen (T.inf W)) →
      ∀ p, IsIso (HomologicalComplex.homologyMap (cechRestrict F W e c) p) := by
    intro n
    induction n with
    | zero =>
      intro κ _ _ W e hcard _ _ p
      have hsurj : Function.Surjective e :=
        (e.injective.bijective_of_nat_card_le (by omega)).2
      have := isIso_cechRestrict_of_surjective F W e c hsurj
      exact Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
        (ComplexShape.up ℕ) p) (cechRestrict F W e c)
    | succ n ih =>
      intro κ _ _ W e hcard hcov haff p
      obtain ⟨a, ha⟩ : ∃ a, a ∉ Set.range e := by
        by_contra h
        push Not at h
        have := Nat.card_le_card_of_surjective e h
        omega
      let jj : {x : κ // x ≠ a} ↪o κ := OrderEmbedding.subtype _
      let e' : ι ↪o {x : κ // x ≠ a} :=
        OrderEmbedding.ofStrictMono (fun i => ⟨e i, fun h => ha ⟨i, h⟩⟩)
          (fun _ _ h => e.strictMono h)
      have hcard' : Nat.card {x : κ // x ≠ a} = Nat.card ι + n := by
        have h := Nat.card_congr (Equiv.optionSubtypeNe a)
        rw [Finite.card_option] at h
        omega
      have haff' : ∀ T : Finset {x : κ // x ≠ a}, T.Nonempty → IsAffineOpen (T.inf (W ∘ jj)) := by
        intro T hT
        rw [← inf_map_orderEmbedding]
        exact haff _ (hT.map)
      have h1 := ih (W ∘ jj) e' hcard' hcov haff' p
      have ha' : a ∉ Set.range jj := by
        rintro ⟨x, hx⟩
        exact x.property hx
      have hall : ∀ x, x ≠ a → x ∈ Set.range jj := fun x hx => ⟨⟨x, hx⟩, rfl⟩
      have hcovj : W a ≤ ⨆ i, W (jj i) := by
        calc W a ≤ ⨆ i, W (e i) := by rw [hcov]; exact le_top
          _ ≤ ⨆ i, W (jj i) := iSup_le fun i => le_iSup_of_le (e' i) le_rfl
      have haffj : ∀ S : Finset {x : κ // x ≠ a}, IsAffineOpen (W a ⊓ S.inf (W ∘ jj)) := by
        intro S
        rw [← inf_insert_map W jj a S]
        exact haff _ (Finset.insert_nonempty _ _)
      have h2 := isIso_homologyMap_cechRestrict_of_oneVertex F W c ha' hall hcovj haffj p
      let r₂ : cechComplex F (W ∘ jj) c ⟶ cechComplex F (W ∘ e) c := cechRestrict F (W ∘ jj) e' c
      have hcomp : cechRestrict F W e c = cechRestrict F W jj c ≫ r₂ :=
        (cechRestrict_comp F c W jj e').symm
      have h1' : IsIso (HomologicalComplex.homologyMap r₂ p) := h1
      rw [hcomp, HomologicalComplex.homologyMap_comp]
      infer_instance
  exact key _ W e (Nat.add_sub_of_le (Nat.card_le_card_of_injective e e.injective)).symm hcov
    haff p

variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]

/-- The family `U ⊔ V` indexed by the lexicographic sum `ι ⊕ₗ κ`. -/
def sumLexFamily (U : ι → X.Opens) (V : κ → X.Opens) : ι ⊕ₗ κ → X.Opens :=
  fun x => Sum.elim U V (ofLex x)

/-- The order embedding `ι ↪o ι ⊕ₗ κ`. -/
def inlLex : ι ↪o ι ⊕ₗ κ := OrderEmbedding.ofStrictMono _ Sum.Lex.inl_strictMono

/-- The order embedding `κ ↪o ι ⊕ₗ κ`. -/
def inrLex : κ ↪o ι ⊕ₗ κ := OrderEmbedding.ofStrictMono _ Sum.Lex.inr_strictMono

variable [Finite ι] [Finite κ] {U : ι → X.Opens} {V : κ → X.Opens}

instance : Finite (ι ⊕ₗ κ) := Finite.of_equiv (ι ⊕ κ) toLex

/-- **Independence of the cover** (blueprint `thm:sm-cech-independence`): two finite covers `U`,
`V` such that all nonempty intersections of the combined family are affine have isomorphic Čech
cohomology, through the restrictions from `Č(U ⊔ V, F)`. -/
def cechCohomologyIsoOfCovers (hU : ⨆ i, U i = ⊤) (hV : ⨆ k, V k = ⊤)
    (haff : ∀ T : Finset (ι ⊕ₗ κ), T.Nonempty → IsAffineOpen (T.inf (sumLexFamily U V)))
    (p : ℕ) : cechCohomology F U c p ≅ cechCohomology F V c p :=
  (@asIso _ _ _ _ (HomologicalComplex.homologyMap
      (cechRestrict F (sumLexFamily U V) (inlLex (ι := ι) (κ := κ)) c) p)
      (isIso_homologyMap_cechRestrict F c (sumLexFamily U V) inlLex hU haff p)).symm ≪≫
    @asIso _ _ _ _ (HomologicalComplex.homologyMap
      (cechRestrict F (sumLexFamily U V) (inrLex (ι := ι) (κ := κ)) c) p)
      (isIso_homologyMap_cechRestrict F c (sumLexFamily U V) inrLex hV haff p)

omit [LinearOrder ι] [LinearOrder κ] [Finite ι] [Finite κ] [F.IsQuasicoherent] in
/-- On a scheme with affine diagonal, all nonempty finite intersections of a family of affine
opens are affine. -/
theorem isAffineOpen_inf_sumLexFamily
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (hUa : ∀ i, IsAffineOpen (U i)) (hVa : ∀ k, IsAffineOpen (V k)) :
    ∀ T : Finset (ι ⊕ₗ κ), T.Nonempty → IsAffineOpen (T.inf (sumLexFamily U V)) := fun T hT => by
  have h := IsAffineOpen.biInf (U := sumLexFamily U V) (T : Set (ι ⊕ₗ κ)) T.finite_toSet
    (Finset.coe_nonempty.mpr hT) (fun x _ => by
      rcases x with i | k
      · exact hUa i
      · exact hVa k)
  simpa [Finset.inf_eq_iInf] using h

/-- On a scheme with affine diagonal (e.g. a separated scheme) any two finite affine covers have
isomorphic Čech cohomology. -/
def cechCohomologyIsoOfAffineCovers [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ k, V k = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (hVa : ∀ k, IsAffineOpen (V k)) (p : ℕ) : cechCohomology F U c p ≅ cechCohomology F V c p :=
  cechCohomologyIsoOfCovers F c hU hV (isAffineOpen_inf_sumLexFamily hUa hVa) p

omit [F.IsQuasicoherent] in
/-- Restriction to a subfamily is natural in the module, on cohomology. -/
lemma homologyMap_cechRestrict_naturality {ι' κ' : Type u} [LinearOrder ι'] [LinearOrder κ']
    {G : X.Modules} (φ : F ⟶ G) (W : κ' → X.Opens) (e : ι' ↪o κ') (p : ℕ) :
    HomologicalComplex.homologyMap (cechComplexMap W c φ) p ≫
        HomologicalComplex.homologyMap (cechRestrict G W e c) p =
      HomologicalComplex.homologyMap (cechRestrict F W e c) p ≫
        HomologicalComplex.homologyMap (cechComplexMap (W ∘ e) c φ) p := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    cechRestrict_naturality]

/-- The isomorphism `cechCohomologyIsoOfCovers` is natural in the quasi-coherent module. -/
lemma cechCohomologyIsoOfCovers_hom_naturality {G : X.Modules} [G.IsQuasicoherent] (φ : F ⟶ G)
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ k, V k = ⊤)
    (haff : ∀ T : Finset (ι ⊕ₗ κ), T.Nonempty → IsAffineOpen (T.inf (sumLexFamily U V)))
    (p : ℕ) :
    HomologicalComplex.homologyMap (cechComplexMap U c φ) p ≫
        (cechCohomologyIsoOfCovers G c hU hV haff p).hom =
      (cechCohomologyIsoOfCovers F c hU hV haff p).hom ≫
        HomologicalComplex.homologyMap (cechComplexMap V c φ) p := by
  have hF : IsIso (HomologicalComplex.homologyMap
      (cechRestrict F (sumLexFamily U V) (inlLex (ι := ι) (κ := κ)) c) p) :=
    isIso_homologyMap_cechRestrict F c _ _ hU haff p
  have hG : IsIso (HomologicalComplex.homologyMap
      (cechRestrict G (sumLexFamily U V) (inlLex (ι := ι) (κ := κ)) c) p) :=
    isIso_homologyMap_cechRestrict G c _ _ hU haff p
  have hl := homologyMap_cechRestrict_naturality F c φ (sumLexFamily U V)
    (inlLex (ι := ι) (κ := κ)) p
  have hr := homologyMap_cechRestrict_naturality F c φ (sumLexFamily U V)
    (inrLex (ι := ι) (κ := κ)) p
  change HomologicalComplex.homologyMap
        (cechComplexMap (sumLexFamily U V ∘ ⇑(inlLex (ι := ι) (κ := κ))) c φ) p ≫
      (@inv _ _ _ _ (HomologicalComplex.homologyMap
        (cechRestrict G (sumLexFamily U V) (inlLex (ι := ι) (κ := κ)) c) p) hG ≫
        HomologicalComplex.homologyMap
          (cechRestrict G (sumLexFamily U V) (inrLex (ι := ι) (κ := κ)) c) p) =
    (@inv _ _ _ _ (HomologicalComplex.homologyMap
        (cechRestrict F (sumLexFamily U V) (inlLex (ι := ι) (κ := κ)) c) p) hF ≫
        HomologicalComplex.homologyMap
          (cechRestrict F (sumLexFamily U V) (inrLex (ι := ι) (κ := κ)) c) p) ≫
      HomologicalComplex.homologyMap
        (cechComplexMap (sumLexFamily U V ∘ ⇑(inrLex (ι := ι) (κ := κ))) c φ) p
  have hl' : @inv _ _ _ _ (HomologicalComplex.homologyMap
      (cechRestrict F (sumLexFamily U V) (inlLex (ι := ι) (κ := κ)) c) p) hF ≫
      HomologicalComplex.homologyMap (cechComplexMap (sumLexFamily U V) c φ) p =
      HomologicalComplex.homologyMap
          (cechComplexMap (sumLexFamily U V ∘ ⇑(inlLex (ι := ι) (κ := κ))) c φ) p ≫
        @inv _ _ _ _ (HomologicalComplex.homologyMap
          (cechRestrict G (sumLexFamily U V) (inlLex (ι := ι) (κ := κ)) c) p) hG := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hl, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [← Category.assoc, ← hl', Category.assoc, hr, Category.assoc]

end Independence

end

end DeJongAlterations.StableModification.Cohomology
