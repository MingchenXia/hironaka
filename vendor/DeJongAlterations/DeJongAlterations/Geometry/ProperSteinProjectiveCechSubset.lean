import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Ring

/-! # The genuine finite subset Čech differential

The diagram is a native functor on the subset poset. In applications its values
are actual localized homogeneous module pieces and its arrows are the actual
localization maps. No injectivity of those arrows is assumed.
-/

/-!
Adapted from the same workspace `BingWangEntropy/FiniteSubsetCech.lean`,
SHA256 64cafd34a46474600294c5302a7a63d63381b124dbd337da4b06d49ad3882b90.
Only native Mathlib is imported; no other project module is imported.
-/

universe u v

open CategoryTheory

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type u} [CommRing K] {I : Type v} [LinearOrder I]

/-- The literal position sign in the increasing enumeration of a finite subset. -/
def subsetCechSign (S : Finset I) (i : I) : ℤ :=
  (-1) ^ (S.filter (fun j => j < i)).card

/-- Deleting a later vertex does not change an earlier vertex's position. -/
theorem subsetCechSign_erase_later (S : Finset I) {i j : I} (hij : i < j) :
    subsetCechSign (S.erase j) i = subsetCechSign S i := by
  unfold subsetCechSign
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp only [Finset.mem_filter, not_and]
  intro _
  exact not_lt_of_ge (le_of_lt hij)

/-- Deleting an earlier vertex reverses the sign of a later vertex. -/
theorem subsetCechSign_erase_earlier (S : Finset I) {i j : I}
    (hi : i ∈ S) (hij : i < j) :
    subsetCechSign S j = -subsetCechSign (S.erase i) j := by
  unfold subsetCechSign
  rw [Finset.filter_erase]
  have hmem : i ∈ S.filter (fun t => t < j) := Finset.mem_filter.mpr ⟨hi, hij⟩
  have hcard := Finset.card_erase_add_one hmem
  rw [← hcard, pow_succ]
  ring

/-- The two orders of deleting different vertices have opposite literal signs. -/
theorem subsetCechSign_two_deletions (S : Finset I) {i j : I}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    subsetCechSign S i * subsetCechSign (S.erase i) j =
      -(subsetCechSign S j * subsetCechSign (S.erase j) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · rw [subsetCechSign_erase_later S h, subsetCechSign_erase_earlier S hi h]
    ring
  · rw [subsetCechSign_erase_later S h, subsetCechSign_erase_earlier S hj h]
    ring

/-- The total finite cube of values of an actual subset diagram. -/
abbrev subsetCechCube (F : Finset I ⥤ ModuleCat.{max u v} K) :=
  ∀ S : Finset I, F.obj S

/-- An actual restriction arrow of the native diagram, viewed as a linear map. -/
def subsetCechRestriction (F : Finset I ⥤ ModuleCat.{max u v} K)
    {S T : Finset I} (h : S ⊆ T) : F.obj S →ₗ[K] F.obj T :=
  (F.map (homOfLE h)).hom

omit [LinearOrder I] in
@[simp]
theorem subsetCechRestriction_comp (F : Finset I ⥤ ModuleCat.{max u v} K)
    {S T U : Finset I} (hST : S ⊆ T) (hTU : T ⊆ U) (x : F.obj S) :
    subsetCechRestriction F hTU (subsetCechRestriction F hST x) =
      subsetCechRestriction F (hST.trans hTU) x := by
  change (F.map (homOfLE hST) ≫ F.map (homOfLE hTU)) x = _
  rw [← F.map_comp]
  rfl

omit [LinearOrder I] in
/-- Equality of subset indices identifies their actual restricted diagram values. -/
theorem subsetCechRestriction_value_congr
    (F : Finset I ⥤ ModuleCat.{max u v} K) (c : subsetCechCube F)
    {S T U : Finset I} (hS : S ⊆ U) (hT : T ⊆ U) (h : S = T) :
    subsetCechRestriction F hS (c S) = subsetCechRestriction F hT (c T) := by
  subst T
  rfl

/-- The alternating deletion differential on the actual diagram. -/
def subsetCechDifferential (F : Finset I ⥤ ModuleCat.{max u v} K) :
    subsetCechCube F →ₗ[K] subsetCechCube F where
  toFun c S := ∑ i ∈ S, subsetCechSign S i •
    subsetCechRestriction F (Finset.erase_subset i S) (c (S.erase i))
  map_add' c c' := by
    funext S
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    funext S
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

@[simp]
theorem subsetCechDifferential_apply (F : Finset I ⥤ ModuleCat.{max u v} K)
    (c : subsetCechCube F) (S : Finset I) :
    subsetCechDifferential F c S = ∑ i ∈ S, subsetCechSign S i •
      subsetCechRestriction F (Finset.erase_subset i S) (c (S.erase i)) := rfl

private def subsetCechDoubleTerm (F : Finset I ⥤ ModuleCat.{max u v} K)
    (c : subsetCechCube F) (S : Finset I) (i j : I) : F.obj S :=
  if i = j then 0 else
    (subsetCechSign S i * subsetCechSign (S.erase i) j) •
      subsetCechRestriction F
        ((Finset.erase_subset j (S.erase i)).trans (Finset.erase_subset i S))
        (c ((S.erase i).erase j))

private theorem subsetCechDoubleTerm_swap
    (F : Finset I ⥤ ModuleCat.{max u v} K) (c : subsetCechCube F)
    (S : Finset I) {i j : I} (hi : i ∈ S) (hj : j ∈ S) :
    subsetCechDoubleTerm F c S i j + subsetCechDoubleTerm F c S j i = 0 := by
  by_cases hij : i = j
  · subst j
    simp [subsetCechDoubleTerm]
  · simp only [subsetCechDoubleTerm, if_neg hij, if_neg (Ne.symm hij)]
    rw [subsetCechRestriction_value_congr F c _ _
      (Finset.erase_right_comm (a := i) (b := j))]
    rw [subsetCechSign_two_deletions S hi hj hij, neg_smul]
    exact neg_add_cancel _

/-- The actual alternating deletion differential squares to zero, even when the
actual restriction maps of the diagram are not injective. -/
theorem subsetCechDifferential_squared
    (F : Finset I ⥤ ModuleCat.{max u v} K) (c : subsetCechCube F) :
    subsetCechDifferential F (subsetCechDifferential F c) = 0 := by
  funext S
  simp only [subsetCechDifferential_apply, map_sum, map_zsmul, Finset.smul_sum,
    smul_smul, subsetCechRestriction_comp, Pi.zero_apply]
  have hexpand :
      (∑ i ∈ S, ∑ j ∈ S.erase i,
        (subsetCechSign S i * subsetCechSign (S.erase i) j) •
          subsetCechRestriction F
            ((Finset.erase_subset j (S.erase i)).trans (Finset.erase_subset i S))
            (c ((S.erase i).erase j))) =
        ∑ ij ∈ S ×ˢ S, subsetCechDoubleTerm F c S ij.1 ij.2 := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_erase S (f := subsetCechDoubleTerm F c S i)
      (a := i) (by simp [subsetCechDoubleTerm])]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [subsetCechDoubleTerm, if_neg (Finset.ne_of_mem_erase hj).symm]
  rw [hexpand]
  apply Finset.sum_involution (fun ij _ => (ij.2, ij.1))
  · rintro ⟨i, j⟩ hij
    exact subsetCechDoubleTerm_swap F c S
      (Finset.mem_product.mp hij).1 (Finset.mem_product.mp hij).2
  · rintro ⟨i, j⟩ _ hne hfix
    have hij : i = j := congrArg Prod.snd hfix
    subst j
    exact hne (by simp [subsetCechDoubleTerm])
  · rintro ⟨i, j⟩ hij
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hij).2, (Finset.mem_product.mp hij).1⟩
  · rintro ⟨i, j⟩ _
    rfl

/-- The verified total differential is a square-zero linear map. -/
theorem subsetCechDifferential_comp_self
    (F : Finset I ⥤ ModuleCat.{max u v} K) :
    (subsetCechDifferential F).comp (subsetCechDifferential F) = 0 := by
  apply LinearMap.ext
  intro c
  exact subsetCechDifferential_squared F c

/-- A cardinal-degree piece consists of the actual diagram values at subsets
of that cardinality, extended by zero at all other subsets. -/
def subsetCechCardPiece (F : Finset I ⥤ ModuleCat.{max u v} K) (n : ℕ) :
    Submodule K (subsetCechCube F) where
  carrier := {c | ∀ S : Finset I, S.card ≠ n → c S = 0}
  zero_mem' := by intro S _; rfl
  add_mem' := by intro c c' hc hc' S hS; simp only [Pi.add_apply, hc S hS, hc' S hS, add_zero]
  smul_mem' := by intro a c hc S hS; simp only [Pi.smul_apply, hc S hS, smul_zero]

/-- Actual deletion increases cardinal degree by one. -/
theorem subsetCechDifferential_mem_cardPiece
    (F : Finset I ⥤ ModuleCat.{max u v} K) (n : ℕ)
    (c : subsetCechCardPiece F n) :
    subsetCechDifferential F c.val ∈ subsetCechCardPiece F (n + 1) := by
  intro S hS
  apply Finset.sum_eq_zero
  intro i hi
  have hcard : (S.erase i).card ≠ n := by
    intro h
    exact hS (by simpa only [h] using (Finset.card_erase_add_one hi).symm)
  rw [c.property (S.erase i) hcard, map_zero, smul_zero]

/-- The literal differential between consecutive cardinal pieces. -/
def subsetCechCardDifferential (F : Finset I ⥤ ModuleCat.{max u v} K) (n : ℕ) :
    subsetCechCardPiece F n →ₗ[K] subsetCechCardPiece F (n + 1) :=
  ((subsetCechDifferential F).comp (subsetCechCardPiece F n).subtype).codRestrict
    (subsetCechCardPiece F (n + 1)) (subsetCechDifferential_mem_cardPiece F n)

@[simp]
theorem subsetCechCardDifferential_coe
    (F : Finset I ⥤ ModuleCat.{max u v} K) (n : ℕ)
    (c : subsetCechCardPiece F n) :
    (subsetCechCardDifferential F n c).val = subsetCechDifferential F c.val := rfl

/-- The actual cardinal-graded differential squares to zero. -/
theorem subsetCechCardDifferential_squared
    (F : Finset I ⥤ ModuleCat.{max u v} K) (n : ℕ)
    (c : subsetCechCardPiece F n) :
    subsetCechCardDifferential F (n + 1) (subsetCechCardDifferential F n c) = 0 := by
  apply Subtype.ext
  exact subsetCechDifferential_squared F c.val

/-- The native augmented normalized subset Čech complex, with the empty
intersection in degree zero and cardinal-n intersections in degree n. -/
def augmentedSubsetCechComplex (F : Finset I ⥤ ModuleCat.{max u v} K) :
    CochainComplex (ModuleCat.{max u v} K) ℕ :=
  CochainComplex.of
    (fun n => ModuleCat.of K (subsetCechCardPiece F n))
    (fun n => ModuleCat.ofHom (subsetCechCardDifferential F n))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact subsetCechCardDifferential_squared F n c)

/-- The native normalized subset Čech complex for the coordinate cover:
degree p contains the genuine intersections of p+1 opens. -/
def subsetCechComplex (F : Finset I ⥤ ModuleCat.{max u v} K) :
    CochainComplex (ModuleCat.{max u v} K) ℕ :=
  CochainComplex.of
    (fun p => ModuleCat.of K (subsetCechCardPiece F (p + 1)))
    (fun p => ModuleCat.ofHom (subsetCechCardDifferential F (p + 1)))
    (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact subsetCechCardDifferential_squared F (p + 1) c)

omit [LinearOrder I] in
/-- A finite coordinate cover has no subset terms above its actual cardinality. -/
theorem subsetCechCardPiece_eq_bot [Fintype I]
    (F : Finset I ⥤ ModuleCat.{max u v} K) (n : ℕ)
    (hn : Fintype.card I < n) : subsetCechCardPiece F n = ⊥ := by
  apply le_antisymm
  · intro c hc
    change c = 0
    funext S
    exact hc S (by
      intro h
      have hcard := Finset.card_le_univ S
      rw [h] at hcard
      exact (not_lt_of_ge hcard) hn)
  · exact bot_le

/-- The actual cardinal piece is the genuine finite dependent product over
subsets of that cardinality; the extension-by-zero representation adds no data. -/
def subsetCechCardProductEquiv
    (F : Finset I ⥤ ModuleCat.{max u v} K) (n : ℕ) :
    subsetCechCardPiece F n ≃ₗ[K]
      (∀ S : {S : Finset I // S.card = n}, F.obj S.val) where
  toFun c S := c.val S.val
  invFun c := ⟨fun S => if h : S.card = n then c ⟨S, h⟩ else 0, by
    intro S hS
    simp only [dif_neg hS]⟩
  left_inv c := by
    apply Subtype.ext
    funext S
    by_cases hS : S.card = n
    · simp only [dif_pos hS]
    · simp only [dif_neg hS, c.property S hS]
  right_inv c := by
    funext S
    simp only [dif_pos S.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A map of actual localized diagrams acts pointwise on the actual Čech cube. -/
def subsetCechCubeMap {F G : Finset I ⥤ ModuleCat.{max u v} K} (α : F ⟶ G) :
    subsetCechCube F →ₗ[K] subsetCechCube G where
  toFun c S := α.app S (c S)
  map_add' c c' := by funext S; exact (α.app S).hom.map_add _ _
  map_smul' a c := by funext S; exact (α.app S).hom.map_smul _ _

/-- Actual diagram naturality commutes with the literal alternating differential. -/
theorem subsetCechCubeMap_comm {F G : Finset I ⥤ ModuleCat.{max u v} K}
    (α : F ⟶ G) (c : subsetCechCube F) :
    subsetCechCubeMap α (subsetCechDifferential F c) =
      subsetCechDifferential G (subsetCechCubeMap α c) := by
  funext S
  change (α.app S).hom (∑ i ∈ S, _) = ∑ i ∈ S, _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  exact ConcreteCategory.congr_hom (α.naturality (homOfLE (Finset.erase_subset i S)))
    (c (S.erase i))

/-- An actual diagram map preserves cardinal degree. -/
def subsetCechCardMap {F G : Finset I ⥤ ModuleCat.{max u v} K}
    (α : F ⟶ G) (n : ℕ) :
    subsetCechCardPiece F n →ₗ[K] subsetCechCardPiece G n :=
  ((subsetCechCubeMap α).comp (subsetCechCardPiece F n).subtype).codRestrict
    (subsetCechCardPiece G n) (by
      intro c S hS
      change α.app S (c.val S) = 0
      rw [c.property S hS, map_zero])

/-- The induced map on the native normalized finite subset Čech complexes. -/
def subsetCechComplexMap {F G : Finset I ⥤ ModuleCat.{max u v} K} (α : F ⟶ G) :
    subsetCechComplex F ⟶ subsetCechComplex G :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom (subsetCechCardMap α (p + 1))) (by
      intro p
      simp only [subsetCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact (subsetCechCubeMap_comm α c.val).symm)

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
