/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeOrder
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialOrdering
import Hironaka.Invariant.MonomialCaseAlong

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionRelativeMonomial
open Hironaka.HolomorphicIdealSheaves
open GermIdealOrder DivisorExponentAlong MonomialCase MonomialCaseAlong MonomialInvariant BoundaryCount
  NormalCrossings MarkedIdeals HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionDivisorExponents HironakaSmoothSubmersionMonomialOrdering
  HironakaSmoothSubmersionRelativeOrder
noncomputable section
variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
variable {f : Y → X}
variable (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
  {I : GermIdeal n X} (hI : I.IsCoherent)
include hf hI

/-- Every genuine nearby relative divisibility predicate is exactly pulled back in every degree. -/
theorem isDivNearAlong_preimage_iff (N H : Set X) (e : ℕ) (y : Y) :
    IsDivNearAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (f ⁻¹' H) e y ↔
      IsDivNearAlong n N I H e (f y) := by
  unfold IsDivNearAlong
  rw [cosupport_preimage_eq hf hI N e,
    ← map_nhds_submersion_eq (hf.isSubmersionAt y), Filter.eventually_map]
  rfl

/-- The literal original relative exponent retains both actual first failure and original fallback. -/
theorem divExpAlong_preimage_eq (N H : Set X) (y : Y) :
    divExpAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (f ⁻¹' H) y =
      divExpAlong n N I H (f y) := by
  classical
  have hP : (fun e => IsDivNearAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I)
      (f ⁻¹' H) e y) = fun e => IsDivNearAlong n N I H e (f y) :=
    funext fun e => propext (isDivNearAlong_preimage_iff hf hI N H e y)
  unfold divExpAlong
  show (if h : ∃ e, ¬ (fun e => IsDivNearAlong m (f ⁻¹' N)
      (GermIdeal.pullback (m := m) f I) (f ⁻¹' H) e y) (e+1) then Nat.find h else 0) =
    (if h : ∃ e, ¬ (fun e => IsDivNearAlong n N I H e (f y)) (e+1) then Nat.find h else 0)
  rw [hP]

/-- The entire original relative indexed function retains every literal boundary entry and beyond-length zero. -/
theorem expDataAlong_preimage_eq (N : Set X) (E : List (Set X)) (y : Y) :
    expDataAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) y =
      expDataAlong n N I E (f y) := by
  funext i
  unfold expDataAlong
  by_cases hi : i < E.length
  · have hi' : i < (E.map (f ⁻¹' ·)).length := by simpa using hi
    rw [dif_pos hi',dif_pos hi]
    have hget : (E.map (f ⁻¹' ·)).get ⟨i,hi'⟩ = f ⁻¹' E.get ⟨i,hi⟩ := by simp
    rw [hget]
    exact divExpAlong_preimage_eq hf hI N _ y
  · have hi' : ¬ i < (E.map (f ⁻¹' ·)).length := by simpa using hi
    rw [dif_neg hi',dif_neg hi]

omit hf hI in
private theorem memberIdx_preimage_eq (E : List (Set X)) (g : Y → X) (y : Y) :
    memberIdx (E.map (g ⁻¹' ·)) y = memberIdx E (g y) := by
  ext i
  rw [mem_memberIdx,mem_memberIdx]
  constructor
  · rintro ⟨hi,hx⟩
    exact ⟨by simpa using hi,by simpa using hx⟩
  · rintro ⟨hi,hx⟩
    exact ⟨by simpa using hi,by simpa using hx⟩

/-- Genuine source-dimensional relative gamma is read in the same entire original indexed data. -/
theorem gammaAlong_preimage_dictionary (N : Set X) (E : List (Set X)) (d : ℕ) (y : Y) :
    gammaAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d y =
      inv m (memberIdx E (f y)) (expDataAlong n N I E (f y)) d := by
  unfold gammaAlong
  rw [memberIdx_preimage_eq,expDataAlong_preimage_eq hf hI N E y]

/-- Equal ambient dimensions preserve the literal whole original relative gamma value. -/
theorem gammaAlong_same_dimension_preimage_eq (hmn : m = n)
    (N : Set X) (E : List (Set X)) (d : ℕ) (y : Y) :
    gammaAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d y =
      gammaAlong n N I E d (f y) := by
  rw [gammaAlong_preimage_dictionary hf hI N E d y,hmn]
  rfl

/-- Actual original SNC internally supplies all bounds for whole relative gamma comparisons across dimensions. -/
theorem gammaAlong_preimage_le_iff (N : Set X) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (d : ℕ) (y z : Y) :
    gammaAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d y ≤
      gammaAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d z ↔
    gammaAlong n N I E d (f y) ≤ gammaAlong n N I E d (f z) := by
  rw [gammaAlong_preimage_dictionary hf hI N E d y,
    gammaAlong_preimage_dictionary hf hI N E d z]
  exact (inv_le_inv_dimension_iff n m (dimension_le_of_submersionAt (hf.isSubmersionAt y))
    (memberIdx E (f y)) (memberIdx E (f z)) (expDataAlong n N I E (f y))
    (expDataAlong n N I E (f z)) d d (card_memberIdx_le E hE (f y))
    (card_memberIdx_le E hE (f z))).symm

/-- Actual whole original relative gamma equality is preserved and reflected, including all colex ties and bottom. -/
theorem gammaAlong_preimage_eq_iff (N : Set X) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (d : ℕ) (y z : Y) :
    gammaAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d y =
      gammaAlong m (f ⁻¹' N) (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d z ↔
    gammaAlong n N I E d (f y) = gammaAlong n N I E d (f z) := by
  rw [le_antisymm_iff,le_antisymm_iff,gammaAlong_preimage_le_iff hf hI N hE d y z,
    gammaAlong_preimage_le_iff hf hI N hE d z y]

omit hI in
/-- Surjectivity transports the entire original relative marked maximum locus without replacing its actual underlying set. -/
theorem maxLocus_gammaAlong_markedPullback_eq (hsurj : Function.Surjective f)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) (hME : IsSNCDivisor n M.E) :
    ResolutionDriver.maxLocus
      (gammaAlong m (markedPullback (m := m) f M).N (markedPullback (m := m) f M).ideal
        (markedPullback (m := m) f M).E M.d) (markedPullback (m := m) f M).cosupp =
    f ⁻¹' ResolutionDriver.maxLocus (gammaAlong n M.N M.ideal M.E M.d) M.cosupp := by
  have hcs : (markedPullback (m := m) f M).cosupp = f ⁻¹' M.cosupp :=
    cosupport_preimage_eq hf hM M.N M.d
  ext y
  change (y ∈ (markedPullback (m := m) f M).cosupp ∧ ∀ z ∈
    (markedPullback (m := m) f M).cosupp,
    gammaAlong m (markedPullback (m := m) f M).N (markedPullback (m := m) f M).ideal
      (markedPullback (m := m) f M).E M.d z ≤
    gammaAlong m (markedPullback (m := m) f M).N (markedPullback (m := m) f M).ideal
      (markedPullback (m := m) f M).E M.d y) ↔
    f y ∈ M.cosupp ∧ ∀ x ∈ M.cosupp,
      gammaAlong n M.N M.ideal M.E M.d x ≤ gammaAlong n M.N M.ideal M.E M.d (f y)
  rw [hcs]
  constructor
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,?_⟩
    intro x hx
    obtain ⟨z,rfl⟩ := hsurj x
    exact (gammaAlong_preimage_le_iff hf hM M.N hME M.d z y).mp (hmax z hx)
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,?_⟩
    intro z hz
    exact (gammaAlong_preimage_le_iff hf hM M.N hME M.d z y).mpr (hmax (f z) hz)

end
end Hironaka.HironakaSmoothSubmersionRelativeMonomial
