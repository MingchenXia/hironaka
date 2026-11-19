import Hironaka.Resolution.HironakaG8OddCuspVanishingStalk
import Hironaka.Resolution.HironakaActualRegularIntrinsicHSProfile
import Hironaka.Resolution.HironakaActualHistoricalCentreFilteredDivision

/-! The literal embedded cusp is an analytic singular source with its
entire intrinsic point profile computed in the displayed chart. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG8OddCuspGeometricSource
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HolGerm HironakaRelativeNormalMonomialBasis HironakaActualPrincipalHSFormula
  HironakaHolomorphicJetChartInvariance
  HironakaActualZeroSectionStabilization HironakaActualHistoricalCentreFilteredDivision
  HironakaActualPointGeometricBennett HironakaActualRegularIntrinsicHSProfile
  HironakaEmbeddedAnalytic HironakaG8NativeCuspDiagram HironakaG8SameHSCuspContact
  HironakaG8OddCuspVanishingStalk

theorem embedded_cusp_isAnalytic (p : ℕ) :
    IsComplexAnalyticSubset (n := 3) (embeddedCuspSet p) := by
  intro x
  have hc : (complexChartAt (n := 3) x).val = OpenPartialHomeomorph.refl (ComplexModel 3) := by
    simp [complexChartAt, chartAt_self_eq]
  refine ⟨{
    generatorCount := 2
    generator := embeddedCuspEquations p
    coordinateNeighborhood := univ
    isOpen_coordinateNeighborhood := isOpen_univ
    center_mem_coordinateNeighborhood := mem_univ _
    coordinateNeighborhood_subset_target := by rw [hc]; exact subset_rfl
    generator_holomorphic := ?_
    zeroLocus := ?_ }⟩
  · intro i
    apply Differentiable.differentiableOn
    fin_cases i
    · change Differentiable ℂ (fun z : ComplexModel 3 => z.ofLp 1 ^ 2 - z.ofLp 0 ^ p)
      exact ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable.pow 2).sub
        ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable.pow p)
    · change Differentiable ℂ (fun z : ComplexModel 3 => z.ofLp 2)
      exact (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable
  · intro y _ _
    rw [hc]
    rfl

private theorem order_two (p : ℕ) (hp : 2 < p) :
    let I := IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2))
    cuspGerm p ∈ I ^ 2 ∧ cuspGerm p ∉ I ^ 3 := by
  have hDegree (i : Fin 2) (k : ℕ) : normalExponentDegree (Finsupp.single i k) = k := by
    simp [normalExponentDegree, Finsupp.single_apply]
  constructor
  · apply (actual_maximal_power_iff_formal_coefficients_zero 2 2 _).mpr
    intro a ha
    have h1 : a ≠ Finsupp.single (1 : Fin 2) 2 := fun h => (Nat.ne_of_lt ha) (h ▸ hDegree 1 2)
    have h0 : a ≠ Finsupp.single (0 : Fin 2) p := fun h =>
      (Nat.ne_of_lt (ha.trans hp)) (h ▸ hDegree 0 p)
    simp [cusp_actual_taylor, cuspSeries, MvPowerSeries.coeff_X_pow, h1, h0]
  · intro h
    have hh := (actual_maximal_power_iff_formal_coefficients_zero 2 3 _).mp h
      (Finsupp.single (1 : Fin 2) 2) (by simp [hDegree])
    have hne : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single (0 : Fin 2) p := by
      intro he
      have he' := congrArg (fun a : Fin 2 →₀ ℕ => a 1) he
      simp at he'
    simp [cusp_actual_taylor, cuspSeries, MvPowerSeries.coeff_X_pow, hne] at hh

/-- The intrinsic Hilbert–Samuel profile at the actual geometric cusp point. -/
theorem embedded_odd_cusp_geometric_profile (p : ℕ) (hp : Odd p) (hp2 : 2 < p) (l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 3) (embeddedCuspSet p)) 0 l =
      Nat.choose (2+l) 2 - (if 2 ≤ l then Nat.choose (2+(l-2)) 2 else 0) := by
  rw [hilbertSamuelAt_model_zero, embedded_odd_cusp_vanishing_stalk p hp,
    embeddedCuspIdeal, hilbertSamuelValue_actualZeroSectionIdeal,
    hilbertSamuelValue_actual_principal _ 2 (order_two p hp2).1 (order_two p hp2).2]

/-- The actual anchor is singular. Orders one and two rule out every
possible smooth dimension through the intrinsic regular profile. -/
theorem embedded_odd_cusp_singular_at_zero (p : ℕ) (hp : Odd p) (hp2 : 2 < p) :
    (0 : ComplexModel 3) ∈ singularSet (n := 3) (embeddedCuspSet p) := by
  rw [mem_singularSet_iff]
  constructor
  · intro i
    fin_cases i
    · change (0 : ℂ)^2 - 0^p = 0
      simp [zero_pow (by omega : p ≠ 0)]
    · rfl
  · intro d hd
    have hd3 : d ≤ 3 := hd.1
    have h1 := (hilbertSamuelAt_actual_regular hd3 hd 1).symm.trans
      (embedded_odd_cusp_geometric_profile p hp hp2 1)
    have h2 := (hilbertSamuelAt_actual_regular hd3 hd 2).symm.trans
      (embedded_odd_cusp_geometric_profile p hp hp2 2)
    interval_cases d <;> first | (norm_num at h1; done) | (norm_num at h2; exact (by decide : ¬ Nat.choose 4 2 = Nat.choose 4 2 - 1) h2)

end
end Hironaka.HironakaG8OddCuspGeometricSource
