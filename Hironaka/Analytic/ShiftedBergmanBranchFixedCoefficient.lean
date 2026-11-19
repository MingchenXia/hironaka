import Hironaka.Analytic.ShiftedBergmanBranch
import Hironaka.Analytic.AnalyticTypeChartTransport

set_option autoImplicit false

/-!
# Fixed-coefficient analytic presentations for shifted Bergman branches

A local Bergman branch has the rational coefficient `1 / m` before and after
a finite real translation.  This module keeps that coefficient explicit rather
than discarding it through the existential analytic-type interface.  In the
defining chart the shifted local potential is the bounded remainder; the
existing chart-transition transport then retains the same coefficient on every
overlapping ambient chart.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.ShiftedBergmanBranchFixedCoefficient


open Hironaka.AnalyticGluingData
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open QuasiEquisingularAtlasTransport
open ShiftedBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- At every point of its own coordinate domain, a shifted Bergman branch has
the explicit rational coefficient `1 / m`; the smooth local potential and
the constant shift form its bounded remainder. -/
theorem shiftedBergmanBranch_logarithmicTypeAt_ownChart
    {theta : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta u m) (a : ℝ) (hm : 0 < m)
    {y : ComplexModel n} (hy : y ∈ D.domain) :
    LogarithmicTypeAt (chartFunction (shiftedBergmanBranch D a) D.chart)
      (((m : ℚ)⁻¹ : ℚ) : ℝ) D.generator y := by
  refine ⟨?_, ⟨D.domain, D.domain.isOpen, hy,
    fun l => (D.generator_analytic l).differentiableOn⟩,
    fun z => -D.potential z + a, ?_, ?_⟩
  · exact_mod_cast inv_pos.mpr (Nat.cast_pos.mpr hm)
  · exact boundedRealGermAt_of_continuousAt
      (((D.localPotential.2.2.1 y hy).contDiffAt
        (D.localPotential.1.mem_nhds hy)).continuousAt.neg.add continuousAt_const)
  · filter_upwards [D.domain.isOpen.mem_nhds hy] with z hz
    have hzsource : D.chart.val.symm z ∈ D.source := by
      change D.chart.val.symm z ∈ D.chart.val.source ∧
        D.chart.val (D.chart.val.symm z) ∈ D.domain
      exact ⟨D.chart.val.map_target (D.domain_le_target hz),
        by rw [D.chart.val.right_inv (D.domain_le_target hz)]; exact hz⟩
    have hcoef : (((((m : ℚ)⁻¹ : ℚ) : ℝ) : EReal)) =
        ((((m : ℝ)⁻¹ : ℝ) : EReal)) := by
      congr 1
      norm_num
    change shiftedBergmanBranch D a (D.chart.val.symm z) =
      (((((m : ℚ)⁻¹ : ℚ) : ℝ) : EReal) * generatorLog D.generator z) +
        ((-D.potential z + a : ℝ) : EReal)
    rw [shiftedBergmanBranch, bergmanBranch, dif_pos hzsource,
      D.chart.val.right_inv (D.domain_le_target hz), sub_eq_add_neg,
      ← EReal.coe_neg, hcoef, EReal.coe_add]
    ac_rfl

/-- The same fixed rational coefficient transports to every ambient chart
whose coordinate point lies in the shifted branch source.  Its generator
family is explicitly precomposed with the chart transition, so different
overlapping branches can be combined by the generator-max interface. -/
theorem shiftedBergmanBranch_logarithmicTypeAt
    {theta : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta u m) (a : ℝ) (hm : 0 < m)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    LogarithmicTypeAt (chartFunction (shiftedBergmanBranch D a) e)
      (((m : ℚ)⁻¹ : ℚ) : ℝ)
      (fun l y => D.generator l (chartTransition e D.chart y)) z := by
  have htransition : z ∈ (chartTransition e D.chart).source := by
    change z ∈ e.val.target ∧ e.val.symm z ∈ D.chart.val.source
    exact ⟨hz, hzsource.1⟩
  have hy : chartTransition e D.chart z ∈ D.domain := by
    change D.chart.val (e.val.symm z) ∈ D.domain
    exact hzsource.2
  exact LogarithmicTypeAt.chartTransition_precompose htransition
    (shiftedBergmanBranch_logarithmicTypeAt_ownChart D a hm hy)

end
end Hironaka.ShiftedBergmanBranchFixedCoefficient
