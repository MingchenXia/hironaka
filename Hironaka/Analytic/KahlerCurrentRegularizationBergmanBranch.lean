import Hironaka.Analytic.LocalBergmanThetaBranch
import Hironaka.Analytic.AnalyticTypeChartTransport

set_option autoImplicit false

/-!
# Bounded analytic type of a local Bergman branch

A finite weighted Bergman family supplies a local theta-PSH branch.  This file
records the complementary statement about its singularities: on the branch
domain, its chart germ is a rational logarithmic presentation with a bounded
remainder.  The remainder is precisely the negative local potential.  The
statement deliberately remains local; a global regularization still requires
compatible finite collar data and a coherent global ideal.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.KahlerCurrentRegularizationBergmanBranch


open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open QuasiEquisingularAtlasTransport

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- In its defining chart, a Bergman branch has the local bounded-remainder
analytic singularity type supplied by its finite generator family. -/
theorem bergmanBranch_analyticTypeAt_ownChart
    {theta : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta u m) {y : ComplexModel n} (hy : y ∈ D.domain) :
    HasAnalyticSingularityTypeAt (chartFunction (bergmanBranch D) D.chart) y := by
  refine HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded
    (D.analyticType y hy) (b := fun z => -D.potential z) ?_ ?_
  · exact boundedRealGermAt_of_continuousAt
      ((D.localPotential.2.2.1 y hy).contDiffAt
        (D.localPotential.1.mem_nhds hy)).continuousAt.neg
  · filter_upwards [D.domain.isOpen.mem_nhds hy] with z hz
    have hzsource : D.chart.val.symm z ∈ D.source := by
      change D.chart.val.symm z ∈ D.chart.val.source ∧
        D.chart.val (D.chart.val.symm z) ∈ D.domain
      exact ⟨D.chart.val.map_target (D.domain_le_target hz),
        by rw [D.chart.val.right_inv (D.domain_le_target hz)]; exact hz⟩
    change bergmanBranch D (D.chart.val.symm z) =
      (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator z +
        ((-D.potential z : ℝ) : EReal)
    rw [bergmanBranch, dif_pos hzsource, D.chart.val.right_inv (D.domain_le_target hz),
      sub_eq_add_neg, ← EReal.coe_neg]

/-- In its defining chart, a Bergman branch has CT22 smooth analytic
singularities: the local potential appearing as its remainder is smooth. -/
theorem bergmanBranch_smoothAnalyticSingularitiesAt_ownChart
    {theta : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta u m) (hm : 0 < m)
    {y : ComplexModel n} (hy : y ∈ D.domain) :
    HasSmoothAnalyticSingularitiesAt (chartFunction (bergmanBranch D) D.chart) y := by
  refine ⟨(m : ℝ)⁻¹, D.N, D.generator, ?_⟩
  refine ⟨inv_pos.mpr (Nat.cast_pos.mpr hm),
    ⟨D.domain, D.domain.isOpen, hy,
      fun l => (D.generator_analytic l).differentiableOn⟩,
    fun z => -D.potential z, ?_, ?_⟩
  · filter_upwards [D.domain.isOpen.mem_nhds hy] with z hz
    exact ((D.localPotential.2.2.1 z hz).contDiffAt
      (D.localPotential.1.mem_nhds hz)).neg
  · filter_upwards [D.domain.isOpen.mem_nhds hy] with z hz
    have hzsource : D.chart.val.symm z ∈ D.source := by
      change D.chart.val.symm z ∈ D.chart.val.source ∧
        D.chart.val (D.chart.val.symm z) ∈ D.domain
      exact ⟨D.chart.val.map_target (D.domain_le_target hz),
        by rw [D.chart.val.right_inv (D.domain_le_target hz)]; exact hz⟩
    change bergmanBranch D (D.chart.val.symm z) =
      (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator z +
        ((-D.potential z : ℝ) : EReal)
    rw [bergmanBranch, dif_pos hzsource, D.chart.val.right_inv (D.domain_le_target hz),
      sub_eq_add_neg, ← EReal.coe_neg]

/-- The same bounded analytic type transports to every chart meeting the
Bergman branch domain. -/
theorem bergmanBranch_analyticTypeAt
    {theta : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta u m) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    HasAnalyticSingularityTypeAt (chartFunction (bergmanBranch D) e) z := by
  have htransition : z ∈ (chartTransition e D.chart).source := by
    change z ∈ e.val.target ∧ e.val.symm z ∈ D.chart.val.source
    exact ⟨hz, hzsource.1⟩
  have hy : chartTransition e D.chart z ∈ D.domain := by
    change D.chart.val (e.val.symm z) ∈ D.domain
    exact hzsource.2
  exact HasAnalyticSingularityTypeAt.chartTransition_precompose htransition
    (bergmanBranch_analyticTypeAt_ownChart D hy)

/-- The smooth-remainder analytic singularities of a Bergman branch transport
to every ambient chart meeting its source. -/
theorem bergmanBranch_smoothAnalyticSingularitiesAt
    {theta : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta u m) (hm : 0 < m) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    HasSmoothAnalyticSingularitiesAt (chartFunction (bergmanBranch D) e) z := by
  have htransition : z ∈ (chartTransition e D.chart).source := by
    change z ∈ e.val.target ∧ e.val.symm z ∈ D.chart.val.source
    exact ⟨hz, hzsource.1⟩
  have hy : chartTransition e D.chart z ∈ D.domain := by
    change D.chart.val (e.val.symm z) ∈ D.domain
    exact hzsource.2
  exact QuasiEquisingularAtlasTransport.HasSmoothAnalyticSingularitiesAt.chartTransition_precompose
    htransition (bergmanBranch_smoothAnalyticSingularitiesAt_ownChart D hm hy)

end

end Hironaka.KahlerCurrentRegularizationBergmanBranch
