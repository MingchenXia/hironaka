import Hironaka.Analytic.KahlerCurrentRegularizationBergmanBranch
import Hironaka.Analytic.PotentialTheory.PshAddition

set_option autoImplicit false

/-!
# Real shifts of local Bergman branches

A finite real translation does not alter the local Bergman branch's curvature
or analytic singularities.  This file records those two local facts while
keeping the branch domain explicit; it makes no assertion that raw collar data
already supplies the comparison constants needed for a finite gluing.
-/

open Set Filter
open scoped Topology

namespace Hironaka.ShiftedBergmanBranch


open Hironaka.AnalyticGluingData
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open QuasiEquisingularAtlasTransport
open KahlerCurrentRegularizationBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The local Bergman branch translated by a finite real constant. -/
noncomputable def shiftedBergmanBranch
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) : M → EReal :=
  fun x => bergmanBranch D x + (a : EReal)

/-- A real shift retains the theta-plurisubharmonic branch condition on the
same patch source. -/
theorem shiftedBergmanBranch_thetaPlurisubharmonicOn
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (hm : 0 < m) (a : ℝ) :
    ThetaPlurisubharmonicOn θ (shiftedBergmanBranch D a) D.source := by
  intro e z hz hzsource
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ :=
    bergmanBranch_thetaPlurisubharmonicOn D hm e z hz hzsource
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have hconst : PlurisubharmonicOn (fun _ : ComplexModel n => (a : EReal)) W :=
    fun y _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) y
  simpa [shiftedBergmanBranch, chartFunction, add_assoc, add_left_comm, add_comm] using
    hpsh.add hconst

/-- In its defining chart, a finite real shift has the same analytic
singularity type at every point of the patch domain. -/
theorem shiftedBergmanBranch_analyticTypeAt_ownChart
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ)
    {y : ComplexModel n} (hy : y ∈ D.domain) :
    HasAnalyticSingularityTypeAt
      (chartFunction (shiftedBergmanBranch D a) D.chart) y := by
  refine HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded
    (bergmanBranch_analyticTypeAt_ownChart D hy) (b := fun _ => a) ?_ ?_
  · exact boundedRealGermAt_of_continuousAt continuousAt_const
  · exact Filter.Eventually.of_forall fun z => by
      rfl

/-- A finite real shift preserves the strong smooth-remainder analytic
singularities of a local Bergman branch. -/
theorem shiftedBergmanBranch_smoothAnalyticSingularitiesAt_ownChart
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) (hm : 0 < m)
    {y : ComplexModel n} (hy : y ∈ D.domain) :
    HasSmoothAnalyticSingularitiesAt
      (chartFunction (shiftedBergmanBranch D a) D.chart) y := by
  refine ⟨(m : ℝ)⁻¹, D.N, D.generator, ?_⟩
  refine ⟨inv_pos.mpr (Nat.cast_pos.mpr hm),
    ⟨D.domain, D.domain.isOpen, hy,
      fun l => (D.generator_analytic l).differentiableOn⟩,
    fun z => -D.potential z + a, ?_, ?_⟩
  · filter_upwards [D.domain.isOpen.mem_nhds hy] with z hz
    exact ((D.localPotential.2.2.1 z hz).contDiffAt
      (D.localPotential.1.mem_nhds hz)).neg.add contDiffAt_const
  · filter_upwards [D.domain.isOpen.mem_nhds hy] with z hz
    have hzsource : D.chart.val.symm z ∈ D.source := by
      change D.chart.val.symm z ∈ D.chart.val.source ∧
        D.chart.val (D.chart.val.symm z) ∈ D.domain
      exact ⟨D.chart.val.map_target (D.domain_le_target hz),
        by rw [D.chart.val.right_inv (D.domain_le_target hz)]; exact hz⟩
    change shiftedBergmanBranch D a (D.chart.val.symm z) =
      (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator z +
        ((-D.potential z + a : ℝ) : EReal)
    rw [shiftedBergmanBranch, bergmanBranch, dif_pos hzsource,
      D.chart.val.right_inv (D.domain_le_target hz), sub_eq_add_neg,
      ← EReal.coe_neg, EReal.coe_add]
    ac_rfl

/-- The strong analytic singularities of a shifted Bergman branch transport
through every overlapping complex chart. -/
theorem shiftedBergmanBranch_smoothAnalyticSingularitiesAt
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) (hm : 0 < m)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    HasSmoothAnalyticSingularitiesAt (chartFunction (shiftedBergmanBranch D a) e) z := by
  have htransition : z ∈ (chartTransition e D.chart).source := by
    change z ∈ e.val.target ∧ e.val.symm z ∈ D.chart.val.source
    exact ⟨hz, hzsource.1⟩
  have hy : chartTransition e D.chart z ∈ D.domain := by
    change D.chart.val (e.val.symm z) ∈ D.domain
    exact hzsource.2
  exact QuasiEquisingularAtlasTransport.HasSmoothAnalyticSingularitiesAt.chartTransition_precompose
    htransition (shiftedBergmanBranch_smoothAnalyticSingularitiesAt_ownChart D a hm hy)

/-- A local upper bound by a branch plus `a` is exactly an upper bound by its
shifted branch. -/
theorem le_shiftedBergmanBranch_of_le_add_const
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) {v : M → EReal} {x : M}
    (h : v x ≤ bergmanBranch D x + (a : EReal)) :
    v x ≤ shiftedBergmanBranch D a x := by
  simpa [shiftedBergmanBranch] using h

/-- A branch-to-candidate estimate shifts by the same finite real amount,
with the target constant accumulated explicitly. -/
theorem shiftedBergmanBranch_le_add_of_le_add
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) {g : M → EReal} {C : ℝ} {x : M}
    (h : bergmanBranch D x ≤ g x + (C : EReal)) :
    shiftedBergmanBranch D a x ≤ g x + ((C + a : ℝ) : EReal) := by
  calc
    shiftedBergmanBranch D a x = bergmanBranch D x + (a : EReal) := rfl
    _ ≤ (g x + (C : EReal)) + (a : EReal) := add_le_add h le_rfl
    _ = g x + ((C + a : ℝ) : EReal) := by
      rw [EReal.coe_add, add_assoc]

end
end Hironaka.ShiftedBergmanBranch
