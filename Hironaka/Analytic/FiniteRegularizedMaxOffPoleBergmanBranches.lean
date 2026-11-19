import Hironaka.Analytic.FiniteRegularizedMaxOffPoleCoreCover
import Hironaka.Analytic.ShiftedBergmanBranchFixedCoefficient
import Hironaka.Analytic.UniformLocalBergmanFiniteAtlas
import Hironaka.Analytic.KahlerCurrentRegularizationRegularizedMax
import Hironaka.Analytic.ShiftedBergmanBranchTop

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Bergman branches of a uniform atlas share one coefficient

`Hironaka.FiniteRegularizedMaxOffPoleCoreCover` runs the core-cover recursion in the
`I-0489` convention, and the only thing it asks of the branches is
`BranchesOffPoleWithCoefficient c`: each branch has such a presentation with ONE
fixed coefficient `c`, the generator families being free.  This module supplies
that hypothesis for the actual shifted Bergman branches.

The coefficient is `1/m`, uniformly, and that is exactly why a
`QuasiEquisingularBergmanAtlas.FiniteUniformLocalBergmanAtlas θ u m` is the right
object: all its patches sit at the same level `m`.  Two steps:

* in its own chart the shifted branch is `m⁻¹ · log ∑ |g_l|² + (a - φ)` with `φ`
  the smooth local potential — the coefficient is visible and the remainder is
  smooth (`shiftedBergmanBranch_smoothLogarithmicTypeAt_ownChart`, the
  coefficient-explicit form of
  `Hironaka.ShiftedBergmanBranch.shiftedBergmanBranch_smoothAnalyticSingularitiesAt_ownChart`);
* `Hironaka.QuasiEquisingularAtlasTransport.SmoothLogarithmicTypeAt.chartTransition_precompose`
  carries that to every overlapping ambient chart WITH THE SAME COEFFICIENT,
  precomposing the generators with the transition.

Weakening the strong presentation to the `I-0489` one at the end costs nothing
(`SmoothLogarithmicTypeAt.boundedSmoothOffPole`) and is what lets the branches be
combined with no alignment at all.

The consequence recorded at the end is the one that matters for Demailly
regularization: the regularized-max stage of a uniform Bergman atlas has analytic
singularities in the `I-0489` convention, with **no** hypothesis on the seed, **no**
alignment of generator families, and no analytic input beyond the atlas itself —
only the combinatorial condition that the collar cores cover `M`.  Compare the
field `hsmoothOffPole` of
`Hironaka.DemaillyRegularizedMaxBergmanDataInterface.RegularizedMaxBergmanChartFrameData`,
which assumes this conclusion; here it is proved from the cover.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.FiniteRegularizedMaxOffPoleBergmanBranches

open Hironaka

open Hironaka.AnalyticGluingData
open Hironaka.NumericalRestrictedVolumeScaffold
open Hironaka.NonKahlerLocus
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open QuasiEquisingularAtlasTransport
open ShiftedBergmanBranch
open ShiftedBergmanBranchTop
open FiniteRegularizedMaxCoreCover
open KahlerCurrentRegularizationRegularizedMax
open FiniteRegularizedMaxOffPoleCoreCover

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The shifted Bergman branch, in its own chart, with the coefficient kept
explicit.**  This is
`Hironaka.ShiftedBergmanBranch.shiftedBergmanBranch_smoothAnalyticSingularitiesAt_ownChart`
without the existential wrapper: the coefficient is `m⁻¹`, the generators are the
patch's own, and the remainder is `a - φ` for the smooth local potential `φ`.

Keeping the coefficient is the whole point — `Fin.append` merges generator
families but not coefficients, so the regularized-max recursion can only run at a
FIXED `c`, and `m⁻¹` is that `c`. -/
theorem shiftedBergmanBranch_smoothLogarithmicTypeAt_ownChart
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) (hm : 0 < m)
    {y : ComplexModel n} (hy : y ∈ D.domain) :
    SmoothLogarithmicTypeAt (chartFunction (shiftedBergmanBranch D a) D.chart)
      ((m : ℝ)⁻¹) D.generator y := by
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

/-- The same coefficient `m⁻¹` on every overlapping ambient chart; only the
generator family changes, by precomposition with the chart transition. -/
theorem shiftedBergmanBranch_smoothLogarithmicTypeAt
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) (hm : 0 < m)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    SmoothLogarithmicTypeAt (chartFunction (shiftedBergmanBranch D a) e) ((m : ℝ)⁻¹)
      (fun l y => D.generator l (chartTransition e D.chart y)) z := by
  have htransition : z ∈ (chartTransition e D.chart).source := by
    change z ∈ e.val.target ∧ e.val.symm z ∈ D.chart.val.source
    exact ⟨hz, hzsource.1⟩
  have hy : chartTransition e D.chart z ∈ D.domain := by
    change D.chart.val (e.val.symm z) ∈ D.domain
    exact hzsource.2
  exact SmoothLogarithmicTypeAt.chartTransition_precompose htransition
    (shiftedBergmanBranch_smoothLogarithmicTypeAt_ownChart D a hm hy)

/-- **The branches of a uniform Bergman atlas all carry the coefficient `m⁻¹`.**
This is the hypothesis `BranchesOffPoleWithCoefficient` of the off-pole
core-cover recursion, discharged for the real branches.  The shifts `a` are
arbitrary, so the feasible collar shifts of the regularized-max route are
covered. -/
theorem branchesOffPoleWithCoefficient_shiftedBergmanBranch
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (atlas : FiniteUniformLocalBergmanAtlas θ u m) (hm : 0 < m)
    (a : Fin atlas.count → ℝ) :
    BranchesOffPoleWithCoefficient (n := n) ((m : ℝ)⁻¹)
      (fun j => ((atlas.patch j).patch.source : Set M))
      (fun j => shiftedBergmanBranch (atlas.patch j).patch (a j)) := by
  intro i e z hz hzsource
  have hs : e.val.symm z ∈ (atlas.patch i).patch.source := hzsource
  exact ⟨(atlas.patch i).patch.N,
    fun l y => (atlas.patch i).patch.generator l
      (chartTransition e (atlas.patch i).patch.chart y),
    (shiftedBergmanBranch_smoothLogarithmicTypeAt (atlas.patch i).patch (a i) hm e hz
      hs).boundedSmoothOffPole⟩

/-! ### The regularized-max stage in the `I-0489` convention -/

/-- The off-pole analogue of
`Hironaka.KahlerCurrentRegularizationRegularizedMax.regularizedMaxStageKahlerCurrent_hasManifoldSmoothAnalyticSingularities`:
the pair (`hbranchsing`, `PolewiseAlignedBranches`) is replaced by the single
one-coefficient hypothesis. -/
theorem regularizedMaxStageKahlerCurrent_hasManifoldAnalyticSingularitiesSmoothOffPole
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) {δ : ℝ} (hδ : 0 < δ)
    {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    (H : RegularizedMaxCoreData δ U branch T.potential)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val (branch i) (U i))
    (hbranchtop : ∀ i x, branch i x ≠ ⊤)
    {c : ℝ} (hbranchoffpole : BranchesOffPoleWithCoefficient (n := n) c U branch)
    (hcover : ∀ x : M, ∃ i : Fin q, x ∈ H.inner i) {k : ℕ} (hk : q ≤ k) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n)
      (regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k).potential :=
  hasManifoldAnalyticSingularitiesSmoothOffPole_finiteRegularizedMaxGlued_of_coreCover hδ H
    hbranchtop (Hironaka.RegularizedMaxERealPshRoute.ThetaPlurisubharmonic.ne_top
      T.strictlyPsh.1) hbranchoffpole hcover hk

/-- **The regularized-max stage of a uniform Bergman atlas has analytic
singularities in the `I-0489` convention.**

No hypothesis on the seed `T.potential`, no alignment of generator families, and
no analytic input beyond the atlas: what is assumed is the collar/core data, the
`θ`-PSH-ness of each branch, and that the cores cover `M`.

This is the field `hsmoothOffPole` of
`Hironaka.DemaillyRegularizedMaxBergmanDataInterface.RegularizedMaxBergmanChartFrameData`
— which assumes exactly this conclusion, calling it "Demailly's Step 3--4
smoothness conclusion" — proved from the cover. -/
theorem regularizedMaxStageKahlerCurrent_hasManifoldAnalyticSingularitiesSmoothOffPole_shiftedBergman
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) {m : ℕ} (hm : 0 < m)
    (atlas : FiniteUniformLocalBergmanAtlas
      (T.representative - T.lowerBound.form).val T.potential m)
    {δ : ℝ} (hδ : 0 < δ) (a : Fin atlas.count → ℝ)
    (H : RegularizedMaxCoreData δ (fun j => ((atlas.patch j).patch.source : Set M))
      (fun j => shiftedBergmanBranch (atlas.patch j).patch (a j)) T.potential)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val
      (shiftedBergmanBranch (atlas.patch i).patch (a i))
      ((atlas.patch i).patch.source : Set M))
    (hcover : ∀ x : M, ∃ i, x ∈ H.inner i) {k : ℕ} (hk : atlas.count ≤ k) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n)
      (regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k).potential :=
  regularizedMaxStageKahlerCurrent_hasManifoldAnalyticSingularitiesSmoothOffPole T hδ H hbranch
    (fun i => shiftedBergmanBranch_ne_top_of_thetaPlurisubharmonicOn
      (atlas.patch i).patch (a i) (hbranch i))
    (branchesOffPoleWithCoefficient_shiftedBergmanBranch atlas hm a) hcover hk

end

end Hironaka.FiniteRegularizedMaxOffPoleBergmanBranches
