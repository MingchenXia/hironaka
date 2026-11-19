import Hironaka.Analytic.ChartWeightedL2Transfer
import Hironaka.Analytic.PotentialTheory.MultiplierIdeals
import Hironaka.Analytic.HolomorphicIdealSheaves

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Reading a germ of `𝓘(mφ)` in a fixed chart, against the corrected weight

Source: Copy-4, `lem:regularization`, Step 4 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

The local half of `lem:regularization` is proved in `ℂᵈ`
(`QuantitativeRegularizationGermGeneratorDomination`) for the **corrected** weight
`Ψ = φ ∘ e⁻¹ + ρ`, where `ρ` is a smooth local potential of `θ` in one fixed chart `e`:
`Ψ` is the honestly plurisubharmonic function, while `φ ∘ e⁻¹` alone is only quasi-psh.

The hypothesis the target supplies is membership in `𝓘(mφ)` at a point `y`, which by
definition (`Hironaka.HolomorphicIdealSheaves.multiplierIdeal`) is tested in the
**preferred chart at `y`** and against the **raw** weight `φ ∘ (complexChartAt y)⁻¹`.

Two changes are therefore needed before the `ℂᵈ` statement applies at a point `y ≠ x` of
the fixed chart, and this module performs exactly those two:

* the chart, by `ChartWeightedL2.multiplierIntegrableAt_chart` (weighted integrability is
  a biholomorphic invariant; the only side condition is upper semicontinuity of the raw
  chart representative on the overlap, which holds because a θ-psh potential is
  quasi-psh in every chart);
* the weight, from `φ ∘ e⁻¹` to `Ψ = φ ∘ e⁻¹ + ρ`, by
  `multiplierIntegrableAt_of_moreSingularAt`: `ρ` is continuous, hence bounded below near
  the point, so the two weights have comparable singularity, and `Ψ` is plurisubharmonic
  there, which is the quasi-psh hypothesis that lemma asks of the target weight.

Nothing here is specific to Bergman kernels or to a generating system; it is the chart
bookkeeping that separates the model statement from the manifold statement.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Hironaka.QuantitativeRegularizationChartGermTransfer

noncomputable section

open Hironaka.HolomorphicIdealSheaves

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- A continuous real function is bounded below near every point of its domain, so
adding it to a weight changes the singularity type by a constant only. -/
theorem moreSingularAt_add_continuous {u : ComplexModel d → EReal}
    {ρ : ComplexModel d → ℝ} {W : Set (ComplexModel d)} (hW : IsOpen W)
    (hρ : ContinuousOn ρ W) {z : ComplexModel d} (hz : z ∈ W) :
    MoreSingularAt u (fun w => u w + (ρ w : EReal)) z := by
  have hcont : ContinuousAt ρ z := (hρ z hz).continuousAt (hW.mem_nhds hz)
  have hnear : ∀ᶠ w in 𝓝 z, ρ z - 1 < ρ w := by
    have := hcont.eventually (p := fun r => ρ z - 1 < r)
      (eventually_gt_nhds (by linarith) : ∀ᶠ r in 𝓝 (ρ z), ρ z - 1 < r)
    exact this
  refine ⟨1 - ρ z, ?_⟩
  filter_upwards [hnear] with w hw
  have hnn : (0 : ℝ) ≤ ρ w + (1 - ρ z) := by linarith
  calc u w ≤ u w + ((ρ w + (1 - ρ z) : ℝ) : EReal) := by
        simpa using le_add_of_nonneg_right (EReal.coe_nonneg.mpr hnn)
    _ = (u w + (ρ w : EReal)) + ((1 - ρ z : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]

/-- **Passing from the raw chart weight to the corrected one.**  If `Ψ = u + ρ` is
plurisubharmonic near `z` with `ρ` continuous there, weighted integrability against `u`
implies weighted integrability against `Ψ`. -/
theorem multiplierIntegrableAt_add_continuous {u : ComplexModel d → EReal}
    {ρ : ComplexModel d → ℝ} {W : Set (ComplexModel d)} (hW : IsOpen W)
    (hρ : ContinuousOn ρ W)
    (hpsh : PlurisubharmonicOn (fun w => u w + (ρ w : EReal)) W)
    {z : ComplexModel d} (hz : z ∈ W) {m : ℝ} {g : ComplexModel d → ℂ}
    (h : MultiplierIntegrableAt u m g z volume) :
    MultiplierIntegrableAt (fun w => u w + (ρ w : EReal)) m g z volume :=
  Hironaka.multiplierIntegrableAt_of_moreSingularAt
    (hpsh z hz).quasiPlurisubharmonicAt
    (moreSingularAt_add_continuous hW hρ hz) h

/-- **A germ of `𝓘(mφ)` read in a fixed chart against the corrected weight.**

`y` is an arbitrary point of the chart source whose image lies in the domain `W` of the
smooth local potential `ρ`; the conclusion is the hypothesis shape of the model statement
`QuantitativeRegularizationGermGeneratorDomination.exists_generators_generatorLog_le_of_plurisubharmonicOn`
at the point `e y`. -/
theorem multiplierIntegrableAt_corrected_of_mem_multiplierIdeal
    {θ : SmoothRealForm d Z 2} {φ : Z → EReal} (hφ : ThetaPlurisubharmonic θ φ)
    (e : ComplexChart d Z) {W : Set (ComplexModel d)} (hW : IsOpen W)
    {ρ : ComplexModel d → ℝ} (hρ : ContinuousOn ρ W)
    (hpsh : PlurisubharmonicOn (fun w => chartFunction φ e w + (ρ w : EReal)) W)
    {m : ℝ} (hm : 0 < m) {y : Z} (hy : y ∈ e.val.source) (hyW : e.val y ∈ W)
    {g : Z → ℂ} (hg : (multiplierIdeal (n := d) m φ).mem y g) :
    MultiplierIntegrableAt (fun w => chartFunction φ e w + (ρ w : EReal)) m
      (fun w => g (e.val.symm w)) (e.val y) volume := by
  have husc : UpperSemicontinuousOn (chartFunction φ e)
      (ChartWeightedL2.overlapDomain e (complexChartAt (n := d) y)) :=
    (hφ.quasiPlurisubharmonic e).upperSemicontinuousOn.mono fun _ hw => hw.1
  have hbase : MultiplierIntegrableAt (chartFunction φ e) m
      (fun w => g (e.val.symm w)) (e.val y) volume :=
    ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) (g := g)
      e (complexChartAt (n := d) y) hy (mem_complexChartAt_source (n := d) y)
      husc hm.ne' hg.2
  exact multiplierIntegrableAt_add_continuous hW hρ hpsh hyW hbase

end

end Hironaka.QuantitativeRegularizationChartGermTransfer
