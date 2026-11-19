import Hironaka.Analytic.QuantitativeRegularizationMultiplierGermFamily
import Hironaka.Analytic.HolomorphicIdealSheaves

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The local half of Copy-4 `lem:regularization`, stated on the manifold

Source: Copy-4, `lem:regularization`, Step 4 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`QuantitativeRegularizationMultiplierGermFamily` proves Step 4 in the model `ℂᵈ` from the
germ hypothesis `MultiplierIntegrableAt u m gᵢ z volume`.  The statement of
`QuantitativeRegularization` is about a manifold `Z` and asks for germs of the sheaf
`multiplierIdeal m φ`.

No coordinate transfer is needed for the *hypothesis*: `multiplierIdeal m φ` is defined at
`x` through the **preferred chart at `x`**, so
`(multiplierIdeal m φ).mem x g` is literally `HolomorphicAt d g x` together with
`MultiplierIntegrableAt (chartFunction φ (complexChartAt x)) m (g ∘ (complexChartAt x).symm)`
at `(complexChartAt x) x`.  What has to be transported is the *conclusion*, and only
across the chart source, where `e.symm ∘ e = id`; that is what
`generatorLog_comp_symm_eventuallyEq` records.

The consequence worth stating plainly: the local lower bound
`φ_m ≥ m⁻¹ log ∑ᵢ|gᵢ|² + O(1)` holds for **every** finite family of germs of `𝓘(mφ)` at
`x`, not only for a generating system.  The Lean statement of the target quantifies
exactly over finite families, so this route needs no Nadel coherence anywhere.  What is
still missing between here and the target is the *global* object: one `φ_m` on all of `Z`,
glued from the chart branches with a single curvature loss `c/m`.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology BigOperators

namespace Hironaka.QuantitativeRegularizationManifoldGermFamily

noncomputable section

open Hironaka.MongeAmpere Hironaka.HolomorphicIdealSheaves BergmanSupWeight
open Hironaka.QuantitativeRegularizationMultiplierGermFamily

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- Reading a family of functions on `Z` in a chart does not change its logarithmic
generator weight, at any point of the chart source. -/
theorem generatorLog_comp_symm_eventuallyEq (e : ComplexChart d Z) {x : Z}
    (hx : x ∈ e.val.source) {N : ℕ} (g : Fin N → Z → ℂ) :
    ∀ᶠ y in 𝓝 x,
      generatorLog (fun i z => g i (e.val.symm z)) (e.val y) = generatorLog g y := by
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  simp only [generatorLog_eq_log_sum, e.val.left_inv hy]

/-- **Step 4 of `lem:regularization` on the manifold, for an arbitrary germ family.**

For every finite family `g` of germs of `𝓘(mφ)` at `x` there is one real constant `C`
with

> `m⁻¹ log ∑ᵢ |gᵢ(y)|² - C ≤ m⁻¹ log K_{B_j}(e(y), e^{-mφ∘e⁻¹})`

for all `y` near `x`, where `e` is the preferred chart at `x` and `B_j` is any Bergman
domain containing `e(x)` and relatively compact in the convex `A ⋐ Ω`.

No generating system of `𝓘(mφ)` appears, so nothing here needs coherence. -/
theorem exists_const_eventually_generatorLog_le_bergmanLog_of_multiplierIdeal
    (hd : 0 < d) {A Ω : Opens (ComplexModel d)}
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    {φ : Z → EReal} {x : Z}
    (hu : PlurisubharmonicOn (chartFunction φ (complexChartAt (n := d) x)) Ω)
    {m : ℝ} (hm : 0 < m)
    {Bj Bjc : Set (ComplexModel d)} (hBjo : IsOpen Bj) (hBjBjc : Bj ⊆ Bjc)
    (hBjc : IsCompact Bjc) (hBjcA : Bjc ⊆ (A : Set (ComplexModel d)))
    {S : ℝ} (hnormS : ∀ z ∈ Bj, ‖z‖ ≤ S)
    (hxBj : (complexChartAt (n := d) x).val x ∈ Bj)
    {N : ℕ} {g : Fin N → Z → ℂ}
    (hg : ∀ i, (multiplierIdeal (n := d) m φ).mem x (g i)) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      ((m⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal)
        ≤ ((m⁻¹ : ℝ) : EReal) *
            bergmanLog Bj
              (fun z => multiplierWeight m
                (chartFunction φ (complexChartAt (n := d) x) z))
              ((complexChartAt (n := d) x).val y) := by
  obtain ⟨C, hC⟩ :=
    exists_const_eventually_generatorLog_le_bergmanLog_of_multiplierIntegrableAt
      (d := d) (u := chartFunction φ (complexChartAt (n := d) x))
      (g := fun i z => g i ((complexChartAt (n := d) x).val.symm z))
      hd hAconv hAΩ hu hm hBjo hBjBjc hBjc hBjcA hnormS hxBj (fun i => (hg i).2)
  refine ⟨C, ?_⟩
  have hcont : ContinuousAt (complexChartAt (n := d) x).val x :=
    (complexChartAt (n := d) x).val.continuousAt
      (mem_complexChartAt_source (n := d) x)
  filter_upwards [hcont.eventually hC,
    generatorLog_comp_symm_eventuallyEq (complexChartAt (n := d) x)
      (mem_complexChartAt_source (n := d) x) g] with y hy hyeq
  rwa [hyeq] at hy

end

end Hironaka.QuantitativeRegularizationManifoldGermFamily
