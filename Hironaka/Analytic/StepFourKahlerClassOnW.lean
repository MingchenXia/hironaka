import Hironaka.Analytic.SubmanifoldRestrictionPositivity
import Hironaka.Analytic.ResidualNef
import Hironaka.Analytic.StepSixLocalGeometry

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 4: a Kähler class on `W`, delivered as positivity along `T_W`

Source: Copy-4, `prop:principalization`, Step 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1880-1906`):

> [...] the function `φ' := (π|_W)^*φ_{K,ℓ} + τψ_{E_rel}|_W` has log singularities
> along `D|_W` with the restricted metric [...] so `θ' + ddᶜφ'` is a Kähler current
> on `W`.  By `lem:residual-nef`, the class
> `{θ'} - {D|_W} = {θ_Y - Θ_D - ½δ₀π^*ω}|_W` (`eq:AW-class`) is Kähler on `W`.

and the first sentences of Step 6 (`:1968-1984`), which choose a Kähler form
`A_W = (θ_Y - Θ_D - ½δ₀π^*ω)|_W + ddᶜf` in that class and an extension `f̃` of `f`.

## What is proved

`exists_positiveOnOneFlattening_of_logSingularities`: if `W` is the image of a
holomorphic immersion `ι : V → Y` of a compact connected complex `k`-manifold, and
on `V` there is a Kähler-current potential `φ'` of a form `θ'` with log
singularities along a metered divisor `D_W` such that `θ' - Θ_{D_W} = ι^*β`
coefficientwise (this is `eq:AW-class` at the level of forms, with
`β = θ_Y - Θ_D - ½δ₀π^*ω`), and if chart-smooth functions on `V` extend to `Y`
along `ι`, then there is a chart-smooth `f̃` on `Y` with

  `PositiveOnOneFlattening W k (β + ddᶜf̃)`,

which is exactly the hypothesis of `StepSixLocalGeometry`.
`exists_localGeometry_of_logSingularities` composes the two: Step 4 + Step 6
give the six local-geometry fields `U, σ, smooth_sigma, dominates_beta,
open_neighbourhood, transform_subset` of the Step-5 structure.

## What it rests on

* `lem:residual-nef`, Kähler half, applied **on `V`**
  (`ResidualNef.exists_chartSmooth_isKahler_sub_curvature`).  That theorem is
  proved from two named classical inputs, Demailly CADG I.5.24
  (`PshRemovableSingularity`) and Demailly 1992 for bounded potentials
  (`BoundedPotentialSmoothing`, itself derived from the one Demailly-2.6 input),
  so this module is NOT sorry-free in its axioms; `#print axioms` shows
  `sorryAx` through exactly those two.
* the restriction calculus of `SubmanifoldRestrictionPositivity` (sorry-free).

Explicit hypotheses, not interfaces: the immersion `ι` (a complex structure on
`W`), the extension property of `ι` (Lee, *Introduction to Smooth Manifolds*,
Lemma 5.34, in the chart-smooth setting), and the Step-4 current `φ'` on `W`
(built in Copy-4 from Step 1 and `sec:positive-current`, which waits on QEA).
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.StepFourKahlerClassOnW

open Hironaka.PositiveClasses Hironaka.HolomorphicMaps
  Hironaka.HolomorphicIdealSheaves Hironaka.AnalyticGluingData
  ManifoldTubePositivity TubePositivityOneFlattening SubmanifoldRestrictionPositivity
  ResidualNefReduction ResidualNef StepSixLocalGeometry

noncomputable section

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Copy-4 Step 4, as positivity along `T_W`.**  `lem:residual-nef` on `V`
makes `ι^*β + ddᶜh` Kähler for a chart-smooth `h`; an extension `f̃` of `h`
then makes `β + ddᶜf̃` strictly positive along the tangent directions of
`W = ι(V)`. -/
theorem exists_positiveOnOneFlattening_of_logSingularities
    [CompactSpace V] [ConnectedSpace V] [Nonempty V]
    {W : Set M} (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (himm : ∀ (e : ComplexChart k V) (d : ComplexChart n M) (z : ComplexModel k),
      z ∈ coordinateDomain ι e d → Function.Injective (fderiv ℝ (coordinateMap ι e d) z))
    (hmaps : ∀ v, ι v ∈ W) (hsurj : ∀ w ∈ W, ∃ v, ι v = w)
    (β : ClosedRealOneOneForm n M)
    {θ' : ClosedRealOneOneForm k V} {DW : MeteredEffectiveQDivisor k V} {φ' : V → EReal}
    (hφ' : IsKahlerCurrentPotential θ' φ') (hlog : HasLogSingularitiesAlong DW φ')
    (hclass : ∀ (e : ComplexChart k V) (z : ComplexModel k), z ∈ e.val.target →
      (θ' - DW.curvature).val.coeff e z = (ClosedRealOneOneForm.pullback hι β).val.coeff e z)
    (hext : ∀ h : V → ℝ, ChartSmooth (n := k) h →
      ∃ f : M → ℝ, ChartSmooth (n := n) f ∧ ∀ v, f (ι v) = h v) :
    ∃ (f : M → ℝ) (hf : ChartSmooth (n := n) f),
      PositiveOnOneFlattening W k (β + ddcClosedForm f hf) := by
  obtain ⟨h, hh, hK⟩ := exists_chartSmooth_isKahler_sub_curvature hφ' hlog
  obtain ⟨f, hf, hfh⟩ := hext h hh
  refine ⟨f, hf, positiveOnOneFlattening_add_ddc_of_isKahler hWreg hι himm hmaps hsurj β hh
    ⟨fun e z hz => ?_, (ClosedRealOneOneForm.pullback hι β + ddcClosedForm h hh).2.1⟩
    hf hfh⟩
  have hcoeff : (ClosedRealOneOneForm.pullback hι β + ddcClosedForm h hh).val.coeff e z =
      ((θ' - DW.curvature) + ddcClosedForm h hh).val.coeff e z := by
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, hclass e z hz]
  rw [hcoeff]
  exact hK.1 e z hz

/-- **Copy-4 Steps 4 and 6, the local geometry of the Step-5 datum.**  Under the
hypotheses of `exists_positiveOnOneFlattening_of_logSingularities`, on a compact
`Y` with closed `W` there are an open `U ⊇ W` and a chart-smooth `σ` with
`β + ddᶜσ` dominating a Kähler form on `U`. -/
theorem exists_localGeometry_of_logSingularities [CompactSpace M]
    (omega : KahlerBackground n M)
    [CompactSpace V] [ConnectedSpace V] [Nonempty V]
    {W : Set M} (hWclosed : IsClosed W) (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (himm : ∀ (e : ComplexChart k V) (d : ComplexChart n M) (z : ComplexModel k),
      z ∈ coordinateDomain ι e d → Function.Injective (fderiv ℝ (coordinateMap ι e d) z))
    (hmaps : ∀ v, ι v ∈ W) (hsurj : ∀ w ∈ W, ∃ v, ι v = w)
    (β : ClosedRealOneOneForm n M)
    {θ' : ClosedRealOneOneForm k V} {DW : MeteredEffectiveQDivisor k V} {φ' : V → EReal}
    (hφ' : IsKahlerCurrentPotential θ' φ') (hlog : HasLogSingularitiesAlong DW φ')
    (hclass : ∀ (e : ComplexChart k V) (z : ComplexModel k), z ∈ e.val.target →
      (θ' - DW.curvature).val.coeff e z = (ClosedRealOneOneForm.pullback hι β).val.coeff e z)
    (hext : ∀ h : V → ℝ, ChartSmooth (n := k) h →
      ∃ f : M → ℝ, ChartSmooth (n := n) f ∧ ∀ v, f (ι v) = h v) :
    ∃ (U : Set M) (σ : M → ℝ), IsOpen U ∧ W ⊆ U ∧ ChartSmooth (n := n) σ ∧
      DominatesKahlerFormOn β (fun x => (σ x : EReal)) U := by
  obtain ⟨f, hf, hpos⟩ := exists_positiveOnOneFlattening_of_logSingularities hWreg hι himm
    hmaps hsurj β hφ' hlog hclass hext
  exact exists_localGeometry_of_positiveOnOneFlattening omega hWclosed hWreg β hf hpos

end

end Hironaka.StepFourKahlerClassOnW
