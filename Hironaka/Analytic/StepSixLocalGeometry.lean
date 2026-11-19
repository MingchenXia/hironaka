import Hironaka.Analytic.TubePositivityOneFlattening
import Hironaka.Analytic.GlobalPotentialTransforms

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 6: the local geometry of the Step-5 datum from Step 4's positivity

Source: Copy-4, `prop:principalization`, Step 6
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1968-1984`):

> Choose a Kähler form `A_W` in the class `eq:AW-class`, and a smooth function `f`
> on `W` such that `A_W = (θ_Y - Θ_D - ½δ₀ π^*ω)|_W + ddᶜf`.  Extend `f` to a smooth
> function `f̃` near `W` [...] For `B ≫ 1`, there is a relatively compact
> neighborhood `U` of `W` on a neighborhood of whose closure
> `Ω_U := θ_Y - Θ_D - ½δ₀ π^*ω + ddᶜ(f̃ + B r_W²) > 0` [...] In particular, `Ω_U`
> dominates a Kähler form on `U`.

## What this module does

In `PrincipalizationCopy4StepFiveCoreReduction.Copy4StepFiveExceptionalWeightData`
the fields `U`, `sigma`, `smooth_sigma`, `dominates_beta`, `open_neighbourhood` and
`transform_subset` are Step 6's output for `β = θ_Y - Θ_D - δ π^*ω` and
`σ = f̃ + B r_W²`.  The tube half is on disk
(`TubePositivityOneFlattening.exists_tube_dominatesKahlerFormOn_of_oneFlattening`),
but it is stated for a form strictly positive along `T_W`, i.e. for `β + ddᶜf̃`
with `f̃` absorbed into the form.  `exists_localGeometry_of_positiveOnOneFlattening`
moves `f̃` back into the potential, which is the shape the Step-5 structure
asks for, so that the six fields follow from ONE hypothesis:

  `PositiveOnOneFlattening W k (β + ddᶜf̃)`  for some chart-smooth `f̃`,

which is exactly what Copy-4 Step 4 (`lem:residual-nef` on `W`, a Kähler
representative `A_W` of the class `eq:AW-class`, and an extension `f̃` of its
potential) has to deliver.  That hypothesis is not addressed here.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.StepSixLocalGeometry

open Hironaka.PositiveClasses Hironaka.AnalyticGluingData
  Hironaka.GlobalPotentialTransforms ManifoldTubePositivity TubePositivityOneFlattening

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Moving a smooth function from the form into the potential**, over a set:
if `η = θ - ddᶜf` coefficientwise and `u` is `θ`-PSH over `Ω`, then `f + u` is
`η`-PSH over `Ω`. -/
theorem thetaPlurisubharmonicOn_coe_add {θ η : SmoothRealForm n M 2} {f : M → ℝ}
    (hf : ChartSmooth (n := n) f)
    (hθη : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      η.coeff e z = θ.coeff e z + smoothDDC (fun y => -f (e.val.symm y)) z)
    {u : M → EReal} {Ω : Set M} (hu : ThetaPlurisubharmonicOn θ u Ω) :
    ThetaPlurisubharmonicOn η (fun x => (f x : EReal) + u x) Ω := by
  have hf' : ChartSmooth (n := n) fun x => -f x := fun e => (hf e).neg
  intro e z hz hzΩ
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz hzΩ
  refine ⟨W, fun y => ρ y + -f (e.val.symm y), hzW,
    isSmoothLocalPotential_add_chartSmooth hf' hθη hρ, ?_⟩
  have heq : (fun y => chartFunction (fun x => (f x : EReal) + u x) e y +
      ((ρ y + -f (e.val.symm y) : ℝ) : EReal)) =
      (fun y => chartFunction u e y + (ρ y : EReal)) := by
    funext y
    simp only [chartFunction]
    induction u (e.val.symm y) using EReal.rec with
    | bot => simp
    | top => simp
    | coe r =>
        rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
        congr 1
        ring
  rw [heq]
  exact hp

/-- **Step 6, local geometry.**  If `β + ddᶜf̃` is strictly positive along the
tangent directions of the compact regular `W` (through one flattening at each
point), then there are an open `U ⊇ W` and a chart-smooth `σ` (namely
`f̃ + B r_W²`) with `β + ddᶜσ` dominating a Kähler form on `U`. -/
theorem exists_localGeometry_of_positiveOnOneFlattening [CompactSpace M]
    (omega : KahlerBackground n M) {W : Set M} {k : ℕ} (hWclosed : IsClosed W)
    (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k) (β : ClosedRealOneOneForm n M)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hpos : PositiveOnOneFlattening W k (β + ddcClosedForm f hf)) :
    ∃ (U : Set M) (σ : M → ℝ), IsOpen U ∧ W ⊆ U ∧ ChartSmooth (n := n) σ ∧
      DominatesKahlerFormOn β (fun x => (σ x : EReal)) U := by
  obtain ⟨r, hr, -, -, B, -, U, hU, hWU, ω', hdom⟩ :=
    exists_tube_dominatesKahlerFormOn_of_oneFlattening omega hWclosed hWreg _ hpos
  refine ⟨U, fun x => f x + B * r x, hU, hWU, fun e => (hf e).add ((hr e).const_smul B),
    ω', ?_, ?_⟩
  · have h := thetaPlurisubharmonicOn_coe_add (θ := (β + ddcClosedForm f hf - ω'.form).val)
      (η := (β - ω'.form).val) hf ?_ hdom.1
    · refine fun e z hz hzU => ?_
      obtain ⟨W', ρ, hzW', hρ, hp⟩ := h e z hz hzU
      refine ⟨W', ρ, hzW', hρ, ?_⟩
      convert hp using 2 with y
      simp only [chartFunction, EReal.coe_add]
    · intro e z hz
      have hneg : smoothDDC (fun y => -f (e.val.symm y)) z
          = -smoothDDC (fun y => f (e.val.symm y)) z := by
        have := smoothDDC_smul e.val.open_target (hf e) (-1) hz
        have hfun : (fun y => -f (e.val.symm y)) = (fun y => (-1 : ℝ) • f (e.val.symm y)) := by
          funext y
          simp
        rw [hfun, this]
        ext v
        simp
      rw [hneg, BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub,
        ClosedRealOneOneForm.coeff_add]
      simp only [ddcClosedForm, SmoothDDCForm.ddcForm_coeff]
      abel
  · intro x hx V hV hxV
    exact ⟨x, hxV, EReal.coe_ne_bot _⟩

end

end Hironaka.StepSixLocalGeometry
