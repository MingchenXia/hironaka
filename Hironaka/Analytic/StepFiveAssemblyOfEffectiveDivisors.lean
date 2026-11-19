import Hironaka.Analytic.StepSixGenericPoint
import Hironaka.Invariant.StepOneDivisorWeights

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Steps 3--6 from Step 1's effective divisors

Source: Copy-4, `prop:principalization`, Steps 1--6
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1760-1992`).

Copy-4 Step 1 produces, by three relative principalizations, a sequence of blowups
`π : Y → X` with strict transform `W` of `V` and **effective divisors** `G̃_M, H^fix_m, P^mov,
P^F` on `Y` with the ideal identities

* `𝔅_M 𝒪_Y = 𝒪_Y(-G̃_M)`,
* `𝔅_m 𝒪_Y ⊆ 𝒪_Y(-H^fix_m)` (from `eq:def-Gm-tilde`, `G̃_m ≥ H^fix_m`),
* `𝓘_V 𝒪_Y = 𝒪_Y(-H) · 𝓘_W` with `H = H^fix_m + P^mov + P^F` (`eq:IV-H`).

`exists_polarBranch_stepFiveData_of_effectiveDivisors` takes Step 1 in exactly that form,
together with smooth metrics on the four divisors (any metrics: `IsDivisorMetric`; they exist
by `DivisorMetric.exists_divisorMetric`) and Copy-4 Step 4's current `φ'` on `W`, which has log
singularities along `D|_W` for the metric of `D` built from them.  It composes

* `StepOneDivisorWeights.stepOneWeights_of_isDivisorMetric` (the three weight relations of
  Step 5, sorry-free), and
* `StepSixGenericPoint.exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent_strictTransform`
  (Steps 3--6 with the point `y` derived; roots: `lem:residual-nef`'s two named inputs).

What stays a hypothesis is what Copy-4 builds in `sec:positive-current` and Step 1 (the ideals
`𝔅_M, 𝔅_m`, the divisors and `φ'` all come from the quasi-equisingular approximation, which
waits) and the named analytic inputs listed on the hypotheses.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepFiveAssemblyOfEffectiveDivisors

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.AnalyticGluingData
  Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  PrincipalizationCopy4StepFiveCoreReduction StepFiveAssemblyOfStepOneStepFour
  SubmanifoldChartedSpace MeteredDivisorRestriction ResidualNefReduction
  ManifoldTubePositivity TubePositivityOneFlattening DivisorMetric

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Copy-4 Steps 3--6 from Step 1's effective divisors and the Step-4 current.**  The
hypotheses up to the constants are those of
`StepSixGenericPoint.exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent_strictTransform`;
Step 1 enters as effective divisors with Copy-4's ideal identities and smooth metrics on them,
and `φ'` has log singularities along `D|_W` for the `D` of `eq:def-DLY` built from those
metrics. -/
theorem exists_polarBranch_stepFiveData_of_effectiveDivisors
    [CompactSpace X] [CompactSpace Y] [ConnectedSpace Y]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    {π : Y → X} (hπ : IsBlowupSequence n X Y π)
    (V : ClosedIrreducibleAnalyticSubvariety n X) {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) k)
    -- Step 3: the exceptional metric
    (E : MeteredEffectiveQDivisor n Y) (hEexc : E.support ⊆ exceptionalLocus n π)
    (hEkahler :
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler)
    -- `sec:fixed-data`: `R = θ + ddᶜΦ_R ≥ δ_R ω` and `eq:PhiR-lower`
    {PhiR : X → EReal} {δR : ℝ}
    (hPhiR : IsThetaPshPotential (θ - δR • omega.form).val PhiR)
    {psiIV psij : X → EReal} {idealIV 𝔧 : GermIdeal n X}
    (hIV : HasAnalyticSingularitiesOfType (n := n) psiIV 1 idealIV)
    (hj : HasAnalyticSingularitiesOfType (n := n) psij 1 𝔧)
    {A : ℝ} (hA : 0 ≤ A) (hPhiRsrc : AmbientPhiRLowerSource n X A PhiR psiIV psij)
    -- `eq:def-TM`: `lem:regularization` at the level `M`
    {c₀ : ℝ} (hc₀ : 0 ≤ c₀) {levQ : ℚ} {UM psiBM : X → EReal} {𝔅M : GermIdeal n X}
    (hpsiBM : HasAnalyticSingularitiesOfType (n := n) psiBM 1 𝔅M)
    (hUM : IsThetaPshPotential (θ + (c₀ / (levQ : ℝ)) • omega.form).val UM)
    (hUMlower : MoreSingularOn (fun x => ((1 / (levQ : ℝ) : ℝ) : EReal) * psiBM x) UM univ)
    -- `eq:def-Psi`: the ideal function of `𝔧 𝔅_m`
    {Ψ psib : X → EReal} {𝔟 : GermIdeal n X} {cΨ δ : ℝ}
    (hΨpsh : ThetaPlurisubharmonic (cΨ • omega.form).val Ψ)
    (hΨtype : HasAnalyticSingularitiesOfType (n := n) Ψ 1 (𝔧.mul 𝔟))
    (hb : HasAnalyticSingularitiesOfType (n := n) psib 1 𝔟)
    -- the constants
    (hlev : 0 < levQ) {L : ℝ} {CQ τQ : ℚ} (hL : 0 < L) (hLlev : L < (levQ : ℝ))
    (hconst : c₀ < L * δR)
    (hC : 1 < CQ) (hCA : L * A ≤ (CQ : ℝ) - 1)
    (hκδ : ((CQ : ℝ) - 1) / (levQ : ℝ) * cΨ ≤ δ)
    (hτ : 0 < τQ) (hτε : (τQ : ℝ) ≤ (L * δR - c₀) / (levQ : ℝ))
    -- Step 1: effective divisors and the ideal identities
    (GM Hfix Pmov PF : EffectiveDivisor n Y)
    (hGMideal : GM.ideal = GermIdeal.pullback (m := n) π 𝔅M)
    (hBm : (GermIdeal.pullback (m := n) π 𝔟).Le Hfix.ideal)
    (hfact : GermIdeal.pullback (m := n) π idealIV =
      ((Hfix.ideal.mul Pmov.ideal).mul PF.ideal).mul
        (vanishingIdeal (n := n) (strictTransform n π V.carrier)))
    -- smooth metrics on them
    (EGM EHfix EPmov EPF : MeteredEffectiveQDivisor n Y)
    (hGMmet : IsDivisorMetric GM EGM) (hHfixmet : IsDivisorMetric Hfix EHfix)
    (hPmovmet : IsDivisorMetric Pmov EPmov) (hPFmet : IsDivisorMetric PF EPF)
    -- a point of `V` near which `Ψ` is smooth (Copy-4 Step 5)
    {x₀ : X} (hx₀V : x₀ ∈ V.carrier) (hΨx₀ : IsSmoothNear (n := n) Ψ x₀)
    -- Step 4's current on `W`, with its complex structure from the flattenings
    : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
      haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
      ∀ (hnd : ∀ O : Set (strictTransform n π V.carrier), IsOpen O → O.Nonempty →
          ∃ p ∈ O, (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).weight (p : Y) ≠ ⊥)
        {φ' : strictTransform n π V.carrier → EReal},
        IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback
          (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
          (ClosedRealOneOneForm.pullback hπ.contMDiff θ
            - δ • ClosedRealOneOneForm.pullback hπ.contMDiff omega.form)) φ' →
        HasLogSingularitiesAlong
          (restrictAlong k (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
            (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E) hnd) φ' →
        ∃ φG : Y → EReal,
          IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ) φG ∧
          Nonempty (Copy4StepFiveExceptionalWeightData
            (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
            (strictTransform n π V.carrier) φG) := by
  obtain ⟨hGM, hH, hHfix⟩ := StepOneDivisorWeights.stepOneWeights_of_isDivisorMetric
    hπ.contMDiff hGMmet hHfixmet hPmovmet hPFmet hGMideal hb hBm
  exact StepSixGenericPoint.exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent_strictTransform
    omega θ hπ V hW E hEexc hEkahler hPhiR hIV hj hA hPhiRsrc hc₀ hpsiBM hUM hUMlower hΨpsh
    hΨtype hb hlev hL hLlev hconst hC hCA hκδ hτ hτε EGM EHfix EPmov EPF hGM hH hfact hHfix
    hx₀V hΨx₀

end

end Hironaka.StepFiveAssemblyOfEffectiveDivisors
