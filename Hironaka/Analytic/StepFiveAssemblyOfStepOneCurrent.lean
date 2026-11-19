import Hironaka.Analytic.StepFiveAssemblyOfStepOneStepFour
import Hironaka.Analytic.MeteredDivisorRestriction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Steps 3--6 from Step 1 and the Step-4 current on `W`

Source: Copy-4, `prop:principalization`, Steps 3--6
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1845-1984`).

`StepFiveAssemblyOfStepOneStepFour.exists_polarBranch_stepFiveData_of_stepOne_stepFour`
takes Step 4 as the positivity statement `PositiveOnOneFlattening W k (β + ddᶜf̃)`.  Here
that hypothesis is replaced by what Copy-4 Step 4 actually starts from, and Step 4 is
carried out by `MeteredDivisorRestriction.exists_positiveOnOneFlattening_of_restrictedDivisor`
(`lem:residual-nef` on `W`, the restriction calculus, the smooth extension lemma):

* `D = copy4Divisor ...` (`eq:def-DLY`) has no component containing `W`, in weight form;
* `φ'` is a Kähler-current potential **on `W`** (with the flattening complex structure) of
  `θ' = (θ_Y - δ π^*ω)|_W`, with log singularities along `D|_W` with the restricted metric.

In Copy-4, `φ' = (π|_W)^*φ_{K,ℓ} + τ ψ_{E_rel}|_W`, built in `sec:positive-current` from the
quasi-equisingular approximation `φ_{K,ℓ}` (QEA waits), so it stays a hypothesis, together with
the Step-1 data.  The theorem therefore says: **for a given `π`, the Step-5 interface's
conclusion follows from the Step-1 data and the Step-4 current**, modulo
`lem:residual-nef`'s two named inputs (Demailly CADG I.5.24 and the one Demailly-1992 input).
The interface's statement is unchanged and it is not discharged (`I-0608`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepFiveAssemblyOfStepOneCurrent

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.AnalyticGluingData
  Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  PrincipalizationCopy4StepFiveCoreReduction StepFiveAssemblyOfStepOneStepFour
  SubmanifoldChartedSpace MeteredDivisorRestriction ResidualNefReduction
  ManifoldTubePositivity TubePositivityOneFlattening

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Copy-4 Steps 3--6 from the Step-1 data and the Step-4 current on `W`.**  The
hypotheses up to the point `y` are those of
`StepFiveAssemblyOfStepOneStepFour.exists_polarBranch_stepFiveData_of_stepOne_stepFour`; Step 4's
positivity is replaced by its source-level input, see the module docstring. -/
theorem exists_polarBranch_stepFiveData_of_stepOne_stepFourCurrent
    [CompactSpace X] [CompactSpace Y] [ConnectedSpace Y]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    {π : Y → X} (hπ : IsBlowupSequence n X Y π)
    {W : Set Y} {k : ℕ} (hW : IsClosedConnectedSubmanifold n W k)
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
    -- Step 1, as weights
    (EGM EHfix EPmov EPF : MeteredEffectiveQDivisor n Y)
    (hGM : HasAnalyticSingularitiesOfType (n := n) EGM.weight 1
      (GermIdeal.pullback (m := n) π 𝔅M))
    {idealH : GermIdeal n Y}
    (hH : HasAnalyticSingularitiesOfType (n := n)
      (fun y => EHfix.weight y + EPmov.weight y + EPF.weight y) 1 idealH)
    (hfact : GermIdeal.pullback (m := n) π idealIV = idealH.mul (vanishingIdeal (n := n) W))
    (hHfix : MoreSingularOn (fun y => psib (π y)) EHfix.weight univ)
    -- the point `y`
    {y : Y} (hyW : y ∈ W) (hyGM : y ∉ EGM.support) (hyPmov : y ∉ EPmov.support)
    (hyPF : y ∉ EPF.support) (hyexc : y ∉ exceptionalLocus n π)
    (hΨy : IsSmoothNear (n := n) Ψ (π y))
    -- Step 4's current on `W`, with its complex structure from the flattenings
    : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
      haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
      ∀ (hnd : ∀ O : Set W, IsOpen O → O.Nonempty →
          ∃ p ∈ O, (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E).weight (p : Y) ≠ ⊥)
        {φ' : W → EReal},
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
            (ClosedRealOneOneForm.pullback hπ.contMDiff θ) W φG) := by
  have hk := le_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  intro hnd φ' hφ' hlog
  obtain ⟨f, hf, hpos⟩ := exists_positiveOnOneFlattening_of_restrictedDivisor hW
    (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
    (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form) δ
    (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E) hnd hφ' hlog
  exact exists_polarBranch_stepFiveData_of_stepOne_stepFour omega θ hπ hW E hEexc hEkahler
    hPhiR hIV hj hA hPhiRsrc hc₀ hpsiBM hUM hUMlower hΨpsh hΨtype hb hlev hL hLlev hconst
    hC hCA hκδ hτ hτε EGM EHfix EPmov EPF hGM hH hfact hHfix hyW hyGM hyPmov hyPF hyexc hΨy
    hf hpos

end

end Hironaka.StepFiveAssemblyOfStepOneCurrent
