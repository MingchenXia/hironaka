import Hironaka.Analytic.StepFourNoComponentContainsW
import Hironaka.Resolution.RelativePrincipalization

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 1: the data `Copy4StepOneData` and the predicate `RelativePrincipalizationHolds`

Source: Copy-4, `prop:principalization`, Steps 1--6, `sec:fixed-data` and
`sec:positive-current`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1395-1992`);
blueprint `ana:copy4-step-one-data`, `ana:relative-principalization`.

This is the base of `PrincipalizationStepOneInterface`: it contains the declarations that the
named input `PrincipalizationStepOneInterface.ct22Copy4_exists_stepOneData` is stated with, so
that the producers of its fields (`PrincipalizationStepOneStages`,
`PrincipalizationStepOneAssembly`, `StepOneExcessAssembly`, ...) can import them without
importing the interface itself.  The declarations keep their names in the namespace
`PrincipalizationStepOneInterface` (moved verbatim from `PrincipalizationStepOneInterface`, run
0110; statements unchanged):

* `Copy4StepOneData` — Copy-4 Steps 1--4 done on a given modification `π` (see the docstring of
  `PrincipalizationStepOneInterface` for the grouping of the fields);
* `Copy4StepOneData.exists_polarBranch_stepFiveData` — the proved half, Steps 3--6;
* `RelativePrincipalizationHolds` — `lem:relative-principalization` (its factorization core) on
  every compact connected complex manifold of dimension `n`;
* `relativePrincipalizationHolds` — that predicate from the Hironaka statement
  `RelativePrincipalization.exists_factorizationData` (I-0484 item 6; proved in place from the canonical resolution invariant).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.PrincipalizationStepOneInterface

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.AnalyticGluingData
  Hironaka.NonKahlerLocus Hironaka.BlowupSequences Hironaka.NumericalRestrictedVolume
  Hironaka.NumericalRestrictedVolumeScaffold
  PrincipalizationCopy4StepFiveCoreReduction StepFiveAssemblyOfStepOneStepFour
  SubmanifoldChartedSpace MeteredDivisorRestriction ResidualNefReduction
  ManifoldTubePositivity TubePositivityOneFlattening DivisorMetric
  PrincipalizationSourceDataReduction

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Copy-4 Steps 1--4 done on the modification `π`.**  The fields are the hypotheses of
`StepFourNoComponentContainsW.exists_polarBranch_stepFiveData_of_effectiveDivisors_of_exceptional`,
grouped as in the source; see the module docstring. -/
structure Copy4StepOneData [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) (V : ClosedIrreducibleAnalyticSubvariety n X) {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) k) where
  /-- Step 3: the exceptional metric of `lem:exceptional-metric`. -/
  E : MeteredEffectiveQDivisor n Y
  hEexc : E.support ⊆ exceptionalLocus n π
  hEkahler :
    (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler
  /-- `sec:fixed-data`: `R = θ + ddᶜΦ_R ≥ δ_R ω` and `eq:PhiR-lower`. -/
  PhiR : X → EReal
  δR : ℝ
  hPhiR : IsThetaPshPotential (θ - δR • omega.form).val PhiR
  psiIV : X → EReal
  psij : X → EReal
  idealIV : GermIdeal n X
  idealJ : GermIdeal n X
  hIV : HasAnalyticSingularitiesOfType (n := n) psiIV 1 idealIV
  hj : HasAnalyticSingularitiesOfType (n := n) psij 1 idealJ
  A : ℝ
  hA : 0 ≤ A
  hPhiRsrc : AmbientPhiRLowerSource n X A PhiR psiIV psij
  /-- `eq:def-TM`: `lem:regularization` at the level `M`, and `V ⊄ Z(𝔅_M)`. -/
  c₀ : ℝ
  hc₀ : 0 ≤ c₀
  levQ : ℚ
  UM : X → EReal
  psiBM : X → EReal
  idealBM : GermIdeal n X
  hpsiBM : HasAnalyticSingularitiesOfType (n := n) psiBM 1 idealBM
  hUM : IsThetaPshPotential (θ + (c₀ / (levQ : ℝ)) • omega.form).val UM
  hUMlower : MoreSingularOn (fun x => ((1 / (levQ : ℝ) : ℝ) : EReal) * psiBM x) UM univ
  hVBM : ¬ V.carrier ⊆ idealBM.zeroLocus
  /-- `eq:def-Psi`: the ideal function of `𝔧 𝔅_m`. -/
  Ψ : X → EReal
  psib : X → EReal
  idealb : GermIdeal n X
  cΨ : ℝ
  δ : ℝ
  hΨpsh : ThetaPlurisubharmonic (cΨ • omega.form).val Ψ
  hΨtype : HasAnalyticSingularitiesOfType (n := n) Ψ 1 (idealJ.mul idealb)
  hb : HasAnalyticSingularitiesOfType (n := n) psib 1 idealb
  /-- The constants of `eq:constants`. -/
  hlev : 0 < levQ
  L : ℝ
  CQ : ℚ
  τQ : ℚ
  hL : 0 < L
  hLlev : L < (levQ : ℝ)
  hconst : c₀ < L * δR
  hC : 1 < CQ
  hCA : L * A ≤ (CQ : ℝ) - 1
  hκδ : ((CQ : ℝ) - 1) / (levQ : ℝ) * cΨ ≤ δ
  hτ : 0 < τQ
  hτε : (τQ : ℝ) ≤ (L * δR - c₀) / (levQ : ℝ)
  /-- Step 1: effective divisors, the ideal identities, `P^mov`, `P^F` exceptional. -/
  GM : EffectiveDivisor n Y
  Hfix : EffectiveDivisor n Y
  Pmov : EffectiveDivisor n Y
  PF : EffectiveDivisor n Y
  hGMideal : GM.ideal = GermIdeal.pullback (m := n) π idealBM
  hBm : (GermIdeal.pullback (m := n) π idealb).Le Hfix.ideal
  hfact : GermIdeal.pullback (m := n) π idealIV =
    ((Hfix.ideal.mul Pmov.ideal).mul PF.ideal).mul
      (vanishingIdeal (n := n) (strictTransform n π V.carrier))
  hPmovexc : Pmov.support ⊆ exceptionalLocus n π
  hPFexc : PF.support ⊆ exceptionalLocus n π
  /-- Smooth metrics on the four divisors. -/
  EGM : MeteredEffectiveQDivisor n Y
  EHfix : MeteredEffectiveQDivisor n Y
  EPmov : MeteredEffectiveQDivisor n Y
  EPF : MeteredEffectiveQDivisor n Y
  hGMmet : IsDivisorMetric GM EGM
  hHfixmet : IsDivisorMetric Hfix EHfix
  hPmovmet : IsDivisorMetric Pmov EPmov
  hPFmet : IsDivisorMetric PF EPF
  /-- Step 5: a point of `V` near which `Ψ` is smooth. -/
  x₀ : X
  hx₀V : x₀ ∈ V.carrier
  hΨx₀ : IsSmoothNear (n := n) Ψ x₀
  /-- Step 4: the Kähler current `φ'` on `W` with log singularities along `D|_W`. -/
  φ' : strictTransform n π V.carrier → EReal
  hφ' : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback
      (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
      (ClosedRealOneOneForm.pullback hπ.contMDiff θ
        - δ • ClosedRealOneOneForm.pullback hπ.contMDiff omega.form)) φ'
  hlog : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    HasLogSingularitiesAlong
      (restrictAlong k (contMDiff_val (le_of_isClosedConnectedSubmanifold hW) hW.2.2)
        (copy4Divisor hlev hC.le hτ.le EGM EPmov EPF E)
        (StepFourNoComponentContainsW.copy4Divisor_noComponent_of_effectiveDivisors hπ V
          hpsiBM.2.1 hVBM hGMideal hPmovexc hPFexc hlev hC.le hτ.le hGMmet hPmovmet hPFmet
          hEexc)) φ'

/-- **The proved half: Copy-4 Steps 3--6 from Steps 1--4.**  The polar branch
`φ_G = φ_{Q_M} ∘ π + τψ_{E_rel}` is a Kähler-current potential of `π^*θ` with Step-5 data. -/
theorem Copy4StepOneData.exists_polarBranch_stepFiveData [CompactSpace X]
    {omega : KahlerBackground n X} {θ : ClosedRealOneOneForm n X} {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [CompactSpace Y] [ConnectedSpace Y] {π : Y → X} {hπ : IsBlowupSequence n X Y π}
    {V : ClosedIrreducibleAnalyticSubvariety n X} {k : ℕ}
    {hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) k}
    (D : Copy4StepOneData omega θ hπ V hW) :
    ∃ φG : Y → EReal,
      IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ) φG ∧
      Nonempty (Copy4StepFiveExceptionalWeightData
        (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
        (strictTransform n π V.carrier) φG) := by
  have hk := le_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hW.2.2
  have := isComplexManifold_chartedSpace hk hW.2.2
  exact StepFourNoComponentContainsW.exists_polarBranch_stepFiveData_of_effectiveDivisors_of_exceptional
    omega θ hπ V hW D.E D.hEexc D.hEkahler D.hPhiR D.hIV D.hj D.hA D.hPhiRsrc D.hc₀ D.hpsiBM
    D.hUM D.hUMlower D.hVBM D.hΨpsh D.hΨtype D.hb D.hlev D.hL D.hLlev D.hconst D.hC D.hCA
    D.hκδ D.hτ D.hτε D.GM D.Hfix D.Pmov D.PF D.hGMideal D.hBm D.hfact D.hPmovexc D.hPFexc
    D.EGM D.EHfix D.EPmov D.EPF D.hGMmet D.hHfixmet D.hPmovmet D.hPFmet D.hx₀V D.hΨx₀
    D.hφ' D.hlog

/-- **`lem:relative-principalization` holds** (its factorization core), for every compact
connected complex manifold of dimension `n` in the universe of `X`.  This is the statement of
the Hironaka theorem `RelativePrincipalization.exists_factorizationData`, quantified
over the manifold so that Copy-4 Step 1 can apply it on the intermediate models
`Y_fix`, `Y_1`. -/
def RelativePrincipalizationHolds (n : ℕ) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] [CompactSpace Y] [ConnectedSpace Y] (W : Set Y) (k : ℕ),
    IsClosedConnectedSubmanifold n W k → W ≠ univ → ∀ 𝔞 : GermIdeal n Y, 𝔞.IsCoherent →
      ¬ 𝔞.Le (vanishingIdeal (n := n) W) → RelativePrincipalization.FactorizationData W k 𝔞

/-- The Hironaka statement `RelativePrincipalization.exists_factorizationData`, as given (I-0484 item 6:
Step 1 USES it); it is proved in place from the canonical resolution invariant. -/
theorem relativePrincipalizationHolds (n : ℕ) : RelativePrincipalizationHolds.{u} n :=
  fun _ _ _ _ _ _ W k hW hWY 𝔞 h𝔞 hres =>
    RelativePrincipalization.exists_factorizationData W k hW hWY 𝔞 h𝔞 hres

end

end Hironaka.PrincipalizationStepOneInterface
