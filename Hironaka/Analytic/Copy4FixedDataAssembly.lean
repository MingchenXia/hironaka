import Hironaka.Invariant.StepOneExcessAssembly
import Hironaka.Analytic.StepFourPullbackCurrent
import Hironaka.Blowup.ExceptionalMetric

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Steps 1--4 from the data on `X` and `V` alone

Source: Copy-4, `sec:positive-current` (`sec:fixed-data`, `eq:constants`, `eq:def-K-ell`,
`lem:ideal-comparison`), `sec:ambient` (`eq:def-TM`) and `prop:principalization` Steps 1--4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1490-1906`).

`PrincipalizationStepOneInterface.ct22Copy4_exists_stepOneData` (formerly a named input and a root of
the main theorem's cone, proved since) asserts that some adapted modification carries `Copy4StepOneData`.
Every field of that structure that concerns the MODIFICATION is now proved:

* Step 1's divisors and ideal identities — `StepOneExcessAssembly.exists_stepOneModel` (three
  relative principalizations, with the excess ideal `𝔣̃_B`);
* Step 3's exceptional metric — `ExceptionalMetric.exists_exceptionalMetric`; the metrics of the
  four divisors — `DivisorMetric.exists_divisorMetric`;
* Step 4's current `φ'` — `StepFourPullbackCurrent.isKahlerCurrentPotential_stepFourCurrent`;
* Step 4's log singularities along `D|_W` — `StepFourLogSingularities.stepFourLogSingularities`.

What remains is data on `X` and on `V` only, collected here in `Copy4FixedData`: the fixed data
of `sec:fixed-data` (`Φ_R`, `𝔧`, `A_R`, `Ψ_m`, `x₀`), `U_M` (`eq:def-TM`), the constants of
`eq:constants`, the two levels (`𝔅_M ⊆ 𝔅_m^{M/m}`, subadditivity), and from `sec:positive-current`
the potential `φ_{K,ℓ}` on `V` (`eq:def-K-ell`, the quasi-equisingular approximation) with its
ideal `𝔅` (an ambient coherent `𝔅̃` with `𝔅 = 𝔅̃|_V`) and `eq:ideal-comparison`.

* `exists_copy4StepOneData_of_fixedData` — **`Copy4FixedData` and `lem:relative-principalization`
  (`hRP`) give the conclusion of `ct22Copy4_exists_stepOneData`.**  Sorry-free.

No existing statement is changed: this is a conditional producer.  It is the proved half of the
split proposed in I-0691 (a named input on `X` and `V` only); whether to restate the named input
is the human's decision.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.Copy4FixedDataAssembly

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.AnalyticGluingData
  Hironaka.BlowupSequences Hironaka.NonKahlerLocus
  PrincipalizationCopy4StepFiveCoreReduction StepFiveAssemblyOfStepOneStepFour
  SubmanifoldChartedSpace MeteredDivisorRestriction ResidualNefReduction DivisorMetric
  IdealWeightPowers RestrictedIdealWeight PrincipalizationStepOneInterface
  StepOneExcessAssembly StepFourLogSingularities ExcessIdealPrincipalization

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **The data of Copy-4 on `X` and `V`** (`sec:fixed-data`, `eq:def-TM`, `eq:constants`,
`sec:positive-current`): every field of `Copy4StepOneData` that does not mention the
modification, with `idealIV = 𝓘_V`, together with the inputs of Step 1's third stage and of
Step 4 — the levels `r, p` (`q = r + p = M/m`, `p = (C-1) r`), `𝔅_M ⊆ 𝔅_m^{r+p}`, the
quasi-equisingular ideal `𝔅̃` with `eq:ideal-comparison` on `V`, and `φ_{K,ℓ}` on `V` with
`θ|_V - δ₀ ω|_V + ddᶜφ_K ≥ 0` and the singularity type of `(C/M) ψ_𝔅̃` (`ℓ^{-1} = C/M`). -/
structure Copy4FixedData [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) where
  /-- `sec:fixed-data`: `R = θ + ddᶜΦ_R ≥ δ_R ω` and `eq:PhiR-lower`. -/
  PhiR : X → EReal
  δR : ℝ
  hPhiR : IsThetaPshPotential (θ - δR • omega.form).val PhiR
  psiIV : X → EReal
  psij : X → EReal
  idealJ : GermIdeal n X
  hIV : HasAnalyticSingularitiesOfType (n := n) psiIV 1 (vanishingIdeal (n := n) V.carrier)
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
  /-- Step 5: a point of `V` near which `Ψ` is smooth. -/
  x₀ : X
  hx₀V : x₀ ∈ V.carrier
  hΨx₀ : IsSmoothNear (n := n) Ψ x₀
  /-- The two levels: `q = r + p = M/m`, `p = (C-1) r`, and `𝔅_M ⊆ 𝔅_m^q` (subadditivity). -/
  r : ℕ
  p : ℕ
  hr : 0 < r
  hrp : ((r + p : ℕ) : ℝ) = (CQ : ℝ) * r
  hle : idealBM.Le (idealPow idealb (r + p))
  /-- The quasi-equisingular ideal `𝔅 = 𝔅̃|_V` and `eq:ideal-comparison` on `V`. -/
  idealB : GermIdeal n X
  hBcoh : idealB.IsCoherent
  hcomp : RestrictLe V.carrier (idealB.mul (idealPow idealb p)) idealBM
  hVB : ¬ V.carrier ⊆ idealB.zeroLocus
  ψB : X → EReal
  hψB : HasAnalyticSingularitiesOfType (n := n) ψB 1 idealB
  /-- `eq:def-K-ell`: `φ_{K,ℓ}` on `V`, with `δ + τ ≤ δ₀`. -/
  δ₀ : ℝ
  hδτ : δ + (τQ : ℝ) ≤ δ₀
  φK : V.carrier → EReal
  hφK : letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
    IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2)
        (θ - δ₀ • omega.form)).val φK
  hφKtype : SameSingularityTypeOn φK
    (fun v => (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) * ψB v.1) univ

/-- `V ⊄ Z(𝔅_m)`, read off the point `x₀` near which `Ψ` is smooth. -/
theorem Copy4FixedData.not_subset_zeroLocus_idealb [CompactSpace X]
    {omega : KahlerBackground n X} {θ : ClosedRealOneOneForm n X}
    {V : ClosedIrreducibleAnalyticSubvariety n X}
    {hV : IsClosedConnectedSubmanifold n V.carrier V.dim} (F : Copy4FixedData omega θ V hV) :
    ¬ V.carrier ⊆ F.idealb.zeroLocus := by
  intro hsub
  have hne : F.Ψ F.x₀ ≠ ⊥ := ne_bot_of_isSmoothNear F.hΨx₀
  apply hne
  have hZ : F.x₀ ∈ (F.idealJ.mul F.idealb).zeroLocus :=
    RestrictLeCalculus.zeroLocus_right_subset_mul F.idealJ F.idealb (hsub F.hx₀V)
  rw [← StepFourNoComponentContainsW.poleSet_eq_zeroLocus F.hΨtype] at hZ
  exact hZ

/-- **Copy-4 Steps 1--4 from the data on `X` and `V`.**  Given `lem:relative-principalization`
(`hRP`) and `Copy4FixedData`, some sequence of blowups adapted to `V`, with closed connected
smooth strict transform of dimension `dim V`, carries `Copy4StepOneData` — the conclusion of the
named input `ct22Copy4_exists_stepOneData`. -/
theorem exists_copy4StepOneData_of_fixedData (hRP : RelativePrincipalizationHolds.{u} n)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_lt : V.dim < n)
    (F : Copy4FixedData omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) := by
  classical
  obtain ⟨Y, _t, _c, _m, π, hπ, hYc, -, hW, GM, Hfix, Pmov, PF, hGM, hBm, hfact, hPmovexc,
    hPFexc, hweights⟩ :=
    exists_stepOneModel hRP V hV hdim_lt F.hb.2.1 F.hpsiBM.2.1 F.hBcoh F.hle F.hcomp
      F.not_subset_zeroLocus_idealb F.hVBM F.hVB
  have := hYc
  have hπs := hπ.isBlowupSequence
  obtain ⟨E, hEexc, hEkahler, -⟩ := ExceptionalMetric.exists_exceptionalMetric omega π hπs
  obtain ⟨EGM, -, hGMmet⟩ := exists_divisorMetric GM
  obtain ⟨EHfix, -, hHfixmet⟩ := exists_divisorMetric Hfix
  obtain ⟨EPmov, -, hPmovmet⟩ := exists_divisorMetric Pmov
  obtain ⟨EPF, -, hPFmet⟩ := exists_divisorMetric PF
  have hk := le_of_isClosedConnectedSubmanifold hW
  have hWV := mem_of_mem_strictTransform hπs.contMDiff V
  have hτR : (0 : ℝ) < (F.τQ : ℝ) := by exact_mod_cast F.hτ
  have hCR : (1 : ℝ) ≤ (F.CQ : ℝ) := by exact_mod_cast F.hC.le
  have hMR : (0 : ℝ) < (F.levQ : ℝ) := by exact_mod_cast F.hlev
  -- Step 4's current
  have hφ' := StepFourPullbackCurrent.isKahlerCurrentPotential_stepFourCurrent omega θ hk
    hV.2.2 F.hφK hπs.contMDiff E hEexc hEkahler hW.2.2 hWV hτR F.hδτ
  -- Step 4's log singularities
  have hw := hweights F.ψB F.hψB EGM EPmov EPF hGMmet hPmovmet hPFmet (F.CQ : ℝ) (F.levQ : ℝ)
    hMR hCR F.hr F.hrp
  exact ⟨Y, _t, _c, _m, π, hπ, hW, ⟨
    { E := E
      hEexc := hEexc
      hEkahler := hEkahler
      PhiR := F.PhiR
      δR := F.δR
      hPhiR := F.hPhiR
      psiIV := F.psiIV
      psij := F.psij
      idealIV := vanishingIdeal (n := n) V.carrier
      idealJ := F.idealJ
      hIV := F.hIV
      hj := F.hj
      A := F.A
      hA := F.hA
      hPhiRsrc := F.hPhiRsrc
      c₀ := F.c₀
      hc₀ := F.hc₀
      levQ := F.levQ
      UM := F.UM
      psiBM := F.psiBM
      idealBM := F.idealBM
      hpsiBM := F.hpsiBM
      hUM := F.hUM
      hUMlower := F.hUMlower
      hVBM := F.hVBM
      Ψ := F.Ψ
      psib := F.psib
      idealb := F.idealb
      cΨ := F.cΨ
      δ := F.δ
      hΨpsh := F.hΨpsh
      hΨtype := F.hΨtype
      hb := F.hb
      hlev := F.hlev
      L := F.L
      CQ := F.CQ
      τQ := F.τQ
      hL := F.hL
      hLlev := F.hLlev
      hconst := F.hconst
      hC := F.hC
      hCA := F.hCA
      hκδ := F.hκδ
      hτ := F.hτ
      hτε := F.hτε
      GM := GM
      Hfix := Hfix
      Pmov := Pmov
      PF := PF
      hGMideal := hGM
      hBm := hBm
      hfact := hfact
      hPmovexc := hPmovexc
      hPFexc := hPFexc
      EGM := EGM
      EHfix := EHfix
      EPmov := EPmov
      EPF := EPF
      hGMmet := hGMmet
      hHfixmet := hHfixmet
      hPmovmet := hPmovmet
      hPFmet := hPFmet
      x₀ := F.x₀
      hx₀V := F.hx₀V
      hΨx₀ := F.hΨx₀
      φ' := fun w => F.φK ⟨π w.1, hWV w.1 w.2⟩ + ((F.τQ : ℝ) : EReal) * E.weight w.1
      hφ' := hφ'
      hlog := stepFourLogSingularities hW hWV F.hlev F.hC.le F.hτ.le F.hφKtype EGM EPmov EPF E
        hw _ }⟩⟩

end

end Hironaka.Copy4FixedDataAssembly
