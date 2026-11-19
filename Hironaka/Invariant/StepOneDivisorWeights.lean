import Hironaka.Analytic.StepFiveAssemblyOfStepOneStepFour

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1's divisors as the weights the Step-5 assembly takes

Source: Copy-4, `prop:principalization`, Steps 1--2
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1600-1660,
1800-1846`): relative principalization produces **effective divisors** on `Y` and ideal
identities,

* `𝔅_M 𝒪_Y = 𝒪_Y(-G̃_M)`,
* `𝓘_V 𝒪_Y = 𝒪_Y(-H) · 𝓘_W` with `H = H^fix_m + P^mov + P^F` (`eq:IV-H`),
* `𝔅_m 𝒪_Y = 𝒪_Y(-G̃_m)` with `G̃_m ≥ H^fix_m` (`eq:def-Gm-tilde`), i.e.
  `𝔅_m 𝒪_Y ⊆ 𝒪_Y(-H^fix_m)`.

`StepFiveAssemblyOfStepOneStepFour.exists_polarBranch_stepFiveData_of_stepOne_stepFour`
takes Step 1 as **weights** of metered divisors.  `exists_stepOneWeights_of_divisors` is the
adapter: it equips the four divisors with smooth metrics (`DivisorMetric.exists_divisorMetric`)
and proves the three weight hypotheses `hGM`, `hH`, `hHfix` of the assembly from the ideal
identities above (`hfact` is the second identity itself).  `stepOneWeights_of_isDivisorMetric`
proves the same three relations for any given metrics.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepOneDivisorWeights

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  DivisorMetric StepFiveDivisorWeights IdealWeightComparison
  AmbientIdealSourcesOfCoherentIdeals

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Step 1's weight relations, for any smooth metrics on Step 1's divisors.**  From the
ideal identities `𝔅_M 𝒪_Y = 𝒪_Y(-G̃_M)` and `𝔅_m 𝒪_Y ⊆ 𝒪_Y(-H^fix_m)`, and smooth metrics
on `G̃_M, H^fix_m, P^mov, P^F` (`IsDivisorMetric`): `ψ_{G̃_M}` presents `𝔅_M 𝒪_Y`,
`ψ_{H^fix} + ψ_{P^mov} + ψ_{P^F}` presents `𝒪_Y(-H)`, and `ψ_{𝔅_m} ∘ π ≤ ψ_{H^fix} + O(1)`.
The metrics are inputs, so a Step-4 current stated relative to them can be supplied. -/
theorem stepOneWeights_of_isDivisorMetric [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {GM Hfix Pmov PF : EffectiveDivisor n Y} {EGM EHfix EPmov EPF : MeteredEffectiveQDivisor n Y}
    (hGMmet : IsDivisorMetric GM EGM) (hHfixmet : IsDivisorMetric Hfix EHfix)
    (hPmovmet : IsDivisorMetric Pmov EPmov) (hPFmet : IsDivisorMetric PF EPF)
    {𝔅M 𝔟 : GermIdeal n X} (hGMideal : GM.ideal = GermIdeal.pullback (m := n) π 𝔅M)
    {psib : X → EReal} (hb : HasAnalyticSingularitiesOfType (n := n) psib 1 𝔟)
    (hBm : (GermIdeal.pullback (m := n) π 𝔟).Le Hfix.ideal) :
    HasAnalyticSingularitiesOfType (n := n) EGM.weight 1
        (GermIdeal.pullback (m := n) π 𝔅M) ∧
      HasAnalyticSingularitiesOfType (n := n)
        (fun y => EHfix.weight y + EPmov.weight y + EPF.weight y) 1
        ((Hfix.ideal.mul Pmov.ideal).mul PF.ideal) ∧
      MoreSingularOn (fun y => psib (π y)) EHfix.weight univ := by
  -- `ψ_{𝔅_m} ∘ π` against `ψ_{H^fix}`, through a weight of the pullback ideal
  obtain ⟨psiPull, hpsiPull⟩ := exists_hasAnalyticSingularitiesOfType_coefficient
    (GermIdealPullbackCalculus.isCoherent_pullback (m := n) hπ hb.2.1) (one_pos : (0 : ℚ) < 1)
  have h1 : MoreSingularOn (psib ∘ π) psiPull univ :=
    (sameSingularityTypeOn_univ_comp_pullback hπ hb hpsiPull).1
  have h2 : MoreSingularOn psiPull EHfix.weight univ :=
    moreSingularOn_univ_of_le hpsiPull (hasAnalyticSingularitiesOfType_of_isDivisorMetric hHfixmet)
      hBm
  exact ⟨hasAnalyticSingularitiesOfType_weight_of_ideal_eq hGMmet hGMideal,
    hasAnalyticSingularitiesOfType_weight_sum_three hHfixmet hPmovmet hPFmet, h1.trans h2⟩

/-- **Step 1's divisors, metered, with the weight relations Step 5 uses.**  From the
effective divisors `G̃_M, H^fix_m, P^mov, P^F` of Copy-4 Step 1 and its ideal identities:
smooth metrics with the same supports, `ψ_{G̃_M}` presenting `𝔅_M 𝒪_Y`,
`ψ_{H^fix} + ψ_{P^mov} + ψ_{P^F}` presenting `𝒪_Y(-H)`, and
`ψ_{𝔅_m} ∘ π ≤ ψ_{H^fix} + O(1)`. -/
theorem exists_stepOneWeights_of_divisors [CompactSpace X] [CompactSpace Y] {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (GM Hfix Pmov PF : EffectiveDivisor n Y) {𝔅M 𝔟 : GermIdeal n X}
    (hGMideal : GM.ideal = GermIdeal.pullback (m := n) π 𝔅M)
    (h𝔟 : 𝔟.IsCoherent) {psib : X → EReal}
    (hb : HasAnalyticSingularitiesOfType (n := n) psib 1 𝔟)
    (hBm : (GermIdeal.pullback (m := n) π 𝔟).Le Hfix.ideal) :
    ∃ EGM EHfix EPmov EPF : MeteredEffectiveQDivisor n Y,
      EGM.support = GM.support ∧ EHfix.support = Hfix.support ∧
      EPmov.support = Pmov.support ∧ EPF.support = PF.support ∧
      HasAnalyticSingularitiesOfType (n := n) EGM.weight 1
        (GermIdeal.pullback (m := n) π 𝔅M) ∧
      HasAnalyticSingularitiesOfType (n := n)
        (fun y => EHfix.weight y + EPmov.weight y + EPF.weight y) 1
        ((Hfix.ideal.mul Pmov.ideal).mul PF.ideal) ∧
      MoreSingularOn (fun y => psib (π y)) EHfix.weight univ := by
  obtain ⟨EGM, hGMsupp, hGMmet⟩ := exists_divisorMetric GM
  obtain ⟨EHfix, hHfixsupp, hHfixmet⟩ := exists_divisorMetric Hfix
  obtain ⟨EPmov, hPmovsupp, hPmovmet⟩ := exists_divisorMetric Pmov
  obtain ⟨EPF, hPFsupp, hPFmet⟩ := exists_divisorMetric PF
  -- `ψ_{𝔅_m} ∘ π` against `ψ_{H^fix}`, through a weight of the pullback ideal
  obtain ⟨psiPull, hpsiPull⟩ := exists_hasAnalyticSingularitiesOfType_coefficient
    (GermIdealPullbackCalculus.isCoherent_pullback (m := n) hπ h𝔟) (one_pos : (0 : ℚ) < 1)
  have h1 : MoreSingularOn (psib ∘ π) psiPull univ :=
    (sameSingularityTypeOn_univ_comp_pullback hπ hb hpsiPull).1
  have h2 : MoreSingularOn psiPull EHfix.weight univ :=
    moreSingularOn_univ_of_le hpsiPull (hasAnalyticSingularitiesOfType_of_isDivisorMetric hHfixmet)
      hBm
  exact ⟨EGM, EHfix, EPmov, EPF, hGMsupp, hHfixsupp, hPmovsupp, hPFsupp,
    hasAnalyticSingularitiesOfType_weight_of_ideal_eq hGMmet hGMideal,
    hasAnalyticSingularitiesOfType_weight_sum_three hHfixmet hPmovmet hPFmet,
    h1.trans h2⟩

end

end Hironaka.StepOneDivisorWeights
