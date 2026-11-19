import Hironaka.Analytic.MeteredDivisorScaling
import Hironaka.Analytic.InvertibleIdealCoherent
import Hironaka.Analytic.IdealPowers

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `eq:def-DLY` for the divisors the modification actually delivers

Source: Copy-4, `prop:principalization` Steps 2--5
(`transcendental-nakamaye-copy4-20260911`,
`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1845-1984`),
in particular

  `H = H^{fix}_m + P^{mov} + P^F`,
  `D = (1/M) G̃_M + ((C-1)/M) P^{mov} + (C/M) P^F + τ E_{rel}`  (`eq:def-DLY`),

and Step 5's list of bounded weights; blueprint `ana:principalization-data`.

## The gap this closes

`Pending/MeteredDivisorScaling` records `eq:def-DLY` as `qcomb4` and observes
that the hypotheses `hD`, `hH` of
`CollarWeightComparison.moreSingularOn_exceptionalWeightSum` then hold *on the
nose*, and that `exists_forall_weight_le` discharges its five boundedness
hypotheses.  What was missing — and is exactly the first finding of `I-0396`
(open since 24 Sep) — is a theorem connecting `qcomb4` to the divisors the
modification hands back: `G̃_M`, `P^{mov}`, `P^F`, `E_{rel}`, `H^{fix}_m` are
`EffectiveDivisor`s (that is what
`RelativePrincipalization.exists_relativePrincipalization` produces:
`Pending/RelativePrincipalization.lean:259`), never
`MeteredEffectiveQDivisor`s, and no declaration turned the first into the
second.

`DivisorMetric.exists_divisorMetric` is the missing link: on a compact manifold
every effective divisor carries a smooth metric.  `exists_stepFiveDivisorWeights`
runs it on the five divisors at once and reads off, from one coherent choice of
metrics, the Step-5 fields that are about *weights*:

| field of `Copy4StepFiveExceptionalWeightData` | supplied as |
|---|---|
| `divisor_split` | `rfl` (`qcomb4 = add Dres (smul τ E_rel)`) |
| `divisor_weight` | exact equality of weights, no `O(1)` |
| `H_weight` | `rfl` (`ψ_H` *is* `ψ_{H^fix} + ψ_{P^mov} + ψ_{P^F}`) |
| `bound_GM`, `bound_Hfix`, `bound_Pmov`, `bound_PF` | quasi-psh + compactness |

The coefficients are rational because `MeteredEffectiveQDivisor` is a
`ℚ`-divisor: `τ` too.  The source calls `E_rel` an effective `ℚ`-divisor, so
this is faithful rather than a restriction, but it is a real constraint on any
caller and is stated as one.

## What this does NOT do

It does not produce a `Copy4StepFiveExceptionalWeightData`.  Of the divisor
side, what is left after this module is exactly the part that is not about
weights: the local geometry `y, U, β, σ` with `dominates_beta`, the positivity
`positive_correction` of `ρ = ψ_D + χ` as a `(θ - β)`-psh potential on `U`,
`smooth_rho_at_y`, `correction_eq`, `correction_weight` (which needs `χ` itself,
i.e. `eq:def-Psi`), and `polar_split`, i.e. Copy-4's construction of `φ_G`.
Those are Step 6 and `sec:positive-current`, not Step 5's weight bookkeeping.
The curvature identity is exported here precisely because `positive_correction`
will consume `Θ_D = Θ_{D_res} + τ Θ_{E_rel}`.

Everything here is sorry-free; `exists_divisorMetric` and
`exists_forall_weight_le`, the two ingredients that carry any content, are
themselves sorry-free.
-/

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepFiveDivisorWeights

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
open Hironaka.DivisorMetric
open Hironaka.IdealWeightPowers
open Hironaka.MeteredDivisorOperations
open Hironaka.MeteredDivisorScaling

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-! ### The divisor weight presents the ideal it is a metric for -/

/-- **`ψ_D` presents any ideal equal to `𝒪(-D)`.**  A restatement of
`DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric` along an ideal
identity; it is the shape in which the *divisor* side feeds the *ambient* side,
whose `AmbientGMLowerSource` asks for a presentation of the pullback ideal at
coefficient `1`. -/
theorem hasAnalyticSingularitiesOfType_weight_of_ideal_eq [CompactSpace Y]
    {D : EffectiveDivisor n Y} {E : MeteredEffectiveQDivisor n Y}
    (hE : IsDivisorMetric D E) {𝔞 : GermIdeal n Y} (h𝔞 : D.ideal = 𝔞) :
    HasAnalyticSingularitiesOfType (n := n) E.weight 1 𝔞 :=
  h𝔞 ▸ hasAnalyticSingularitiesOfType_of_isDivisorMetric hE

/-- **`ψ_H = ψ_{H^fix} + ψ_{P^mov} + ψ_{P^F}` presents `𝒪(-H)`.**  Copy-4 writes
`H = H^{fix}_m + P^{mov} + P^F`, so the ideal of `H` is the product of the three
ideals; the sum of the three divisor weights presents that product at
coefficient `1`, by `IdealWeightPowers.hasAnalyticSingularitiesOfType_mul`
applied twice.  The left-associated sum is the one Step 5 writes. -/
theorem hasAnalyticSingularitiesOfType_weight_sum_three [CompactSpace Y]
    {Hfix Pmov PF : EffectiveDivisor n Y}
    {EHfix EPmov EPF : MeteredEffectiveQDivisor n Y}
    (hHfix : IsDivisorMetric Hfix EHfix) (hPmov : IsDivisorMetric Pmov EPmov)
    (hPF : IsDivisorMetric PF EPF) :
    HasAnalyticSingularitiesOfType (n := n)
      (fun y => EHfix.weight y + EPmov.weight y + EPF.weight y) 1
      ((Hfix.ideal.mul Pmov.ideal).mul PF.ideal) :=
  hasAnalyticSingularitiesOfType_mul
    (hasAnalyticSingularitiesOfType_mul
      (hasAnalyticSingularitiesOfType_of_isDivisorMetric hHfix)
      (hasAnalyticSingularitiesOfType_of_isDivisorMetric hPmov))
    (hasAnalyticSingularitiesOfType_of_isDivisorMetric hPF)

/-! ### `eq:def-DLY` from five effective divisors -/

/-- **The weight side of Copy-4 Step 5, from the divisors the modification
delivers.**  Five effective divisors on a compact `Y` and the rational Step-5
coefficients produce smooth metrics, the divisor `D` of `eq:def-DLY`, its
residual part `D_res = D - τ E_rel`, the divisor `H = H^fix + P^mov + P^F`, and
the five Step-5 fields listed in the module docstring.

`divisor_split`, `divisor_weight` and `H_weight` come out as *exact* weight
identities — no `O(1)` is spent — because `weight_add`, `weight_smul` and
`weight_qcomb4` are definitional for divisors built this way.  The curvature
identity `Θ_D = Θ_{D_res} + τ Θ_{E_rel}` is exported for
`positive_correction`, which is not proved here. -/
theorem exists_stepFiveDivisorWeights [CompactSpace Y]
    (GM Hfix Pmov PF Erel : EffectiveDivisor n Y)
    {levQ CQ tauQ : ℚ} (hlevQ : 0 < levQ) (hCQ : 1 ≤ CQ) (htauQ : 0 ≤ tauQ) :
    ∃ (EGM EHfix EPmov EPF EErel Dres D : MeteredEffectiveQDivisor n Y)
      (KGM KHfix KPmov KPF : ℝ),
      IsDivisorMetric GM EGM ∧ IsDivisorMetric Hfix EHfix ∧
      IsDivisorMetric Pmov EPmov ∧ IsDivisorMetric PF EPF ∧
      IsDivisorMetric Erel EErel ∧
      EGM.support = GM.support ∧ EHfix.support = Hfix.support ∧
      EPmov.support = Pmov.support ∧ EPF.support = PF.support ∧
      EErel.support = Erel.support ∧
      D.curvature = Dres.curvature + ((tauQ : ℝ)) • EErel.curvature ∧
      (∀ x, D.weight x = Dres.weight x
        + (((tauQ : ℝ)) : EReal) * EErel.weight x) ∧
      MoreSingularOn Dres.weight
        (fun x => ((1 / (levQ : ℝ) : ℝ) : EReal) * EGM.weight x
          + ((((CQ : ℝ) - 1) / (levQ : ℝ) : ℝ) : EReal) * EPmov.weight x
          + (((CQ : ℝ) / (levQ : ℝ) : ℝ) : EReal) * EPF.weight x) univ ∧
      MoreSingularOn
        (fun x => EHfix.weight x + EPmov.weight x + EPF.weight x)
        (add (add EHfix EPmov) EPF).weight univ ∧
      (∀ x, EGM.weight x ≤ (KGM : EReal)) ∧
      (∀ x, EHfix.weight x ≤ (KHfix : EReal)) ∧
      (∀ x, EPmov.weight x ≤ (KPmov : EReal)) ∧
      (∀ x, EPF.weight x ≤ (KPF : EReal)) := by
  obtain ⟨EGM, hGMsupp, hGMmet⟩ := exists_divisorMetric GM
  obtain ⟨EHfix, hHfixsupp, hHfixmet⟩ := exists_divisorMetric Hfix
  obtain ⟨EPmov, hPmovsupp, hPmovmet⟩ := exists_divisorMetric Pmov
  obtain ⟨EPF, hPFsupp, hPFmet⟩ := exists_divisorMetric PF
  obtain ⟨EErel, hErelsupp, hErelmet⟩ := exists_divisorMetric Erel
  obtain ⟨KGM, hKGM⟩ := exists_forall_weight_le EGM
  obtain ⟨KHfix, hKHfix⟩ := exists_forall_weight_le EHfix
  obtain ⟨KPmov, hKPmov⟩ := exists_forall_weight_le EPmov
  obtain ⟨KPF, hKPF⟩ := exists_forall_weight_le EPF
  have h₁ : (0 : ℚ) ≤ 1 / levQ := div_nonneg zero_le_one hlevQ.le
  have h₂ : (0 : ℚ) ≤ (CQ - 1) / levQ := div_nonneg (by linarith) hlevQ.le
  have h₃ : (0 : ℚ) ≤ CQ / levQ := div_nonneg (by linarith) hlevQ.le
  have e₁ : ((1 / levQ : ℚ) : ℝ) = 1 / (levQ : ℝ) := by push_cast; ring
  have e₂ : (((CQ - 1) / levQ : ℚ) : ℝ) = ((CQ : ℝ) - 1) / (levQ : ℝ) := by
    push_cast; ring
  have e₃ : ((CQ / levQ : ℚ) : ℝ) = (CQ : ℝ) / (levQ : ℝ) := by push_cast; ring
  refine ⟨EGM, EHfix, EPmov, EPF, EErel,
    add (add (smul h₁ EGM) (smul h₂ EPmov)) (smul h₃ EPF),
    qcomb4 n Y h₁ h₂ h₃ htauQ EGM EPmov EPF EErel,
    KGM, KHfix, KPmov, KPF,
    hGMmet, hHfixmet, hPmovmet, hPFmet, hErelmet,
    hGMsupp, hHfixsupp, hPmovsupp, hPFsupp, hErelsupp,
    rfl, fun _ => rfl, ?_, MoreSingularOn.of_le fun _ _ => le_rfl,
    hKGM, hKHfix, hKPmov, hKPF⟩
  refine MoreSingularOn.of_le fun x _ => le_of_eq ?_
  simp only [weight_add, weight_smul, e₁, e₂, e₃]

end

end Hironaka.StepFiveDivisorWeights
