import Hironaka.Analytic.AmbientConvexCurrent
import Hironaka.Blowup.ExceptionalMetric
import Hironaka.Analytic.MeteredDivisorPositivity
import Hironaka.Analytic.GlobalPotentialPullback
import Hironaka.Blowup.BlowupSequenceTotalTransform
import Hironaka.Blowup.BlowupBigPullback
import Hironaka.Blowup.BlowupPushforward
import Hironaka.Analytic.PotentialTheory.LocalPotentials

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 3: the global polar branch `φ_G`

Source: Copy-4, `prop:principalization`, Step 3
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1848-1867`):

> Apply `lem:exceptional-metric` to `π` and `ω`: there is an effective
> `π`-exceptional `ℚ`-divisor `E_rel`, with a smooth metric, such that
> `ω_Y := π^*ω - Θ_{E_rel}` is a Kähler form on `Y`. [...] Fix a rational number
> `τ` with `0 < τ < min{ε₀, δ₀/2}`, and set `φ_G := φ_{Q_M} ∘ π + τ ψ_{E_rel}`.
> By `eq:QM-positivity`,
> `θ_Y + ddᶜφ_G = π^*Q_M + τ([E_rel] - Θ_{E_rel}) ≥ (ε₀ - τ) π^*ω + τ ω_Y ≥ τ ω_Y`,
> so `θ_Y + ddᶜφ_G` is a Kähler current.

## Why this module exists

`TN.3.4.DIVISORSIDE`: of the fields of
`PrincipalizationCopy4StepFiveCoreReduction.Copy4StepFiveExceptionalWeightData`,
`polar_split` (`φ_G = φ_{Q,π} + τ ψ_E`) had no producer, and neither had the
`IsKahlerCurrentPotential θ_Y φ_G` conjunct of the faithful Step-5 interface
`PrincipalizationPolarBranchStepFive.ct22Copy4_exists_polarBranch_copy4StepFiveExceptionalWeightData`.
Both are Copy-4's construction of `φ_G`, which is Step 3, and Step 3 needs no
input beyond what the project already proves:

* `eq:QM-positivity` — `AmbientConvexCurrent.isThetaPshPotential_ambient`;
* pullback of a `θ`-PSH function along a holomorphic map —
  `GlobalPotentialPullback.thetaPlurisubharmonic_comp`;
* `lem:exceptional-metric` — `ExceptionalMetric.exists_exceptionalMetric`
  (sorry-free);
* `[E] ≥ 0`, i.e. `ψ_E` is `Θ_E`-PSH — `MeteredDivisorPositivity.thetaPlurisubharmonic_weight`.

What is added here is the arithmetic of the forms
(`π^*θ - τ ω_Y = π^*(θ - εω) + τ Θ_E + (ε - τ) π^*ω`) and local nondegeneracy of
`φ_G` (an exceptional point has no neighbourhood inside the exceptional locus;
off it `π` is a local homeomorphism and `ψ_E` is finite).

The construction is **generic in the blowup sequence `π`**: nothing about the
three-stage modification of Copy-4 Step 1 is used, only `IsBlowupSequence`.

## What is and is not claimed

The inputs `U_M` (`T_M ≥ -(c₀/M)ω`, from `lem:regularization`) and `Φ_R`
(`R ≥ δ_R ω`, from Boucksom 3.17 / Demailly 2.6) are **hypotheses** here; this
module neither names nor proves them.  The constants enter exactly as in
`eq:constants`: `c₀ < L δ_R`, `L < M` (written `lev`), `0 < τ ≤ ε₀`.  Copy-4 asks
`τ < min{ε₀, δ₀/2}`; the `δ₀/2` part is used only in Step 4, so only `τ ≤ ε₀` is
assumed, which makes the statement stronger, not weaker.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.PolarBranchStepThree

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka.AnalyticGluingData
  Hironaka.NumericalRestrictedVolumeScaffold
  ThetaPshConvexCombination AmbientConvexCurrent

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Local nondegeneracy of `φ ∘ π + τ ψ`.**  If `φ` is locally nondegenerate on
`X`, `π` is a blowup sequence and `ψ` is finite off the exceptional locus, then
`φ ∘ π + τ ψ` is locally nondegenerate on `Y`.  Every open set of `Y` meets the
complement of the exceptional locus (whose interior is empty), and there `π` maps
neighbourhoods onto neighbourhoods. -/
theorem locallyNondegenerate_comp_add_smul {π : Y → X} (hπ : IsBlowupSequence n X Y π)
    {φ : X → EReal} (hφ : LocallyNondegenerate φ) {ψ : Y → EReal}
    (hψ : ∀ y, y ∉ exceptionalLocus n π → ψ y ≠ ⊥) {τ : ℝ} (hτ : 0 < τ) :
    LocallyNondegenerate (fun y => φ (π y) + (τ : EReal) * ψ y) := by
  intro y U hU hyU
  have hint := BlowupSequenceTotalTransform.interior_exceptionalLocus_eq_empty_of_isBlowupSequence hπ
  have hnot : ¬ U ⊆ exceptionalLocus n π := fun hsub => by
    have hy := interior_maximal hsub hU hyU
    rw [hint] at hy
    exact hy
  obtain ⟨z₀, hz₀U, hz₀E⟩ := not_subset.mp hnot
  set N : Set Y := U ∩ (exceptionalLocus n π)ᶜ with hNdef
  have hN : IsOpen N :=
    hU.inter (StrictTransformComposition.isOpen_compl_exceptionalLocus hπ.contMDiff)
  have himg : π '' N ∈ 𝓝 (π z₀) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
      hπ.contMDiff hz₀E]
    exact image_mem_map (hN.mem_nhds ⟨hz₀U, hz₀E⟩)
  obtain ⟨x, hxi, hx⟩ := hφ (π z₀) _ isOpen_interior (mem_interior_iff_mem_nhds.mpr himg)
  obtain ⟨z, ⟨hzU, hzE⟩, rfl⟩ := interior_subset hxi
  refine ⟨z, hzU, EReal.add_ne_bot_iff.mpr ⟨hx, fun h => hψ z hzE ?_⟩⟩
  exact eq_bot_of_coe_mul_eq_bot hτ h

/-- Pullback commutes with `θ - ε ω`, coefficientwise. -/
theorem pullback_sub_smul_geometricallyEq {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (θ w : ClosedRealOneOneForm n X) (ε : ℝ) :
    (ClosedRealOneOneForm.pullback hπ (θ - ε • w)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hπ θ - ε • ClosedRealOneOneForm.pullback hπ w).val := by
  intro e z hz
  have h1 := BlowupBigPullback.pullback_sub_geometricallyEq hπ θ (ε • w) e hz
  have h2 := BlowupPushforward.pullback_smul_geometricallyEq hπ ε w e hz
  rw [h1, BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, h2]

/-- **Copy-4 Step 3.**  With `T_M = θ + ddᶜU ≥ -(c₀/M) ω`, `R = θ + ddᶜΦ ≥ δ_R ω`,
`c₀ < L δ_R`, `L < M`, an exceptional metric `E` (`π^*ω - Θ_E` Kähler, supported in
the exceptional locus) and `0 < τ ≤ ε₀ = (L δ_R - c₀)/M`, the function
`φ_G = φ_{Q_M} ∘ π + τ ψ_E` is a Kähler-current potential of `π^*θ`, with Kähler
lower bound `τ ω_Y`. -/
theorem isKahlerCurrentPotential_polarBranch
    (omega : KahlerBackground n X) {θ : ClosedRealOneOneForm n X} {U Φ : X → EReal}
    {c₀ δR L lev τ : ℝ} (hc₀ : 0 ≤ c₀) (hL : 0 < L) (hlev : L < lev)
    (hconst : c₀ < L * δR)
    (hU : IsThetaPshPotential (θ + (c₀ / lev) • omega.form).val U)
    (hΦ : IsThetaPshPotential (θ - δR • omega.form).val Φ)
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) (E : MeteredEffectiveQDivisor n Y)
    (hEexc : E.support ⊆ exceptionalLocus n π)
    (hEkahler :
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler)
    (hτ : 0 < τ) (hτε : τ ≤ (L * δR - c₀) / lev) :
    IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
      (fun y => convexComb (1 - L / lev) U Φ (π y) + (τ : EReal) * E.weight y) := by
  set ε : ℝ := (L * δR - c₀ + L * c₀ / lev) / lev with hεdef
  obtain ⟨hε₀ε, -, hQ⟩ := isThetaPshPotential_ambient omega hc₀ hL hlev hconst hU hΦ
  have hτε' : τ ≤ ε := hτε.trans hε₀ε
  set θY := ClosedRealOneOneForm.pullback hπ.contMDiff θ with hθY
  set ωY₀ := ClosedRealOneOneForm.pullback hπ.contMDiff omega.form with hωY₀
  -- the pulled-back ambient potential is `(θ_Y - ε π^*ω)`-PSH
  have hQπ : ThetaPlurisubharmonic (θY - ε • ωY₀).val
      (fun y => convexComb (1 - L / lev) U Φ (π y)) :=
    ((pullback_sub_smul_geometricallyEq hπ.contMDiff θ omega.form ε).thetaPlurisubharmonic_iff
      _).mp (GlobalPotentialPullback.thetaPlurisubharmonic_comp hπ.contMDiff hQ.1)
  -- `ψ_E` is `Θ_E`-PSH
  have hEpsh : ThetaPlurisubharmonic E.curvature.val E.weight :=
    MeteredDivisorPositivity.thetaPlurisubharmonic_weight E
  -- the sum
  have hsum := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul one_pos hτ hQπ hEpsh
  -- add the semipositive `(ε - τ) π^*ω`
  have hsemi : ((ε - τ) • ωY₀).val.IsSemipositive := by
    intro e z hz v
    rw [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (sub_nonneg.mpr hτε')
      (ClosedRealOneOneForm.pullback_isSemipositive hπ.contMDiff omega.isSemipositive e z hz v)
  have hall := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hsum hsemi
  -- the Kähler background `τ ω_Y`, `ω_Y = π^*ω - Θ_E`
  refine ⟨KahlerBackground.smul hτ ⟨ωY₀ - E.curvature, hEkahler⟩, ?_, ?_⟩
  · rw [KahlerBackground.smul_form]
    change ThetaPlurisubharmonic (θY - τ • (ωY₀ - E.curvature)).val _
    have hform : (1 : ℝ) • (θY - ε • ωY₀) + τ • E.curvature + (ε - τ) • ωY₀
        = θY - τ • (ωY₀ - E.curvature) := by
      module
    have hfun : (fun p => ((1 : ℝ) : EReal) * convexComb (1 - L / lev) U Φ (π p)
          + (τ : EReal) * E.weight p)
        = (fun y => convexComb (1 - L / lev) U Φ (π y) + (τ : EReal) * E.weight y) := by
      funext p
      rw [EReal.coe_one, one_mul]
    rw [← hform, ← hfun]
    exact hall
  · exact locallyNondegenerate_comp_add_smul hπ hQ.2
      (fun y hy hbot => hy (hEexc (show y ∈ E.support from hbot))) hτ

/-- **Copy-4 Step 3 with the exceptional metric produced.**  On a compact `X`,
`lem:exceptional-metric` supplies `E_rel` once for the blowup sequence; then every
`0 < τ ≤ ε₀` gives a Kähler-current potential `φ_G = φ_{Q_M} ∘ π + τ ψ_{E_rel}` of
`π^*θ`.  This is the `polar_split` / `phiQpi_def` shape of
`Copy4StepFiveExceptionalWeightData` (with `pi := π`, `psiE := E.weight`). -/
theorem exists_exceptionalMetric_isKahlerCurrentPotential_polarBranch [CompactSpace X]
    (omega : KahlerBackground n X) {θ : ClosedRealOneOneForm n X} {U Φ : X → EReal}
    {c₀ δR L lev : ℝ} (hc₀ : 0 ≤ c₀) (hL : 0 < L) (hlev : L < lev)
    (hconst : c₀ < L * δR)
    (hU : IsThetaPshPotential (θ + (c₀ / lev) • omega.form).val U)
    (hΦ : IsThetaPshPotential (θ - δR • omega.form).val Φ)
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) :
    ∃ E : MeteredEffectiveQDivisor n Y, E.support ⊆ exceptionalLocus n π ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ (L * δR - c₀) / lev →
        IsKahlerCurrentPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ)
          (fun y => convexComb (1 - L / lev) U Φ (π y) + (τ : EReal) * E.weight y) := by
  obtain ⟨E, hEexc, hEkahler, -⟩ := ExceptionalMetric.exists_exceptionalMetric omega π hπ
  exact ⟨E, hEexc, fun τ hτ hτε =>
    isKahlerCurrentPotential_polarBranch omega hc₀ hL hlev hconst hU hΦ hπ E hEexc
      hEkahler hτ hτε⟩

end

end Hironaka.PolarBranchStepThree
