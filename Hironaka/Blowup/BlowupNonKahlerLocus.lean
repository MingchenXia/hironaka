import Hironaka.Blowup.BlowupBigPullback
import Hironaka.Blowup.BlowupExceptionalCentre
import Hironaka.Analytic.HolomorphicLocalInverse

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The non-Kähler locus under one blowup

Source: CT22, Lemma 4.1; Boucksom, *Divisorial Zariski decompositions*, Prop. 2.3.

Let `π : Z → Y` be the blowup of a compact Kähler manifold along a closed submanifold `C`, and let
`α = {θ}` be big.

* `lelongNumber_pos_of_dim_eq_zero`: in dimension `0` every Lelong number is positive.
* `nonKahlerLocus_pullback_subset`: `E_nK(π^* α) ⊆ π⁻¹ E_nK(α) ∪ Exc π`.  Off the exceptional
  locus, if `T ∈ α` has `ν(T, π z) = 0`, then the pulled-back current
  `(u - h) ∘ π + ε log (U₂ ∘ π)` (`BlowupBigPullback.pullbackCurrent`, `U₂` the Blanchard weight of
  the exceptional centre `C₂ = π(Exc π)`) has Lelong number `0` at `z`: `U₂ ∘ π > 0` near `z`, and
  `ν((u - h) ∘ π, z) ≤ ν(u - h, π z) ≤ ν(u, π z)` (`HolomorphicLocalInverse`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupNonKahlerLocus

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  BlanchardWeight FactorizedWeightForm FactorizedWeightPsh BlowupExceptionalCentre

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- In dimension `0` every Lelong number is positive (the punctured neighbourhoods are empty). -/
theorem lelongNumber_pos_of_dim_eq_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (hn : n = 0) (u : M → EReal)
    (x : M) : 0 < lelongNumber (n := n) u x := by
  subst hn
  have hbot : 𝓝[≠] x = ⊥ := by
    have hsub : (chartAt (ComplexModel 0) x).source ⊆ {x} := fun y hy =>
      (chartAt (ComplexModel 0) x).injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)
    rw [← empty_mem_iff_bot, mem_nhdsWithin]
    exact ⟨_, (chartAt (ComplexModel 0) x).open_source, mem_chart_source _ x,
      fun y hy => absurd (hsub hy.1) hy.2⟩
  exact LelongNumberComparison.lelongNumber_pos_of_le_log (γ := 1) one_pos (C := 0)
    (by rw [hbot]; exact Filter.eventually_bot)

/-- **`E_nK(π^* α) ⊆ π⁻¹ E_nK(α) ∪ Exc π`.** -/
theorem nonKahlerLocus_pullback_subset [CompactSpace Y] (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    nonKahlerLocus (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) ⊆
      g ⁻¹' nonKahlerLocus (RealBottChern.ofRepresentative θ) ∪ exceptionalLocus n g := by
  intro z hz
  by_contra hcon
  simp only [mem_union, mem_preimage, not_or] at hcon
  obtain ⟨hzY, hzE⟩ := hcon
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact hzY fun T => lelongNumber_pos_of_dim_eq_zero hn _ _
  simp only [mem_nonKahlerLocus, not_forall, not_lt, nonpos_iff_eq_zero] at hzY
  obtain ⟨T, hT0⟩ := hzY
  have := BlowupCompact.compactSpace_of_isBlowupAlong hg
  obtain ⟨D, -, hflatC⟩ := exists_blanchardData_exceptionalCentre hg
  have hC₂C := exceptionalCentre_subset hg
  have hexc : ∀ z', g z' ∉ exceptionalCentre n g → z' ∉ exceptionalLocus n g :=
    fun z' h hE => h ⟨z', hE, rfl⟩
  obtain ⟨F, ε, hε, hK⟩ := BlowupKahler.exists_isKahler_pullback_add_of_flat T.lowerBound hg D
    hflatC (isClosed_exceptionalCentre hg) hC₂C hexc
  obtain ⟨h, hh, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
  have hU : ∀ y ∉ C, 0 < D.weight y := fun y hy => D.weight_pos_of_notMem fun h2 => hy (hC₂C h2)
  set R := BlowupBigPullback.pullbackCurrent T hg hh heq hU F hε hK
  have hR := hz R
  -- the weight is positive near `z`
  have hgz : g z ∉ exceptionalCentre n g := fun h2 => hzE (by
    rw [← preimage_exceptionalCentre hg]; exact h2)
  have hwc : Continuous fun z' => D.weight (g z') :=
    (KahlerCurrentMax.continuous_of_chartSmooth D.chartSmooth_weight).comp hg.contMDiff.continuous
  have hpos : ∀ᶠ z' in 𝓝 z, 0 < D.weight (g z') :=
    hwc.continuousAt.eventually (lt_mem_nhds (D.weight_pos_of_notMem hgz))
  set u : Y → EReal := fun y => T.potential y - (h y : EReal)
  have hRpot : R.potential =ᶠ[𝓝 z]
      fun z' => u (g z') + ((ε * Real.log (D.weight (g z')) : ℝ) : EReal) := by
    filter_upwards [hpos] with z' hz'
    rw [BlowupBigPullback.pullbackCurrent_potential,
      logWeight_of_pos (U := fun z' => D.weight (g z')) hz', ← EReal.coe_mul]
  have hlogc : ContinuousAt (fun z' => ε * Real.log (D.weight (g z'))) z :=
    continuousAt_const.mul (hwc.continuousAt.log (D.weight_pos_of_notMem hgz).ne')
  -- `u ∘ g` is theta-psh, so a positive Lelong number forces a pole
  have hu₁ : ThetaPlurisubharmonic (θ - T.lowerBound.form).val u := by
    refine GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hh (fun e z hz => ?_)
      T.strictlyPsh.1
    rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, heq e z hz]
    abel
  have hpull := GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff hu₁
  have hle : lelongNumber (n := n) R.potential z ≤ lelongNumber (n := n) T.potential (g z) := by
    rw [LelongNumberComparison.lelongNumber_congr hRpot]
    refine (LelongNumberComparison.lelongNumber_add_le hlogc).trans ?_
    refine (HolomorphicLocalInverse.lelongNumber_comp_le hg.contMDiff hzE (u := u)
      fun hpos => eq_bot_of_lelongNumber_pos hn hpull hpos).trans ?_
    exact KahlerCurrentMax.lelongNumber_sub_le
      (KahlerCurrentMax.continuous_of_chartSmooth hh).continuousAt
  rw [hT0] at hle
  exact absurd hR (not_lt.mpr hle)

end

end Hironaka.BlowupNonKahlerLocus
