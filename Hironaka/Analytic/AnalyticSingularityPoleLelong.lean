import Hironaka.Analytic.GlobalAnalyticSingularities
import Hironaka.Analytic.LelongNumberComparison
import Hironaka.Analytic.FactorizedWeightForm

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Poles of a potential with analytic singularities have positive Lelong number

Source: Demailly, *Complex analytic and differential geometry*, III.5 (the Lelong
number of `c log ∑ |g_i|²`) together with the definition of analytic singularities
in Copy-4, `sec:prelim`.

If `φ` has analytic singularities of type `(c, 𝔞)` then near every point
`φ = c log ∑ |g_i|² + R` with `R` bounded and the `g_i` holomorphic.  At a pole
`x` of `φ` the presentation forces `g_i x = 0` for every `i`, so each `g_i` is
`O(‖z - x‖)` in the preferred chart; hence

    φ ≤ 2c · log ‖z - x‖ + O(1)

near `x`, and `ν(φ, x) ≥ 2c > 0`.

This discharges the hypothesis `hpole_pos` of
`Hironaka.KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos_of_explicit_lelongComparison`
for any regularized current presented with analytic singularities: that
obligation is not an extra analytic input, it is a consequence of the
presentation.  Everything here is sorry-free.
-/

open Set Filter Asymptotics
open scoped Topology Manifold ENNReal ContDiff

namespace Hironaka.AnalyticSingularityPoleLelong

open Hironaka.NonKahlerLocus Hironaka.GlobalAnalyticSingularities
  Hironaka.NumericalRestrictedVolumeScaffold

noncomputable section

/-- A common bound `‖g_i‖ ≤ K d` turns the logarithmic generator weight into
`2 log d + log (N K²)`.  Degenerate cases (`d = 0`, `N = 0`, all generators
vanishing) are exactly the cases where the left side is `⊥`. -/
theorem generatorLog_le_two_log_of_norm_le {X : Type*} {N : ℕ}
    (f : Fin N → X → ℂ) (y : X) {K d : ℝ} (hK : 0 < K) (hd : 0 ≤ d)
    (hbound : ∀ j, ‖f j y‖ ≤ K * d) :
    generatorLog f y ≤ ((2 * Real.log d + Real.log ((N : ℝ) * K ^ 2) : ℝ) : EReal) := by
  by_cases hzero : ∀ j, f j y = 0
  · rw [(generatorLog_eq_bot_iff f y).mpr hzero]
    exact bot_le
  obtain ⟨j0, hj0⟩ := not_forall.mp hzero
  have hj0sq : 0 < ‖f j0 y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hj0) 2
  have hS : 0 < generatorNormSq f y := by
    refine lt_of_lt_of_le hj0sq ?_
    exact Finset.single_le_sum (f := fun j => ‖f j y‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ j0)
  have hd0 : 0 < d := by
    rcases hd.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hbound j0
      rw [← h, mul_zero] at this
      exact absurd (norm_eq_zero.mp (le_antisymm this (norm_nonneg _))) hj0
  have hNpos : 0 < (N : ℝ) := by
    have : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact absurd j0.isLt (by omega))
    exact_mod_cast this
  have hle : generatorNormSq f y ≤ (N : ℝ) * K ^ 2 * d ^ 2 := by
    have : ∑ j, ‖f j y‖ ^ 2 ≤ ∑ _j : Fin N, (K * d) ^ 2 :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hbound j) 2
    calc generatorNormSq f y = ∑ j, ‖f j y‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin N, (K * d) ^ 2 := this
      _ = (N : ℝ) * (K * d) ^ 2 := by simp
      _ = (N : ℝ) * K ^ 2 * d ^ 2 := by ring
  rw [generatorLog_of_nonzero ⟨j0, hj0⟩, EReal.coe_le_coe_iff]
  calc Real.log (generatorNormSq f y)
      ≤ Real.log ((N : ℝ) * K ^ 2 * d ^ 2) := Real.log_le_log hS hle
    _ = Real.log ((N : ℝ) * K ^ 2) + 2 * Real.log d := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        push_cast
        ring
    _ = 2 * Real.log d + Real.log ((N : ℝ) * K ^ 2) := by ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A pole of a potential with analytic singularities has positive Lelong
number.**  The explicit bound produced is `ν(φ, x) ≥ 2c` for the coefficient `c`
of the presentation. -/
theorem lelongNumber_pos_of_hasAnalyticSingularities {φ : M → EReal}
    (hφ : HasAnalyticSingularities (n := n) φ) {x : M} (hx : φ x = ⊥) :
    0 < lelongNumber (n := n) φ x := by
  obtain ⟨c, 𝔞, hc, -, hlocal⟩ := hφ
  obtain ⟨U, hU, hxU, N, g, hgdiff, -, R, C, hRC, hrep⟩ := hlocal x
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  -- every generator vanishes at the pole
  have hgx : ∀ j, g j x = 0 :=
    (scaled_generatorLog_add_eq_bot_iff g x hcpos (R x)).mp
      ((hrep x hxU).symm.trans hx)
  have hxe : x ∈ (complexChartAt (n := n) x).val.source := mem_complexChartAt_source x
  -- each generator is `O(‖z - x‖)` in the preferred chart
  have hlip : ∀ j : Fin N, ∃ K : ℝ, 0 < K ∧ ∀ᶠ y in 𝓝 x, ‖g j y‖ ≤ K *
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ := by
    intro j
    have hmd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g j) x :=
      (hgdiff j).mdifferentiableAt (hU.mem_nhds hxU)
    have hGd : DifferentiableAt ℂ
        (fun ζ => g j ((complexChartAt (n := n) x).val.symm ζ))
        ((complexChartAt (n := n) x).val x) := by
      refine FactorizedWeightForm.differentiableAt_comp_chart_symm _
        ((complexChartAt (n := n) x).val.map_source hxe) ?_
      rw [(complexChartAt (n := n) x).val.left_inv hxe]
      exact hmd
    obtain ⟨K, hK, hKw⟩ := hGd.hasFDerivAt.isBigO_sub.exists_pos
    refine ⟨K, hK, ?_⟩
    filter_upwards [((complexChartAt (n := n) x).val.continuousAt hxe).eventually hKw.bound,
      (complexChartAt (n := n) x).val.open_source.mem_nhds hxe] with y hy hye
    simpa [(complexChartAt (n := n) x).val.left_inv hye,
      (complexChartAt (n := n) x).val.left_inv hxe, hgx j] using hy
  choose Kf hKfpos hKfbound using hlip
  have hsum : (0 : ℝ) ≤ ∑ j, Kf j := Finset.sum_nonneg fun j _ => (hKfpos j).le
  set K : ℝ := 1 + ∑ j, Kf j with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKfle : ∀ j, Kf j ≤ K := by
    intro j
    have := Finset.single_le_sum (f := Kf) (fun i _ => (hKfpos i).le) (Finset.mem_univ j)
    rw [hKdef]; linarith
  have hall : ∀ᶠ y in 𝓝 x, ∀ j, ‖g j y‖ ≤ K *
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ := by
    rw [eventually_all]
    intro j
    filter_upwards [hKfbound j] with y hy
    exact hy.trans (mul_le_mul_of_nonneg_right (hKfle j) (norm_nonneg _))
  refine LelongNumberComparison.lelongNumber_pos_of_le_log
    (γ := 2 * (c : ℝ)) (by positivity)
    (C := (c : ℝ) * Real.log ((N : ℝ) * K ^ 2) + C) ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hall, hU.mem_nhds hxU] with y hy hyU _
  have hbnd := generatorLog_le_two_log_of_norm_le g y hKpos (norm_nonneg _) hy
  rw [hrep y hyU]
  rcases eq_or_ne (generatorLog g y) ⊥ with hb | hb
  · rw [hb, EReal.coe_mul_bot_of_pos hcpos, EReal.bot_add]
    exact bot_le
  · have hga : generatorLog g y = (((generatorLog g y).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (generatorLog_ne_top g y) hb).symm
    rw [hga] at hbnd ⊢
    rw [EReal.coe_le_coe_iff] at hbnd
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith [mul_le_mul_of_nonneg_left hbnd hcpos.le, (abs_le.mp (hRC y hyU)).2]

/-- The pole set of a potential with analytic singularities is contained in its
own positive-Lelong locus. -/
theorem poleSet_subset_lelongNumber_pos_of_hasAnalyticSingularities {φ : M → EReal}
    (hφ : HasAnalyticSingularities (n := n) φ) :
    poleSet φ ⊆ {x | 0 < lelongNumber (n := n) φ x} :=
  fun _ hx => lelongNumber_pos_of_hasAnalyticSingularities hφ hx

end

end Hironaka.AnalyticSingularityPoleLelong
