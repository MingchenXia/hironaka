import Hironaka.Analytic.LelongNumberPole
import Hironaka.Analytic.KahlerCurrentMax
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Comparison of Lelong numbers

Source: Demailly, *Complex analytic and differential geometry*, III.7.

* `lelongNumber_le_comp`: for a map `f` differentiable at `z`, `ν(u, f z) ≤ ν(u ∘ f, z)`.
  In charts `‖f z' - f z‖ ≤ c ‖z' - z‖`, so a bound `u ≤ γ log ‖· - f z‖ + C` pulls back; at the
  points with `f z' = f z` the value `u (f z) = -∞` is used (a positive Lelong number forces a pole).
* `lelongNumber_congr`: the Lelong number only depends on the germ.
* `lelongNumber_pos_of_le_log`: an explicit logarithmic bound gives a positive Lelong number.
* `lelongNumber_le_sub`: adding back a continuous function does not increase the Lelong number.
-/

open Set Filter Asymptotics
open scoped Topology ENNReal NNReal Manifold

namespace Hironaka.LelongNumberComparison

open Hironaka.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V] [IsComplexManifold n V]

/-- An explicit logarithmic bound gives a positive Lelong number. -/
theorem lelongNumber_pos_of_le_log {u : M → EReal} {x : M} {γ : ℝ} (hγ : 0 < γ) {C : ℝ}
    (h : ∀ᶠ y in 𝓝[≠] x, u y ≤ ((γ * Real.log
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) : EReal)) :
    0 < lelongNumber (n := n) u x := by
  unfold lelongNumber
  refine lt_of_lt_of_le ?_ (le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
      u y ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) ⟨γ, hγ.le⟩ ⟨C, h⟩ le_rfl)
  exact ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hγ)

/-- The Lelong number only depends on the germ. -/
theorem lelongNumber_congr {u v : M → EReal} {x : M} (h : u =ᶠ[𝓝 x] v) :
    lelongNumber (n := n) u x = lelongNumber (n := n) v x :=
  le_antisymm
    (KahlerCurrentMax.lelongNumber_le_of_eventually_le
      (eventually_nhdsWithin_of_eventually_nhds (h.mono fun _ hy => hy.symm.le)))
    (KahlerCurrentMax.lelongNumber_le_of_eventually_le
      (eventually_nhdsWithin_of_eventually_nhds (h.mono fun _ hy => hy.le)))

omit [IsComplexManifold n M] in
/-- Adding a real function continuous at `x` does not increase the Lelong number. -/
theorem lelongNumber_add_le {u : M → EReal} {h : M → ℝ} {x : M} (hh : ContinuousAt h x) :
    lelongNumber (n := n) (fun y => u y + (h y : EReal)) x ≤ lelongNumber (n := n) u x := by
  have := KahlerCurrentMax.lelongNumber_sub_le (n := n) (u := u) (h := fun y => -h y) hh.neg
  simpa [sub_eq_add_neg] using this

omit [IsComplexManifold n M] in
/-- Subtracting a real function continuous at `x` does not decrease the Lelong number. -/
theorem lelongNumber_le_sub {u : M → EReal} {h : M → ℝ} {x : M} (hh : ContinuousAt h x) :
    lelongNumber (n := n) u x ≤ lelongNumber (n := n) (fun y => u y - (h y : EReal)) x := by
  have := lelongNumber_add_le (n := n) (u := fun y => u y - (h y : EReal)) hh
  simpa [EReal.sub_add_cancel] using this

/-- **Lelong numbers do not decrease under pullback.** -/
theorem lelongNumber_le_comp {f : V → M} {z : V}
    (hf : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f z) {u : M → EReal}
    (hbot : 0 < lelongNumber (n := n) u (f z) → u (f z) = ⊥) :
    lelongNumber (n := n) u (f z) ≤ lelongNumber (n := n) (fun z' => u (f z')) z := by
  set y := f z
  set d := complexChartAt (n := n) y
  set e := complexChartAt (n := n) z
  have hze : z ∈ e.val.source := mem_complexChartAt_source z
  have hyd : y ∈ d.val.source := mem_complexChartAt_source y
  -- the coordinate expression of `f` is differentiable
  set F : ComplexModel n → ComplexModel n := fun w => d.val (f (e.val.symm w))
  have hFd : DifferentiableAt ℂ F (e.val z) := by
    have h := hf.differentiableWithinAt_writtenInExtChartAt
    simp only [modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ] at h
    exact h
  obtain ⟨c, hc, hcw⟩ := hFd.hasFDerivAt.isBigO_sub.exists_pos
  have hlip : ∀ᶠ z' in 𝓝 z, ‖d.val (f z') - d.val y‖ ≤ c * ‖e.val z' - e.val z‖ := by
    have h1 := (e.val.continuousAt hze).eventually hcw.bound
    filter_upwards [h1, e.val.open_source.mem_nhds hze] with z' hz' hz'e
    simpa [F, e.val.left_inv hz'e, e.val.left_inv hze] using hz'
  have hfc : ContinuousAt f z := hf.continuousAt
  unfold lelongNumber
  refine iSup₂_le fun γ hγC => ?_
  obtain ⟨C, hC⟩ := hγC
  rcases eq_or_ne γ 0 with rfl | hγ0
  · simp
  have hγpos : (0 : ℝ) < γ := by
    have := (pos_iff_ne_zero (a := γ)).mpr hγ0; exact_mod_cast this
  have hybot : u y = ⊥ := hbot (lelongNumber_pos_of_le_log hγpos hC)
  refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ z' in 𝓝[≠] z,
      u (f z') ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) z).val z' - (complexChartAt (n := n) z).val z‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) γ ⟨C + γ * Real.log c, ?_⟩ le_rfl
  have hC' : ∀ᶠ z' in 𝓝 z, f z' ≠ y → u (f z') ≤ ((γ * Real.log
      ‖d.val (f z') - d.val y‖ + C : ℝ) : EReal) :=
    hfc.eventually (eventually_nhdsWithin_iff.mp hC)
  have hsrc : ∀ᶠ z' in 𝓝 z, f z' ∈ d.val.source := hfc.eventually (d.val.open_source.mem_nhds hyd)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hC', hsrc, hlip, e.val.open_source.mem_nhds hze] with z' h1 h2 h3 h4 hz'z
  by_cases hfz : f z' = y
  · rw [hfz, hybot]; exact bot_le
  have hnz : 0 < ‖e.val z' - e.val z‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hz'z (e.val.injOn h4 hze h)
  have hny : 0 < ‖d.val (f z') - d.val y‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hfz (d.val.injOn h2 hyd h)
  refine (h1 hfz).trans (EReal.coe_le_coe_iff.mpr ?_)
  have hlog : Real.log ‖d.val (f z') - d.val y‖ ≤ Real.log c + Real.log ‖e.val z' - e.val z‖ := by
    rw [← Real.log_mul hc.ne' hnz.ne']
    exact Real.log_le_log hny h3
  nlinarith [hlog, hγpos]

end

end Hironaka.LelongNumberComparison
