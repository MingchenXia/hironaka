import Hironaka.Analytic.LelongNumberComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Scaling and bounded perturbation of Lelong numbers

Two elementary consequences of the definition of `lelongNumber` as the supremum of the
exponents `γ` admitting a bound `u ≤ γ log ‖· - x‖ + C` near `x`.  Both are proved by
transporting an admissible exponent, so neither needs plurisubharmonicity.

* `lelongNumber_smul_le`: `ν(c u, x) ≤ c · ν(u, x)` for `c > 0`.
* `lelongNumber_le_add_of_eventually_le_const`: adding a function that is bounded above near
  `x` does not decrease the Lelong number.
-/

open Set Filter
open scoped Topology ENNReal NNReal

namespace Hironaka.LelongNumberScaling

open Hironaka.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Adding a function bounded above near `x` does not decrease the Lelong number. -/
theorem lelongNumber_le_add_of_eventually_le_const {u v : M → EReal} {x : M} {c : ℝ}
    (hv : ∀ᶠ y in 𝓝[≠] x, v y ≤ (c : EReal)) :
    lelongNumber (n := n) u x ≤ lelongNumber (n := n) (fun y => u y + v y) x := by
  unfold lelongNumber
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨C, hC⟩ := hγ
  refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
      u y + v y ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) γ ⟨C + c, ?_⟩ le_rfl
  filter_upwards [hC, hv] with y hy hyv
  calc u y + v y ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
          EReal) + (c : EReal) := add_le_add hy hyv
    _ = _ := by rw [← EReal.coe_add]; ring_nf

/-- A positive multiple scales the Lelong number by at most that factor. -/
theorem lelongNumber_smul_le {u : M → EReal} {x : M} {c : ℝ} (hc : 0 < c) :
    lelongNumber (n := n) (fun y => (c : EReal) * u y) x ≤
      ENNReal.ofReal c * lelongNumber (n := n) u x := by
  conv_lhs => unfold lelongNumber
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨C, hC⟩ := hγ
  set δ : ℝ≥0 := ⟨(γ : ℝ) / c, by positivity⟩ with hδ
  have hδu : (δ : ℝ≥0∞) ≤ lelongNumber (n := n) u x := by
    unfold lelongNumber
    refine le_iSup₂_of_le (f := fun (γ' : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
        u y ≤ (((γ' : ℝ) * Real.log
          ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
            EReal)) => (γ' : ℝ≥0∞)) δ ⟨C / c, ?_⟩ le_rfl
    filter_upwards [hC] with y hy
    set L : ℝ := Real.log
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ with hL
    induction hu : u y using EReal.rec with
    | bot => exact bot_le
    | top =>
        rw [hu, EReal.coe_mul_top_of_pos hc] at hy
        exact absurd (top_le_iff.mp hy) (EReal.coe_ne_top _)
    | coe a =>
        rw [hu, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hy
        refine EReal.coe_le_coe_iff.mpr ?_
        rw [hδ]
        show a ≤ (γ : ℝ) / c * L + C / c
        rw [div_mul_eq_mul_div, ← add_div]
        exact (le_div_iff₀ hc).mpr (by linarith [hy])
  have hγδ : (γ : ℝ) = c * (δ : ℝ) := by
    show (γ : ℝ) = c * ((γ : ℝ) / c)
    field_simp
  calc (γ : ℝ≥0∞) = ENNReal.ofReal ((γ : ℝ)) := by
        rw [ENNReal.ofReal_coe_nnreal]
    _ = ENNReal.ofReal c * (δ : ℝ≥0∞) := by
        rw [hγδ, ENNReal.ofReal_mul hc.le, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal c * lelongNumber (n := n) u x := by
        gcongr

end

end Hironaka.LelongNumberScaling
