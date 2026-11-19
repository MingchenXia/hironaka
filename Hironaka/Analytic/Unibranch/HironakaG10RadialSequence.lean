import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10RadialSequence
noncomputable def radii (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - 1 / ((n : ℝ) + 2), by
    constructor
    · have h : 1 / ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one₀ (by positivity)]
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    · have : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
      linarith⟩

theorem radii_strict (n : ℕ) : 0 < (radii n : ℝ) ∧ (radii n : ℝ) < 1 := by
  change 0 < 1 - 1 / ((n : ℝ) + 2) ∧ 1 - 1 / ((n : ℝ) + 2) < 1
  have h : 1 / ((n : ℝ) + 2) < 1 := by
    rw [div_lt_one₀ (by positivity)]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h' : 0 < 1 / ((n : ℝ) + 2) := by positivity
  constructor <;> linarith

theorem radii_tendsto : Tendsto radii atTop (𝓝 ⟨1,by simp⟩) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 : ℝ))
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h' : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert h using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    congr 1; ring
  simpa using tendsto_const_nhds.sub h'
end Hironaka.Analytic.Unibranch.HironakaG10RadialSequence
