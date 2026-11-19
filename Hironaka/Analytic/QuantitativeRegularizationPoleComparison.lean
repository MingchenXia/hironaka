import Hironaka.Analytic.PointPoleExtension

set_option autoImplicit false

/-! # Local comparison for the point-pole weights -/

open scoped ENNReal

namespace Hironaka.QuantitativeRegularizationPoleComparison

noncomputable section



variable {d p : ℕ}

/-- On a ball where `φ ≤ A`, shrinking the regularizing radius from `η` to
`δ ≤ η` makes the point-pole weight dominate the `η`-pole with an explicit
constant.  This is the pointwise comparison needed to instantiate the pole
domination premise of `QuantitativeRegularizationPoleLimit`. -/
theorem exp_neg_poleWeight_lower_bound {φ : ComplexModel d → ℝ}
    {x z : ComplexModel d} {A R δ η : ℝ}
    (hφ : φ z ≤ A) (hz : ‖z - x‖ ≤ R) (hδ : 0 < δ) (hδη : δ ≤ η) :
    Real.exp (-A - (‖x‖ + R) ^ 2) *
        ((‖z - x‖ ^ 2 + η ^ 2) ^ p)⁻¹ ≤
      Real.exp (-PointPole.poleWeight p φ x δ z) := by
  rw [PointPole.exp_neg_poleWeight φ x hδ z]
  have hnorm : ‖z‖ ≤ ‖x‖ + R := by
    calc ‖z‖ ≤ ‖x‖ + ‖z - x‖ := norm_le_norm_add_norm_sub' z x
      _ ≤ ‖x‖ + R := by linarith
  have hsq : ‖z‖ ^ 2 ≤ (‖x‖ + R) ^ 2 := by
    have hsum : 0 ≤ ‖x‖ + R := (norm_nonneg z).trans hnorm
    exact (sq_le_sq₀ (norm_nonneg _) hsum).mpr hnorm
  have hexpφ : Real.exp (-A) ≤ Real.exp (-φ z) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexpz : Real.exp (-((‖x‖ + R) ^ 2)) ≤ Real.exp (-‖z‖ ^ 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hbase : 0 < ‖z - x‖ ^ 2 + δ ^ 2 := by positivity
  have hη : 0 ≤ η := le_trans hδ.le hδη
  have hden : ‖z - x‖ ^ 2 + δ ^ 2 ≤ ‖z - x‖ ^ 2 + η ^ 2 := by
    nlinarith [sq_nonneg η, sq_nonneg δ]
  have hinv : ((‖z - x‖ ^ 2 + η ^ 2) ^ p)⁻¹ ≤
      ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ :=
    inv_anti₀ (pow_pos hbase p) (pow_le_pow_left₀ hbase.le hden p)
  rw [show -A - (‖x‖ + R) ^ 2 = -A + (-((‖x‖ + R) ^ 2)) by ring,
    Real.exp_add]
  calc
    (Real.exp (-A) * Real.exp (-((‖x‖ + R) ^ 2))) *
        ((‖z - x‖ ^ 2 + η ^ 2) ^ p)⁻¹
        ≤ (Real.exp (-φ z) * Real.exp (-‖z‖ ^ 2)) *
          ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ := by
            gcongr
    _ = Real.exp (-φ z) * ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ *
          Real.exp (-‖z‖ ^ 2) := by ring

end

end Hironaka.QuantitativeRegularizationPoleComparison
