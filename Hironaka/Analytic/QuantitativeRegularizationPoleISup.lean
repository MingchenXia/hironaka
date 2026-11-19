import Hironaka.Analytic.QuantitativeRegularizationPoleComparison

set_option autoImplicit false

/-! # Supremum domination by shrinking point-pole weights -/

namespace Hironaka.QuantitativeRegularizationPoleISup

noncomputable section



variable {d p : ℕ}

/-- A positive family of regularizing radii that reaches every scale makes the
supremum of the corresponding point-pole weights dominate every fixed pole.
This is the `iSup` input required by `QuantitativeRegularizationPoleLimit`. -/
theorem inverse_pole_le_iSup_exp_neg_poleWeight {φ : ComplexModel d → ℝ}
    {x z : ComplexModel d} {A R η : ℝ} {δ : ℕ → ℝ}
    (hδpos : ∀ i, 0 < δ i)
    (hδsmall : ∀ η : ℝ, 0 < η → ∃ i, δ i ≤ η)
    (hφ : φ z ≤ A) (hz : ‖z - x‖ ≤ R) (hη : 0 < η) :
    ENNReal.ofReal (Real.exp (-A - (‖x‖ + R) ^ 2)) *
        ENNReal.ofReal (((‖z - x‖ ^ 2 + η ^ 2) ^ p)⁻¹) ≤
      ⨆ i, ENNReal.ofReal (Real.exp (-PointPole.poleWeight p φ x (δ i) z)) := by
  obtain ⟨i, hδi⟩ := hδsmall η hη
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_le_ofReal
    (QuantitativeRegularizationPoleComparison.exp_neg_poleWeight_lower_bound
      hφ hz (hδpos i) hδi)).trans (le_iSup (fun i =>
        ENNReal.ofReal (Real.exp (-PointPole.poleWeight p φ x (δ i) z))) i)

end

end Hironaka.QuantitativeRegularizationPoleISup
