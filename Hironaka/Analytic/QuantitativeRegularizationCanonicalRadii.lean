import Hironaka.Analytic.QuantitativeRegularizationPoleISup

set_option autoImplicit false

/-! # Canonical shrinking radii for point-pole regularization -/

namespace Hironaka.QuantitativeRegularizationCanonicalRadii

noncomputable section



variable {d p : ℕ}

/-- The canonical positive regularization radii used for the point-pole limit. -/
def canonicalRadius (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)

/-- Every canonical regularization radius is positive. -/
theorem canonicalRadius_pos (i : ℕ) : 0 < canonicalRadius i := by
  exact div_pos zero_lt_one (by positivity)

/-- The canonical regularization radii decrease with their index. -/
theorem canonicalRadius_antitone : Antitone canonicalRadius := by
  intro i j hij
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hij 1

/-- The canonical radii reach every prescribed positive scale. -/
theorem exists_canonicalRadius_le (η : ℝ) (hη : 0 < η) :
    ∃ i : ℕ, canonicalRadius i ≤ η := by
  obtain ⟨i, hi⟩ := exists_nat_gt (1 / η)
  refine ⟨i, ?_⟩
  rw [canonicalRadius]
  apply (div_le_iff₀ (by positivity)).mpr
  have hmul : (1 / η) * η < (i : ℝ) * η :=
    mul_lt_mul_of_pos_right hi hη
  have hone : (1 : ℝ) < (i : ℝ) * η := by
    calc
      1 = (1 / η) * η := by field_simp [hη.ne']
      _ < (i : ℝ) * η := hmul
  nlinarith

/-- The canonical radii instantiate the pole-domination lower bound on any
region where the local upper bounds for `φ` and the norm are available. -/
theorem canonicalRadius_inverse_pole_le_iSup_exp_neg_poleWeight
    {φ : ComplexModel d → ℝ} {x z : ComplexModel d} {A R η : ℝ}
    (hφ : φ z ≤ A) (hz : ‖z - x‖ ≤ R) (hη : 0 < η) :
    ENNReal.ofReal (Real.exp (-A - (‖x‖ + R) ^ 2)) *
        ENNReal.ofReal (((‖z - x‖ ^ 2 + η ^ 2) ^ p)⁻¹) ≤
      ⨆ i, ENNReal.ofReal
        (Real.exp (-PointPole.poleWeight p φ x (canonicalRadius i) z)) :=
  QuantitativeRegularizationPoleISup.inverse_pole_le_iSup_exp_neg_poleWeight
    canonicalRadius_pos exists_canonicalRadius_le hφ hz hη

end

end Hironaka.QuantitativeRegularizationCanonicalRadii
