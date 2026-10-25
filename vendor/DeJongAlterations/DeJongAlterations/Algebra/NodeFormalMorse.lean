import DeJongAlterations.Algebra.NodeFormalMorseCorrection
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Squared ideal powers and literal quotient split-node corrections

The correction over `A / I^(2*n)` is constructed from the original series
and its original coefficient ideal. Square-zero nilpotence is proved inside
the literal quotient, including the zero-ring case `n = 0`.

This is a bounded correction only. It does not assert a complete separated
limit, a flat complete hypersurface presentation, or étale algebraization.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse

open MvPowerSeries

universe u
variable {R : Type u} [CommRing R]

/-- The exact improved error order is `I^(2*n)`, with the original constant retained. -/
theorem correctedError_power_coeff_mem (I : Ideal R) (hI : IsNilpotent I)
    (n : ℕ) (hn : n ≠ 0) (H : Series R) (hH : ∀ d, coeff d H ∈ I ^ n) :
    ∀ d, coeff d
      (correctedError (I ^ n) (hI.pow_of_pos hn) H hH - C (constantCoeff H)) ∈ I ^ (2 * n) := by
  simpa only [← pow_mul, Nat.mul_comm n 2] using
    correctedError_sub_constant_coeff_mem (I ^ n) (hI.pow_of_pos hn) H hH

/-- Removing the actual new constant gives the same precise doubled order. -/
theorem correctedResidual_power_coeff_mem (I : Ideal R) (hI : IsNilpotent I)
    (n : ℕ) (hn : n ≠ 0) (H : Series R) (hH : ∀ d, coeff d H ∈ I ^ n) :
    ∀ d, coeff d (correctedResidual (I ^ n) (hI.pow_of_pos hn) H hH) ∈ I ^ (2 * n) := by
  simpa only [← pow_mul, Nat.mul_comm n 2] using
    correctedResidual_coeff_mem (I ^ n) (hI.pow_of_pos hn) H hH

/-- The complete bounded correction data are internally constructed from the original error. -/
theorem exists_power_correction (I : Ideal R) (hI : IsNilpotent I)
    (n : ℕ) (hn : n ≠ 0) (h : R) (H : Series R) (hH : ∀ d, coeff d H ∈ I ^ n) :
    ∃ (e : Series R ≃ₐ[R] Series R) (h' : R) (E' : Series R),
      e (X 0) = X 0 - secondPart H ∧
      e (X 1) = X 1 - firstPart H ∧
      e.symm (X 0 * X 1 - C h - H) = X 0 * X 1 - C h' - E' ∧
      h' - h ∈ I ^ n ∧
      (∀ d, coeff d E' ∈ I ^ (2 * n)) ∧
      constantCoeff E' = 0 ∧
      (∀ f, MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) (e f) =
        MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) f) ∧
      (∀ f, MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) (e.symm f) =
        MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) f) := by
  refine ⟨correctionEquiv (I ^ n) (hI.pow_of_pos hn) H hH,
    h + correctedConstant (I ^ n) (hI.pow_of_pos hn) H hH,
    correctedResidual (I ^ n) (hI.pow_of_pos hn) H hH,
    correctionEquiv_X_zero _ _ _ _, correctionEquiv_X_one _ _ _ _,
    correctionEquation_with_constant _ _ _ _ _, ?_,
    correctedResidual_power_coeff_mem I hI n hn H hH,
    correctedResidual_constantCoeff _ _ _ _,
    correctionEquiv_reduction _ _ _ _, correctionEquiv_symm_reduction _ _ _ _⟩
  simpa only [add_sub_cancel_left] using
    correctedConstant_mem (I ^ n) (hI.pow_of_pos hn) H hH

/-- The literal coefficient quotient for the doubled error order. -/
abbrev QuotientCoefficients (I : Ideal R) (n : ℕ) := R ⧸ I ^ (2 * n)

/-- The actual correction ideal in the literal coefficient quotient. -/
def quotientCorrectionIdeal (I : Ideal R) (n : ℕ) : Ideal (QuotientCoefficients I n) :=
  (I.map (Ideal.Quotient.mk (I ^ (2 * n)))) ^ n

/-- Square-zero follows internally from the original ideal power killed by the quotient. -/
theorem quotientCorrectionIdeal_sq (I : Ideal R) (n : ℕ) :
    quotientCorrectionIdeal I n ^ 2 = 0 := by
  unfold quotientCorrectionIdeal
  rw [← pow_mul, ← Ideal.map_pow, Nat.mul_comm n 2, Ideal.map_quotient_self]
  rfl

/-- No nilpotence certificate is requested of the caller of the quotient construction. -/
theorem quotientCorrectionIdeal_isNilpotent (I : Ideal R) (n : ℕ) :
    IsNilpotent (quotientCorrectionIdeal I n) :=
  ⟨2, quotientCorrectionIdeal_sq I n⟩

/-- The original coefficientwise power condition descends along the actual quotient map. -/
theorem quotientError_coeff_mem (I : Ideal R) (n : ℕ) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I ^ n) :
    ∀ d, coeff d (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) H) ∈
      quotientCorrectionIdeal I n := by
  intro d
  rw [coeff_map]
  unfold quotientCorrectionIdeal
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (hH d)

/-- The actual coefficient-preserving coordinate automorphism over `R / I^(2*n)`. -/
def quotientCorrectionEquiv (I : Ideal R) (n : ℕ) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I ^ n) :
    Series (QuotientCoefficients I n) ≃ₐ[QuotientCoefficients I n]
      Series (QuotientCoefficients I n) :=
  correctionEquiv (quotientCorrectionIdeal I n) (quotientCorrectionIdeal_isNilpotent I n)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) H) (quotientError_coeff_mem I n H hH)

@[simp]
theorem quotientCorrectionEquiv_X_zero (I : Ideal R) (n : ℕ) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I ^ n) :
    quotientCorrectionEquiv I n H hH (X 0) =
      X 0 - MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) (secondPart H) := by
  simp [quotientCorrectionEquiv, secondPart_map]

@[simp]
theorem quotientCorrectionEquiv_X_one (I : Ideal R) (n : ℕ) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I ^ n) :
    quotientCorrectionEquiv I n H hH (X 1) =
      X 1 - MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) (firstPart H) := by
  simp [quotientCorrectionEquiv, firstPart_map]

@[simp]
theorem quotientCorrectionEquiv_C (I : Ideal R) (n : ℕ) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I ^ n) (r : R) :
    quotientCorrectionEquiv I n H hH
      (C (Ideal.Quotient.mk (I ^ (2 * n)) r)) = C (Ideal.Quotient.mk (I ^ (2 * n)) r) := by
  simp [quotientCorrectionEquiv]

/-- The squared-error term actually vanishes over the literal doubled-power quotient. -/
theorem quotient_correctedError (I : Ideal R) (n : ℕ) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I ^ n) :
    correctedError (quotientCorrectionIdeal I n) (quotientCorrectionIdeal_isNilpotent I n)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) H) (quotientError_coeff_mem I n H hH) =
        C (Ideal.Quotient.mk (I ^ (2 * n)) (constantCoeff H)) := by
  have he : correctedError (quotientCorrectionIdeal I n) (quotientCorrectionIdeal_isNilpotent I n)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) H) (quotientError_coeff_mem I n H hH) -
        C (constantCoeff (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) H)) = 0 := by
    ext d
    have hd := correctedError_sub_constant_coeff_mem (quotientCorrectionIdeal I n)
      (quotientCorrectionIdeal_isNilpotent I n)
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) H) (quotientError_coeff_mem I n H hH) d
    rw [quotientCorrectionIdeal_sq] at hd
    simpa only [Ideal.zero_eq_bot, Ideal.mem_bot, map_zero] using hd
  simpa only [constantCoeff_map] using sub_eq_zero.mp he

/-- Exact formal normalization over the doubled-power quotient, with the original constant map. -/
theorem quotientCorrectionEquation (I : Ideal R) (n : ℕ) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I ^ n) :
    (quotientCorrectionEquiv I n H hH).symm
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) (X 0 * X 1 - H)) =
        X 0 * X 1 - C (Ideal.Quotient.mk (I ^ (2 * n)) (constantCoeff H)) := by
  have he := correctionEquation (quotientCorrectionIdeal I n)
    (quotientCorrectionIdeal_isNilpotent I n)
    (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) H) (quotientError_coeff_mem I n H hH)
  rw [quotient_correctedError I n H hH] at he
  simpa only [quotientCorrectionEquiv, map_sub, map_mul, MvPowerSeries.map_X] using he

/-- The baseline original scalar is also tracked through the literal quotient and inverse. -/
theorem quotientCorrectionEquation_with_constant (I : Ideal R) (n : ℕ) (h : R) (H : Series R)
    (hH : ∀ d, coeff d H ∈ I ^ n) :
    (quotientCorrectionEquiv I n H hH).symm
      (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (2 * n))) (X 0 * X 1 - C h - H)) =
        X 0 * X 1 - C (Ideal.Quotient.mk (I ^ (2 * n)) (h + constantCoeff H)) := by
  have he : X 0 * X 1 - C h - H = (X 0 * X 1 - H) - C h := by ring
  rw [he, map_sub, map_sub, quotientCorrectionEquation, MvPowerSeries.map_C]
  change X 0 * X 1 - C (Ideal.Quotient.mk (I ^ (2 * n)) (constantCoeff H)) -
    (quotientCorrectionEquiv I n H hH).symm (C (Ideal.Quotient.mk (I ^ (2 * n)) h)) = _
  rw [show (quotientCorrectionEquiv I n H hH).symm
    (C (Ideal.Quotient.mk (I ^ (2 * n)) h)) = C (Ideal.Quotient.mk (I ^ (2 * n)) h) from
      correctionEquiv_symm_C _ _ _ _ _]
  simp only [map_add]
  ring

end DeJongAlterations.Algebra.NodeFormalMorse
