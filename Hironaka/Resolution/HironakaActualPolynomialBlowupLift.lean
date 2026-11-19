import Hironaka.Resolution.HironakaActualFormalBlowupMemberGeneration

/-! Polynomial denominator clearing in the SAME actual coordinate blowup.
The source polynomial lies in its genuine centre power. No target ideal,
Hilbert--Samuel equality or division output is an input.
Blueprint: `hironaka-actual-polynomial-blowup-lift-20261102.tex`. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaActualPolynomialBlowupLift
noncomputable section
open HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration
variable {n : ℕ}

private theorem polynomial_coe_sub (P Q : MvPolynomial (Fin n) ℂ) :
    ((P - Q : MvPolynomial (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ) =
      (P : MvPowerSeries (Fin n) ℂ) - (Q : MvPowerSeries (Fin n) ℂ) :=
  MvPolynomial.coeToMvPowerSeries.ringHom.map_sub P Q

private theorem coordinate_mem (A : Set (Fin n)) (i : Fin n) (hi : i ∈ A) :
    (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ) ∈ actualFormalCoordinateIdeal n A :=
  Ideal.subset_span ⟨i, hi, rfl⟩

private theorem blowup_constant (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (c : ℂ) : actualFormalBlowup A e b (MvPowerSeries.C c) = MvPowerSeries.C c :=
  (actualFormalBlowup A e b).commutes c

private theorem blowup_pivot (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) :
    actualFormalBlowup A e b (MvPowerSeries.X e) = MvPowerSeries.X e := by
  rw [actualFormalBlowup_X]
  simp [actualFormalBlowupCoordinates, he]

private theorem variable_lift (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (i : Fin n) :
    ∃ (d : ℕ) (L : MvPolynomial (Fin n) ℂ),
      (L : MvPowerSeries (Fin n) ℂ) ∈ actualFormalCoordinateIdeal n A ^ d ∧
      actualFormalBlowup A e b (L : MvPowerSeries (Fin n) ℂ) =
        (MvPowerSeries.X e) ^ d * MvPowerSeries.X i := by
  classical
  by_cases hi : i ∈ A
  · by_cases hie : i = e
    · subst i
      refine ⟨0, MvPolynomial.X e, ?_, ?_⟩
      · simp
      · simpa using blowup_pivot A e he b
    · refine ⟨1, MvPolynomial.X i - MvPolynomial.C (b i) * MvPolynomial.X e, ?_, ?_⟩
      · simp only [polynomial_coe_sub, MvPolynomial.coe_mul, MvPolynomial.coe_C,
          MvPolynomial.coe_X, pow_one]
        exact Ideal.sub_mem _ (coordinate_mem A i hi)
          (Ideal.mul_mem_left _ _ (coordinate_mem A e he))
      · simp only [polynomial_coe_sub, MvPolynomial.coe_mul, MvPolynomial.coe_C,
          MvPolynomial.coe_X, map_sub, map_mul, blowup_constant,
          actualFormalBlowup_X, actualFormalBlowupCoordinates, if_pos hi,
          if_neg hie, if_pos he, ite_true, pow_one]
        ring
  · refine ⟨0, MvPolynomial.X i, ?_, ?_⟩
    · simp
    · simp [actualFormalBlowup_X, actualFormalBlowupCoordinates, hi]

/-- Every target polynomial has an actual polynomial lift in a true source centre power. -/
theorem exists_actual_polynomial_blowup_lift (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    ∃ (N : ℕ) (H : MvPolynomial (Fin n) ℂ),
      (H : MvPowerSeries (Fin n) ℂ) ∈ actualFormalCoordinateIdeal n A ^ N ∧
      actualFormalBlowup A e b (H : MvPowerSeries (Fin n) ℂ) =
        (MvPowerSeries.X e) ^ N * (P : MvPowerSeries (Fin n) ℂ) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      refine ⟨0, MvPolynomial.C c, ?_, ?_⟩
      · simp
      · simpa using blowup_constant A e b c
  | add P Q hP hQ =>
      obtain ⟨N, H, hH, hsH⟩ := hP
      obtain ⟨M, K, hK, hsK⟩ := hQ
      refine ⟨N + M, H * MvPolynomial.X e ^ M + K * MvPolynomial.X e ^ N, ?_, ?_⟩
      · simp only [MvPolynomial.coe_add, MvPolynomial.coe_mul, MvPolynomial.coe_pow,
          MvPolynomial.coe_X, pow_add]
        exact Ideal.add_mem _
          (Ideal.mul_mem_mul hH (Ideal.pow_mem_pow (coordinate_mem A e he) M))
          (Ideal.mul_mem_mul_rev (Ideal.pow_mem_pow (coordinate_mem A e he) N) hK)
      · simp only [MvPolynomial.coe_add, MvPolynomial.coe_mul, MvPolynomial.coe_pow,
          MvPolynomial.coe_X, map_add, map_mul, map_pow, blowup_pivot A e he b,
          hsH, hsK, pow_add]
        ring
  | mul_X P i hP =>
      obtain ⟨N, H, hH, hsH⟩ := hP
      obtain ⟨d, L, hL, hsL⟩ := variable_lift A e he b i
      refine ⟨N + d, H * L, ?_, ?_⟩
      · simpa only [MvPolynomial.coe_mul, pow_add] using Ideal.mul_mem_mul hH hL
      · simp only [MvPolynomial.coe_mul, map_mul, hsH, hsL, MvPolynomial.coe_X,
          pow_add]
        ring

/-- The lift's genuinely defined exceptional normalization is the desired target polynomial. -/
theorem exists_actual_normalized_polynomial_lift (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    ∃ (N : ℕ) (H : MvPolynomial (Fin n) ℂ)
      (hH : (H : MvPowerSeries (Fin n) ℂ) ∈ actualFormalCoordinateIdeal n A ^ N),
      actualNormalizedFormalMember A e he b N (H : MvPowerSeries (Fin n) ℂ) hH =
        (P : MvPowerSeries (Fin n) ℂ) := by
  obtain ⟨N, H, hH, hsH⟩ := exists_actual_polynomial_blowup_lift A e he b P
  exact ⟨N, H, hH, (actualNormalizedFormalMember_unique A e he b N
    (H : MvPowerSeries (Fin n) ℂ) hH (P : MvPowerSeries (Fin n) ℂ) hsH.symm).symm⟩

end
end Hironaka.HironakaActualPolynomialBlowupLift
