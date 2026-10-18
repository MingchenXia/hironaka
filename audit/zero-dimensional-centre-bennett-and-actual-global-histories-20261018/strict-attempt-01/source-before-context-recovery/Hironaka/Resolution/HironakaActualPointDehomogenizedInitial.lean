/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointExceptionalInitialForm
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Actual finite polynomial dehomogenization identifies the whole exceptional restriction of genuine point-normalized members. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointDehomogenizedInitial
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualPointExceptionalInitialForm
variable {n : ℕ}

/-- The actual finite polynomial point-chart evaluation, with exceptional coordinate set to one. -/
def actualPointDehomogenization (e : Fin n) (b : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => if i=e then 1 else MvPolynomial.C (b i)+MvPolynomial.X i)

/-- Whole formal inclusion retains the exact actual finite polynomial evaluation. -/
theorem actualPointDehomogenization_coe (e : Fin n) (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ)=
      MvPolynomial.aeval (fun i => if i=e then 1 else MvPowerSeries.C (b i)+MvPowerSeries.X i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [actualPointDehomogenization]; rfl
  | add P Q hP hQ => simpa only [map_add,MvPolynomial.coe_add] using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
      simp only [map_mul,MvPolynomial.coe_mul,actualPointDehomogenization,MvPolynomial.aeval_X]
      dsimp only [actualPointDehomogenization] at hP
      rw [hP]
      split_ifs <;> simp

private theorem homogeneous_aeval_scaled (P : MvPolynomial (Fin n) ℂ) (d : ℕ)
    (hP : P.IsHomogeneous d) (x : Fin n → MvPowerSeries (Fin n) ℂ)
    (c : MvPowerSeries (Fin n) ℂ) :
    MvPolynomial.aeval (fun i => c*x i) P=c^d*MvPolynomial.aeval x P := by
  rw [← P.support_sum_monomial_coeff,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [MvPolynomial.aeval_monomial,Finsupp.prod,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [← hP.degree_eq_sum_deg_support ha]
  ac_rfl

/-- The genuine whole point blowup factors every actual homogeneous polynomial by its true exceptional degree. -/
theorem actualFormalBlowup_homogeneous_polynomial (e : Fin n) (b : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) (d : ℕ) (hP : P.IsHomogeneous d) :
    actualFormalBlowup Set.univ e b (P : MvPowerSeries (Fin n) ℂ)=
      (MvPowerSeries.X e)^d*(actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ) := by
  rw [actualFormalBlowup,MvPowerSeries.substAlgHom_apply,MvPowerSeries.subst_coe]
  have hc : actualFormalBlowupCoordinates Set.univ e b=
      fun i => MvPowerSeries.X e*(if i=e then 1 else MvPowerSeries.C (b i)+MvPowerSeries.X i) := by
    funext i
    by_cases hi : i=e <;> simp [actualFormalBlowupCoordinates,hi]
  rw [hc,homogeneous_aeval_scaled P d hP,← actualPointDehomogenization_coe]

/-- The actual finite initial polynomial is genuinely homogeneous, including the zero polynomial. -/
theorem actualPointHomogeneousPolynomial_isHomogeneous (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    (actualPointHomogeneousPolynomial d F).IsHomogeneous d := by
  intro a ha
  have hc : MvPowerSeries.coeff a (MvPowerSeries.homogeneousComponent d F) ≠ 0 := by
    rw [← actualPointHomogeneousPolynomial_coe,MvPolynomial.coeff_coe]
    exact ha
  exact MvPowerSeries.isHomogeneous_homogeneousComponent F d hc

/-- The entire actual exceptional restriction equals the true finite dehomogenized initial polynomial class. -/
theorem actual_point_normalized_member_congr_dehomogenization (e : Fin n) (b : Fin n → ℂ)
    (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ d) :
    actualNormalizedFormalMember Set.univ e (mem_univ e) b d F hF-
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d F) : MvPowerSeries (Fin n) ℂ) ∈
        Ideal.span {MvPowerSeries.X e} := by
  obtain ⟨hP,hcongr⟩ := actual_point_normalized_member_congr_homogeneous_polynomial e b d F hF
  have hn : actualNormalizedFormalMember Set.univ e (mem_univ e) b d
      (actualPointHomogeneousPolynomial d F) hP=
        (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d F) : MvPowerSeries (Fin n) ℂ) := by
    symm
    apply actualNormalizedFormalMember_unique
    exact (actualFormalBlowup_homogeneous_polynomial e b _ d
      (actualPointHomogeneousPolynomial_isHomogeneous d F)).symm
  rwa [hn] at hcongr

end
end Hironaka.HironakaActualPointDehomogenizedInitial
