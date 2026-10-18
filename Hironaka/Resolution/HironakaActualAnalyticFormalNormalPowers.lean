/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients

/-! Every genuine formal normal power contracts to the entire original analytic normal power. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticFormalNormalPowers
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalFormalTaylor
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualFormalCoordinatePowerDivision

/-- The literal genuine dimension reassociation preserves the original Taylor embedding's injectivity. -/
theorem actualUnshiftedTaylorAlgHom_injective (n : ℕ) :
    Function.Injective (actualUnshiftedTaylorAlgHom n) := by
  have hc (m : ℕ) (e : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (hf : Function.Injective f) :
      Function.Injective (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) e) f : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) := by
    subst m
    exact hf
  exact hc (0+n) (Nat.zero_add n) (originalTaylorAlgHom n) (originalTaylorAlgHom_injective n)

/-- The whole analytic normal ideal power is exactly the kernel of ALL actual low relative coefficient germs. -/
theorem mem_normalIdeal_pow_iff_actual_relative_coefficients_zero (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    g ∈ normalIdeal d t ^ q ↔ ∀ γ : Fin t →₀ ℕ,
      normalExponentDegree γ < q → actualNormalAnalyticCoefficientGerm d t g γ=0 := by
  constructor
  · intro hg γ hγ
    have hm : normalPolynomialEval d t (actualNormalTaylorPolynomial d t q g) ∈ normalIdeal d t ^ q := by
      have he : normalPolynomialEval d t (actualNormalTaylorPolynomial d t q g)=
          g-(g-normalPolynomialEval d t (actualNormalTaylorPolynomial d t q g)) := by ring
      rw [he]
      exact Ideal.sub_mem _ hg (actualNormalTaylorPolynomial_remainder d t q g)
    have hz := coefficient_eq_zero_of_normalPolynomialEval_mem d t q _ γ hγ hm
    rwa [actualNormalTaylorPolynomial_coefficient_eq_germ d t q g γ hγ] at hz
  · intro hc
    have hp : actualNormalTaylorPolynomial d t q g=0 := by
      apply MvPolynomial.ext
      intro γ
      rw [MvPolynomial.coeff_zero]
      by_cases hγ : normalExponentDegree γ < q
      · rw [actualNormalTaylorPolynomial_coefficient_eq_germ d t q g γ hγ]
        exact hc γ hγ
      · exact actualNormalTaylorPolynomial_coefficient_high d t q g γ (by omega)
    have hm := actualNormalTaylorPolynomial_remainder d t q g
    rwa [hp,map_zero,sub_zero] at hm

/-- Genuine original analytic normal powers and genuine formal normal powers have EXACTLY the same original members. -/
theorem mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    g ∈ normalIdeal d t ^ q ↔ actualUnshiftedTaylorAlgHom (d+t) g ∈
      actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) ^ q := by
  constructor
  · intro hg
    have hm := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (d+t)).toRingHom hg
    rwa [Ideal.map_pow,map_normalIdeal_originalTaylor] at hm
  · intro hg
    apply (mem_normalIdeal_pow_iff_actual_relative_coefficients_zero d t q g).mpr
    intro γ hγ
    apply actualUnshiftedTaylorAlgHom_injective d
    rw [map_zero,← actualFormalNormalCoefficient_actualTaylor]
    apply MvPowerSeries.ext
    intro β
    change MvPowerSeries.coeff (actualJoinedExponent β γ) (actualUnshiftedTaylorAlgHom (d+t) g)=
      MvPowerSeries.coeff β 0
    rw [map_zero]
    exact (mem_actualFormalCoordinateIdeal_pow_iff _ q _).mp hg _
      (by rw [actualJoinedExponent_normal_weight];exact hγ)

/-- Equality of the ENTIRE inverse-image ideals, for every degree and both actual coordinate blocks. -/
theorem comap_actual_formal_normal_pow_eq_original_normal_pow (d t q : ℕ) :
    Ideal.comap (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
      (actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t) ^ q)=
      normalIdeal d t ^ q := by
  ext g
  exact (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t q g).symm

end
end Hironaka.HironakaActualAnalyticFormalNormalPowers
