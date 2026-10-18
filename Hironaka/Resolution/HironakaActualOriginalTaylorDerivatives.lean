/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalFormalTaylor
import Mathlib.RingTheory.MvPowerSeries.Derivative

/-! Entire actual original Taylor series commute with genuine analytic coordinate differentiation. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualOriginalTaylorDerivatives
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalActualBaseJetDimension
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor

/-- Actual analytic differentiation and true polynomial differentiation agree in the whole original germ ring. -/
theorem originalDerivative_polynomialEval (n : ℕ) (i : Fin n) (P : MvPolynomial (Fin n) ℂ) :
    iteratedDerivativeGerm [normalVector 0 n i] (originalPolynomialEval n P)=
      originalPolynomialEval n (MvPolynomial.pderiv i P) := by
  let := tangentAlgebra 0 n
  change normalDerivation 0 n i (originalPolynomialEval n P)=_
  rw [← normalPolynomialEval_original_coefficient_lift n P,
    normalDerivation_polynomialEval,MvPolynomial.pderiv_map,
    normalPolynomialEval_original_coefficient_lift]

private theorem originalTaylor_polynomial_coefficient (n : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (originalTaylorAlgHom n (originalPolynomialEval n P))=MvPolynomial.coeff α P := by
  let k := normalExponentDegree α
  have hr : originalPolynomialEval n (P-originalTaylorPolynomial n k (originalPolynomialEval n P)) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) := by
    rw [map_sub]
    exact originalTaylorPolynomial_remainder n k (originalPolynomialEval n P)
  have hc := originalPolynomial_coefficient_eq_zero_of_eval_mem n (k+1) _ α (by dsimp [k];omega) hr
  rw [MvPolynomial.coeff_sub,sub_eq_zero] at hc
  rw [originalTaylorAlgHom_coefficient,
    originalTaylorCoefficientMap_eq_coefficient n k _ α (by dsimp [k];omega)]
  exact hc.symm

/-- Genuine original whole-germ Taylor expansion commutes with actual analytic coordinate differentiation. -/
theorem originalTaylorAlgHom_coordinate_derivative (n : ℕ) (i : Fin n)
    (g : HolGerm (ComplexModel (0+n))) :
    originalTaylorAlgHom n (iteratedDerivativeGerm [normalVector 0 n i] g)=
      MvPowerSeries.pderiv ℂ i (originalTaylorAlgHom n g) := by
  apply MvPowerSeries.ext
  intro α
  let k := normalExponentDegree α
  let P := originalTaylorPolynomial n (k+1) g
  let D := iteratedDerivativeGerm [normalVector 0 n i]
  have hd : D (g-originalPolynomialEval n P) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) := by
    let := tangentAlgebra 0 n
    have hr : g-originalPolynomialEval n P ∈ normalIdeal 0 n ^ ((k+1)+1) := by
      rw [zeroTangentNormalIdeal_eq_maximalIdeal]
      exact originalTaylorPolynomial_remainder n (k+1) g
    have h := normalDerivation_mem_normalIdeal_pow 0 n (k+1) i _ hr
    rw [zeroTangentNormalIdeal_eq_maximalIdeal] at h
    exact h
  have hc := (mem_original_maximal_pow_iff_formal_coefficients_zero n (k+1) _).mp hd α (by dsimp [k];omega)
  simp only [map_sub,sub_eq_zero] at hc
  have hdegree : normalExponentDegree (α+Finsupp.single i 1)<(k+1)+1 := by
    have he : normalExponentDegree (α+Finsupp.single i 1)=normalExponentDegree α+1 := by
      simp [normalExponentDegree,Finset.sum_add_distrib]
    rw [he]
    dsimp [k]
    omega
  rw [MvPowerSeries.coeff_pderiv]
  calc
    MvPowerSeries.coeff α (originalTaylorAlgHom n (D g))=
        MvPowerSeries.coeff α (originalTaylorAlgHom n (D (originalPolynomialEval n P))) := hc
    _=MvPowerSeries.coeff α (originalTaylorAlgHom n (originalPolynomialEval n (MvPolynomial.pderiv i P))) := by
      rw [show D (originalPolynomialEval n P)=originalPolynomialEval n (MvPolynomial.pderiv i P) from
        originalDerivative_polynomialEval n i P]
    _=MvPolynomial.coeff α (MvPolynomial.pderiv i P) := originalTaylor_polynomial_coefficient n _ α
    _=MvPolynomial.coeff (α+Finsupp.single i 1) P*(α i+1) := MvPolynomial.coeff_pderiv P α
    _=MvPowerSeries.coeff (α+Finsupp.single i 1) (originalTaylorAlgHom n g)*(α i+1) := by
      rw [originalTaylorAlgHom_coefficient,
        originalTaylorCoefficientMap_eq_coefficient n (k+1) g (α+Finsupp.single i 1) hdegree]

end
end Hironaka.HironakaActualOriginalTaylorDerivatives
