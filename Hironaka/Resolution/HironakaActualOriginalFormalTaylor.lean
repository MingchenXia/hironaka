/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalTaylorPolynomial
import Mathlib.RingTheory.MvPowerSeries.Basic

/-! The genuine original Taylor algebra embedding uses ACTUAL formal convolution. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOriginalFormalTaylor
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaActualOriginalTaylorPolynomial

/-- The true original constants have their genuine constant polynomial at EVERY actual truncation. -/
theorem originalTaylorPolynomial_constant (n k : ℕ) (c : ℂ) :
    originalTaylorPolynomial n k (HolGerm.constHom c)=MvPolynomial.C c := by
  classical
  apply Eq.symm
  apply originalTaylorPolynomial_unique n k (HolGerm.constHom c) (MvPolynomial.C c)
  · intro α hα
    by_cases hz : α=0
    · subst α
      simp [normalExponentDegree] at hα
    · simp [MvPolynomial.coeff_C,Ne.symm hz]
  · have he : originalPolynomialEval n (MvPolynomial.C c)=HolGerm.constHom c := by
      rw [originalPolynomialEval,MvPolynomial.aeval_C]
      rfl
    rw [he,sub_self]
    exact Ideal.zero_mem _

/-- Every original coordinate retains its literal original linear polynomial whenever degree one is retained. -/
theorem originalTaylorPolynomial_coordinate (n k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    originalTaylorPolynomial n k (normalCoordinate 0 n i)=MvPolynomial.X i := by
  classical
  apply Eq.symm
  apply originalTaylorPolynomial_unique n k (normalCoordinate 0 n i) (MvPolynomial.X i)
  · intro α hα
    by_cases he : α=Finsupp.single i 1
    · have hd : normalExponentDegree (Finsupp.single i 1)=1 := by simp [normalExponentDegree]
      rw [he,hd] at hα
      omega
    · simp [MvPolynomial.coeff_X,Ne.symm he]
  · rw [originalPolynomialEval,MvPolynomial.aeval_X,sub_self]
    exact Ideal.zero_mem _

/-- The actual original stabilized coefficients, in the GENUINE multivariate formal-series ring. -/
def originalTaylorSeries (n : ℕ) (g : HolGerm (ComplexModel (0+n))) : MvPowerSeries (Fin n) ℂ :=
  originalTaylorCoefficientMap n g

/-- Every genuine formal coefficient is precisely the independently constructed original complex coefficient. -/
theorem originalTaylorSeries_coefficient (n : ℕ) (g : HolGerm (ComplexModel (0+n))) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (originalTaylorSeries n g)=originalTaylorCoefficientMap n g α := rfl

/-- Actual original constants become actual constant formal series. -/
theorem originalTaylorSeries_constant (n : ℕ) (c : ℂ) :
    originalTaylorSeries n (HolGerm.constHom c)=MvPowerSeries.C c := by
  classical
  apply MvPowerSeries.ext
  intro α
  rw [originalTaylorSeries_coefficient,originalTaylorCoefficientMap_eq_coefficient n (normalExponentDegree α) _ α (by omega),
    originalTaylorPolynomial_constant]
  simp only [MvPolynomial.coeff_C,MvPowerSeries.coeff_C,eq_comm]

/-- EACH original coordinate becomes the corresponding genuine formal variable. -/
theorem originalTaylorSeries_coordinate (n : ℕ) (i : Fin n) :
    originalTaylorSeries n (normalCoordinate 0 n i)=MvPowerSeries.X i := by
  classical
  apply MvPowerSeries.ext
  intro α
  rw [originalTaylorSeries_coefficient,originalTaylorCoefficientMap_eq_coefficient n (normalExponentDegree α+1) _ α (by omega),
    originalTaylorPolynomial_coordinate n _ (by omega)]
  simp only [MvPolynomial.coeff_X,MvPowerSeries.coeff_X,eq_comm]

private theorem exponentDegree_add {n : ℕ} (α β : Fin n →₀ ℕ) :
    normalExponentDegree (α+β)=normalExponentDegree α+normalExponentDegree β := by
  simp [normalExponentDegree,Finset.sum_add_distrib]

/-- Genuine WHOLE original Taylor remainders force the ACTUAL formal coefficient convolution. -/
theorem originalTaylorCoefficientMap_mul (n : ℕ) (g h : HolGerm (ComplexModel (0+n)))
    (α : Fin n →₀ ℕ) :
    originalTaylorCoefficientMap n (g*h) α =
      ∑ p ∈ Finset.antidiagonal α, originalTaylorCoefficientMap n g p.1*originalTaylorCoefficientMap n h p.2 := by
  classical
  let k := normalExponentDegree α
  let A := originalTaylorPolynomial n k g
  let B := originalTaylorPolynomial n k h
  let C := originalTaylorPolynomial n k (g*h)
  let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))
  have hc : originalPolynomialEval n (C-A*B) ∈ m^(k+1) := by
    rw [map_sub,map_mul]
    have he : originalPolynomialEval n C-originalPolynomialEval n A*originalPolynomialEval n B =
        -(g*h-originalPolynomialEval n C)+g*(h-originalPolynomialEval n B)+
          (g-originalPolynomialEval n A)*originalPolynomialEval n B := by ring
    rw [he]
    exact Ideal.add_mem _ (Ideal.add_mem _
      ((m^(k+1)).neg_mem (originalTaylorPolynomial_remainder n k (g*h)))
      (Ideal.mul_mem_left _ g (originalTaylorPolynomial_remainder n k h)))
      (Ideal.mul_mem_right _ _ (originalTaylorPolynomial_remainder n k g))
  have he := originalPolynomial_coefficient_eq_zero_of_eval_mem n (k+1) _ α (by dsimp [k]; omega) hc
  rw [MvPolynomial.coeff_sub,sub_eq_zero] at he
  rw [originalTaylorCoefficientMap_eq_coefficient n k (g*h) α (by dsimp [k]; omega)]
  change MvPolynomial.coeff α C=_
  rw [he,MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum : p.1+p.2=α := Finset.mem_antidiagonal.mp hp
  have hd : normalExponentDegree p.1+normalExponentDegree p.2=k := by
    rw [← exponentDegree_add,hsum]
  change MvPolynomial.coeff p.1 (originalTaylorPolynomial n k g)*
      MvPolynomial.coeff p.2 (originalTaylorPolynomial n k h)=_
  rw [← originalTaylorCoefficientMap_eq_coefficient n k g p.1 (by omega),
    ← originalTaylorCoefficientMap_eq_coefficient n k h p.2 (by omega)]

/-- This is multiplication in the ACTUAL formal power-series ring, with its genuine convolution. -/
theorem originalTaylorSeries_mul (n : ℕ) (g h : HolGerm (ComplexModel (0+n))) :
    originalTaylorSeries n (g*h)=originalTaylorSeries n g*originalTaylorSeries n h := by
  classical
  apply MvPowerSeries.ext
  intro α
  rw [MvPowerSeries.coeff_mul,originalTaylorSeries_coefficient,originalTaylorCoefficientMap_mul]
  rfl

/-- Addition is the original additive operation on both actual rings. -/
theorem originalTaylorSeries_add (n : ℕ) (g h : HolGerm (ComplexModel (0+n))) :
    originalTaylorSeries n (g+h)=originalTaylorSeries n g+originalTaylorSeries n h :=
  (originalTaylorCoefficientMap n).map_add g h

/-- The same actual series map is a genuine ORIGINAL complex algebra homomorphism. -/
def originalTaylorAlgHom (n : ℕ) :
    HolGerm (ComplexModel (0+n)) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun := originalTaylorSeries n
  map_zero' := (originalTaylorCoefficientMap n).map_zero
  map_one' := by simpa only [map_one] using originalTaylorSeries_constant n 1
  map_add' := originalTaylorSeries_add n
  map_mul' := originalTaylorSeries_mul n
  commutes' c := by
    change originalTaylorSeries n (HolGerm.constHom c)=MvPowerSeries.C c
    exact originalTaylorSeries_constant n c

/-- EVERY original coefficient has its actual original complex value under the genuine algebra map. -/
theorem originalTaylorAlgHom_coefficient (n : ℕ) (g : HolGerm (ComplexModel (0+n))) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (originalTaylorAlgHom n g)=originalTaylorCoefficientMap n g α := rfl

/-- The genuine formal-series algebra homomorphism is faithful on the ENTIRE original germ ring. -/
theorem originalTaylorAlgHom_injective (n : ℕ) : Function.Injective (originalTaylorAlgHom n) :=
  originalTaylorCoefficientMap_injective n

/-- Each SAME original coordinate germ has exactly its corresponding genuine formal variable image. -/
theorem originalTaylorAlgHom_coordinate (n : ℕ) (i : Fin n) :
    originalTaylorAlgHom n (normalCoordinate 0 n i)=MvPowerSeries.X i :=
  originalTaylorSeries_coordinate n i

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- ACTUAL original maximal powers have exactly the genuine lower formal-coefficient kernel. -/
theorem mem_original_maximal_pow_iff_formal_coefficients_zero (n q : ℕ)
    (g : HolGerm (ComplexModel (0+n))) :
    g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q ↔
      ∀ α : Fin n →₀ ℕ, normalExponentDegree α < q → MvPowerSeries.coeff α (originalTaylorAlgHom n g)=0 := by
  constructor
  · intro hg α hα
    rw [originalTaylorAlgHom_coefficient,
      originalTaylorCoefficientMap_eq_coefficient n (normalExponentDegree α) g α (by omega)]
    have hsmall : g ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (normalExponentDegree α+1) :=
      Ideal.pow_le_pow_right (by omega) hg
    have hrem := originalTaylorPolynomial_remainder n (normalExponentDegree α) g
    have hp : originalPolynomialEval n (originalTaylorPolynomial n (normalExponentDegree α) g) ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (normalExponentDegree α+1) := by
      have he : originalPolynomialEval n (originalTaylorPolynomial n (normalExponentDegree α) g)=
          g-(g-originalPolynomialEval n (originalTaylorPolynomial n (normalExponentDegree α) g)) := by ring
      rw [he]
      exact Ideal.sub_mem _ hsmall hrem
    exact originalPolynomial_coefficient_eq_zero_of_eval_mem n _ _ α (by omega) hp
  · intro hc
    cases q with
    | zero => simp
    | succ k =>
      have hp : originalTaylorPolynomial n k g=0 := by
        ext α
        by_cases hα : normalExponentDegree α < k+1
        · rw [← originalTaylorCoefficientMap_eq_coefficient n k g α hα]
          exact hc α hα
        · exact originalTaylorPolynomial_coefficient_high n k g α (by omega)
      have hrem := originalTaylorPolynomial_remainder n k g
      rwa [hp,map_zero,sub_zero] at hrem

end
end Hironaka.HironakaActualOriginalFormalTaylor
