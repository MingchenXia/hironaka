/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalFormalTaylor
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-! Genuine formal extension/contraction of ENTIRE original holomorphic ideals. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualFormalIdealContraction
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalActualBaseJetDimension
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor
  HironakaActualWholeIdealJetDetection

/-- Original coordinate polynomial evaluation followed by actual Taylor is the GENUINE polynomial-series inclusion. -/
theorem originalTaylorAlgHom_polynomialEval (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    originalTaylorAlgHom n (originalPolynomialEval n P)=(P : MvPowerSeries (Fin n) ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [originalPolynomialEval,MvPolynomial.aeval_C,AlgHom.commutes,MvPolynomial.coe_C]
    rw [MvPowerSeries.c_eq_algebraMap]
  | add P Q hP hQ => rw [map_add,map_add,hP,hQ,MvPolynomial.coe_add]
  | mul_X P i hP =>
    rw [map_mul,map_mul,hP,originalPolynomialEval,MvPolynomial.aeval_X,
      originalTaylorAlgHom_coordinate,MvPolynomial.coe_mul,MvPolynomial.coe_X]

/-- ANY genuine formal coefficient has an internally constructed actual original polynomial germ approximation. -/
def actualFormalApproximation (n k : ℕ) (A : MvPowerSeries (Fin n) ℂ) : HolGerm (ComplexModel (0+n)) :=
  originalPolynomialEval n (MvPowerSeries.truncTotal (k+1) A)

/-- The original polynomial germ approximation retains EVERY genuine lower formal coefficient. -/
theorem actualFormalApproximation_coefficient (n k : ℕ) (A : MvPowerSeries (Fin n) ℂ)
    (α : Fin n →₀ ℕ) (hα : normalExponentDegree α < k+1) :
    MvPowerSeries.coeff α (originalTaylorAlgHom n (actualFormalApproximation n k A))=MvPowerSeries.coeff α A := by
  rw [actualFormalApproximation,originalTaylorAlgHom_polynomialEval,MvPolynomial.coeff_coe]
  apply MvPowerSeries.coeff_truncTotal
  rwa [Finsupp.degree_eq_sum]

/-- The SAME actual approximation retains the genuine coefficient of its product with ANY actual formal series. -/
theorem actualFormalApproximation_mul_coefficient (n k : ℕ) (A B : MvPowerSeries (Fin n) ℂ)
    (α : Fin n →₀ ℕ) (hα : normalExponentDegree α < k+1) :
    MvPowerSeries.coeff α (originalTaylorAlgHom n (actualFormalApproximation n k A)*B)=
      MvPowerSeries.coeff α (A*B) := by
  classical
  rw [MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hs : p.1+p.2=α := Finset.mem_antidiagonal.mp hp
  have hd : normalExponentDegree p.1+normalExponentDegree p.2=normalExponentDegree α := by
    have he := congrArg normalExponentDegree hs
    simpa only [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib] using he
  rw [actualFormalApproximation_coefficient n k A p.1 (by omega)]

/-- Literal finite formal ideal expressions give genuine original whole maximal-power representatives. -/
theorem formal_combination_actual_jet_approximation (n : ℕ) {r : ℕ}
    (G : Fin r → HolGerm (ComplexModel (0+n))) (A : Fin r → MvPowerSeries (Fin n) ℂ)
    (g : HolGerm (ComplexModel (0+n)))
    (he : originalTaylorAlgHom n g=∑ i, A i*originalTaylorAlgHom n (G i)) (k : ℕ) :
    g-∑ i, actualFormalApproximation n k (A i)*G i ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (k+1) := by
  classical
  apply (mem_original_maximal_pow_iff_formal_coefficients_zero n (k+1) _).mpr
  intro α hα
  have ht : originalTaylorAlgHom n (g-∑ i, actualFormalApproximation n k (A i)*G i)=
      originalTaylorAlgHom n g-∑ i,originalTaylorAlgHom n (actualFormalApproximation n k (A i)*G i) := by
    rw [map_sub,map_sum]
  rw [ht,map_sub,map_sum]
  have hc := congrArg (fun F : MvPowerSeries (Fin n) ℂ => MvPowerSeries.coeff α F) he
  rw [map_sum] at hc
  rw [hc]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i _
  have hmul : originalTaylorAlgHom n (actualFormalApproximation n k (A i)*G i)=
      originalTaylorAlgHom n (actualFormalApproximation n k (A i))*originalTaylorAlgHom n (G i) := map_mul _ _ _
  rw [hmul]
  exact (actualFormalApproximation_mul_coefficient n k (A i) (originalTaylorAlgHom n (G i)) α hα).symm

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- EVERY original whole ideal contracts from its ACTUAL entire formal extension, without a flatness premise. -/
theorem mem_original_ideal_iff_formal_extension (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (g : HolGerm (ComplexModel (0+n))) :
    g ∈ I ↔ originalTaylorAlgHom n g ∈ Ideal.map (originalTaylorAlgHom n).toRingHom I := by
  constructor
  · exact Ideal.mem_map_of_mem _
  · intro hg
    let := isNoetherianRing_holGerm_euclidean (0+n)
    obtain ⟨r,G,hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
    have hspan : Ideal.span (range G)=I := hG
    have hmap : Ideal.map (originalTaylorAlgHom n).toRingHom I=
        Ideal.span (range fun i => originalTaylorAlgHom n (G i)) := by
      rw [← hspan,Ideal.map_span,← Set.range_comp]
      rfl
    rw [hmap] at hg
    obtain ⟨A,hA⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
    apply (mem_original_ideal_iff_all_positive_thickenings I g).mpr
    intro k
    let p := ∑ i,actualFormalApproximation n k (A i)*G i
    have hp : p ∈ I := by
      apply Ideal.sum_mem
      intro i _
      apply Ideal.mul_mem_left
      rw [← hspan]
      exact Ideal.mem_span_range_self (x := i)
    have hrem := formal_combination_actual_jet_approximation n G A g hA.symm k
    have he : p+(g-p)=g := by abel
    rw [← he]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hp) (Ideal.mem_sup_right hrem)

/-- BOTH entire ideal directions recover the SAME original ideal from its genuine formal extension. -/
theorem comap_map_originalTaylorAlgHom (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) :
    Ideal.comap (originalTaylorAlgHom n).toRingHom (Ideal.map (originalTaylorAlgHom n).toRingHom I)=I := by
  ext g
  exact (mem_original_ideal_iff_formal_extension n I g).symm

/-- Genuine formal extension is injective on ALL original ideals. -/
theorem original_formal_ideal_extension_injective (n : ℕ) :
    Function.Injective (Ideal.map (originalTaylorAlgHom n).toRingHom) := by
  intro I J he
  have hc := congrArg (Ideal.comap (originalTaylorAlgHom n).toRingHom) he
  rwa [comap_map_originalTaylorAlgHom,comap_map_originalTaylorAlgHom] at hc

/-- The WHOLE original maximal ideal extends to the WHOLE genuine formal variable ideal. -/
theorem map_original_maximalIdeal_eq_formal_variables (n : ℕ) :
    Ideal.map (originalTaylorAlgHom n).toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))))=
      Ideal.span (range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ)) := by
  rw [← zeroTangentNormalIdeal_eq_maximalIdeal,normalIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact originalTaylorAlgHom_coordinate n i

/-- EVERY original maximal power extends to the SAME genuine formal variable-ideal power. -/
theorem map_original_maximal_pow_eq_formal_variables_pow (n q : ℕ) :
    Ideal.map (originalTaylorAlgHom n).toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)=
      (Ideal.span (range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ))) ^ q := by
  rw [Ideal.map_pow,map_original_maximalIdeal_eq_formal_variables]

/-- ALL true original ideal thickenings have exactly their genuine formal variable-power extensions. -/
theorem map_original_thickening_eq_formal_thickening (n q : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) :
    Ideal.map (originalTaylorAlgHom n).toRingHom (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)=
      Ideal.map (originalTaylorAlgHom n).toRingHom I ⊔
        (Ideal.span (range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ))) ^ q := by
  rw [Ideal.map_sup,map_original_maximal_pow_eq_formal_variables_pow]

end
end Hironaka.HironakaActualFormalIdealContraction
