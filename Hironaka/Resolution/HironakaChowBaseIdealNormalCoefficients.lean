import Hironaka.Resolution.HironakaActualSplitAnalyticCoefficients
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Hironaka.Analytic.HolomorphicGermPointTruncationClosure
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers

/-! Actual whole base-ideal extension is detected by EVERY original analytic
normal coefficient. Genuine finite normal remainders and native Noetherian
LOCAL Krull on the actual quotient module supply the reverse implication.
Blueprint FIRST: `hironaka-g10-base-ideal-normal-coefficients.tex`. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaChowBaseIdealNormalCoefficients
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualSplitAnalyticCoefficients HironakaHolomorphicJetChartInvariance
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalFormalTaylor
  HolomorphicGermPointTruncationClosure HironakaActualAnalyticFormalNormalPowers

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

private def coefficientLinearMap (gamma : Fin t →₀ ℕ) :
    HolGerm (ComplexModel (d+t)) →ₗ[HolGerm (ComplexModel d)] HolGerm (ComplexModel d) where
  toFun := fun f => actualNormalAnalyticCoefficientGerm d t f gamma
  map_add' f g := by
    apply actualUnshiftedTaylorAlgHom_injective d
    rw [map_add, ← actualFormalNormalCoefficient_actualTaylor,
      ← actualFormalNormalCoefficient_actualTaylor, ← actualFormalNormalCoefficient_actualTaylor]
    apply MvPowerSeries.ext
    intro beta
    change MvPowerSeries.coeff (actualJoinedExponent beta gamma)
      (actualUnshiftedTaylorAlgHom (d+t) (f+g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' a f := by
    change actualNormalAnalyticCoefficientGerm d t (tangentPullback d t a * f) gamma =
      a * actualNormalAnalyticCoefficientGerm d t f gamma
    exact actualNormalAnalyticCoefficientGerm_tangent_mul d t a f gamma

/-- EVERY genuine original A-valued normal coefficient detects membership
in the literal actual base-ideal extension, including both unit ideals and
empty coordinate blocks. No separatedness or completion packet is input. -/
theorem mem_extended_base_ideal_iff_all_normal_coefficients
    (a : Ideal (HolGerm (ComplexModel d))) (f : HolGerm (ComplexModel (d+t))) :
    f ∈ Ideal.map (tangentPullback d t).toRingHom a ↔
      ∀ gamma, actualNormalAnalyticCoefficientGerm d t f gamma ∈ a := by
  constructor
  · intro hf gamma
    let : IsNoetherianRing (HolGerm (ComplexModel d)) := isNoetherianRing_holGerm_euclidean d
    obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian a)
    have hgi (i : Fin r) : g i ∈ a := hg ▸ Submodule.subset_span ⟨i, rfl⟩
    rw [← hg, Ideal.map_span, ← Set.range_comp] at hf
    obtain ⟨H, hH⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
    change coefficientLinearMap d t gamma f ∈ a
    rw [← hH, map_sum]
    apply Ideal.sum_mem
    intro i _
    change actualNormalAnalyticCoefficientGerm d t
      (H i * tangentPullback d t (g i)) gamma ∈ a
    rw [mul_comm, actualNormalAnalyticCoefficientGerm_tangent_mul]
    exact Ideal.mul_mem_right _ _ (hgi i)
  · intro hCoeff
    apply (mem_iff_mem_all_point_truncations (d+t)
      (Ideal.map (tangentPullback d t).toRingHom a) f).mpr
    intro q
    let P := actualNormalTaylorPolynomial d t q f
    have hPc (gamma : Fin t →₀ ℕ) : MvPolynomial.coeff gamma P ∈ a := by
      change MvPolynomial.coeff gamma (actualNormalTaylorPolynomial d t q f) ∈ a
      by_cases hLow : normalExponentDegree gamma < q
      · rw [actualNormalTaylorPolynomial_coefficient_eq_germ d t q f gamma hLow]
        exact hCoeff gamma
      · rw [actualNormalTaylorPolynomial_coefficient_high d t q f gamma (by omega)]
        exact a.zero_mem
    have hP : normalPolynomialEval d t P ∈ Ideal.map (tangentPullback d t).toRingHom a := by
      rw [P.as_sum, map_sum]
      apply Ideal.sum_mem
      intro gamma _
      rw [normalPolynomialEval_monomial]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem (tangentPullback d t).toRingHom (hPc gamma))
    have hNormal : normalIdeal d t ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply (HolGerm.mem_maximalIdeal_iff _).mpr
      rfl
    have hRemainder : f - normalPolynomialEval d t P ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q :=
      (pow_le_pow_left' hNormal q) (actualNormalTaylorPolynomial_remainder d t q f)
    have hSum : normalPolynomialEval d t P + (f-normalPolynomialEval d t P) ∈
        Ideal.map (tangentPullback d t).toRingHom a ⊔
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t))) ^ q :=
      Ideal.add_mem _ (Submodule.mem_sup_left hP) (Submodule.mem_sup_right hRemainder)
    convert hSum using 1
    ring

end
end Hironaka.HironakaChowBaseIdealNormalCoefficients
