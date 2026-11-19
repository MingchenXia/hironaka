import Hironaka.Resolution.HironakaChowFibreRemainderWeightedFiltration
import Hironaka.Resolution.HironakaActualHistoricalCentreFilteredDivision

/-! Fixed actual normal coefficients of the SAME native remainder gain
base-maximal order on genuine high normal powers. No normal-adic claim.
BP FIRST: hironaka-g10-fibre-remainder-coefficient-orders.tex. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaChowFibreRemainderCoefficientOrders
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualJointBaseFibre HironakaActualFiniteDegLexWeights
  HironakaActualCoefficientPresentationCentrePower HironakaActualRelativeCoefficientGerms
  HironakaActualRelativeTaylorCoefficients HironakaActualAnalyticFormalNormalPowers
  HironakaActualFormalCoordinatePowerDivision HironakaActualCentreJointJets
  HironakaChowFibreLiftWeightedFactors HironakaChowFibreLiftUniformTails
  HironakaChowOriginalFibreSupportedDivision HironakaChowFibreSupportModules
  HironakaChowFibreDivisionRemainder HironakaChowFibreRemainderWeightedFiltration
  HironakaActualHistoricalCentreFilteredDivision

private theorem weighted_joined (d t L : ℕ) (w : Fin t → ℕ)
    (β : Fin d →₀ ℕ) (γ : Fin t →₀ ℕ) :
    weightedDegree (extendedWeight d t L w) (actualJoinedExponent β γ) =
      L * normalExponentDegree β + weightedDegree w γ := by
  simp [weightedDegree, normalExponentDegree, Fin.sum_univ_add, extendedWeight,
    actualJoinedExponent, ← Finset.mul_sum]

private theorem normal_degree_le_weighted (d t L : ℕ) (w : Fin t → ℕ)
    (hw : ∀ i, 1 ≤ w i) (α : Fin (d+t) →₀ ℕ) :
    normalExponentDegree (actualNormalExponent α) ≤ weightedDegree (extendedWeight d t L w) α := by
  have hNormal : normalExponentDegree (actualNormalExponent α) ≤
      weightedDegree w (actualNormalExponent α) := by
    apply Finset.sum_le_sum
    intro i _
    calc
      actualNormalExponent α i = 1 * actualNormalExponent α i := by omega
      _ ≤ w i * actualNormalExponent α i := Nat.mul_le_mul_right _ (hw i)
  calc
    normalExponentDegree (actualNormalExponent α) ≤
        L * normalExponentDegree (actualTangentExponent α) + weightedDegree w (actualNormalExponent α) :=
      hNormal.trans (Nat.le_add_left _ _)
    _ = weightedDegree (extendedWeight d t L w) α := by
      rw [← weighted_joined, actualJoinedExponent_split]

private theorem weighted_coeff_zero_of_normal_power (d t L : ℕ) (w : Fin t → ℕ)
    (hw : ∀ i, 1 ≤ w i) (g : HolGerm (ComplexModel (d+t))) (q : ℕ)
    (hg : g ∈ normalIdeal d t ^ q) :
    ∀ α, weightedDegree (extendedWeight d t L w) α < q →
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t) g) = 0 := by
  intro α hα
  have hFormal := (mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow d t q g).mp hg
  apply (mem_actualFormalCoordinateIdeal_pow_iff (actualTangentCentreVariables d t) q _).mp hFormal α
  have hWeight : Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) α =
      normalExponentDegree (actualNormalExponent α) := by
    calc
      Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) α =
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t))
            (actualJoinedExponent (actualTangentExponent α) (actualNormalExponent α)) :=
        congrArg _ (actualJoinedExponent_split α).symm
      _ = _ := actualJoinedExponent_normal_weight d t _ _
  rw [hWeight]
  exact lt_of_le_of_lt (normal_degree_le_weighted d t L w hw α) hα

variable (d t : ℕ)
local notation "A" => HolGerm (ComplexModel d)
local notation "S" => HolGerm (ComplexModel (d+t))
local instance : Algebra A S := tangentAlgebra d t

/-- Fixed normal coefficients of the SAME actual remainder acquire true
base-maximal order. All original weights and the native remainder are retained. -/
theorem coefficient_remainder_mem_base_maximal_pow (I : Ideal S)
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[A] S)
    (he : ∀ z, e z = supportedReassembly d t I P z)
    (g : S) (q r : ℕ) (γ : Fin t →₀ ℕ)
    (hg : g ∈ normalIdeal d t ^ q)
    (hBound : P.baseWeight * r + weightedDegree (degLexWeight t P.fibre.degreeBound) γ ≤ q) :
    actualNormalAnalyticCoefficientGerm d t (divisionRemainder d t I e g : S) γ ∈
      IsLocalRing.maximalIdeal A ^ r := by
  have hw (i : Fin t) : 1 ≤ degLexWeight t P.fibre.degreeBound i :=
    Nat.succ_le_iff.mpr (degLexWeight_positive t P.fibre.degreeBound i)
  have hR := (produced_fibre_division_weighted_filtration d t I P e he g q
    (weighted_coeff_zero_of_normal_power d t P.baseWeight _ hw g q hg)).2
  apply (actual_maximal_power_iff_formal_coefficients_zero d r _).mpr
  intro β hβ
  rw [← actualFormalNormalCoefficient_actualTaylor]
  change MvPowerSeries.coeff (actualJoinedExponent β γ)
    (actualUnshiftedTaylorAlgHom (d+t) (divisionRemainder d t I e g : S)) = 0
  apply hR
  rw [weighted_joined]
  have hMul := Nat.mul_lt_mul_of_pos_left hβ P.baseWeight_pos
  omega

end
end Hironaka.HironakaChowFibreRemainderCoefficientOrders
