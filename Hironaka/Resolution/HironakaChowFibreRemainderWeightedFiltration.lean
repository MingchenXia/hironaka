import Hironaka.Resolution.HironakaChowFibreDivisionRemainder
import Hironaka.Resolution.HironakaChowFibreLiftWeightedTailSupport
import Hironaka.Resolution.HironakaChowSupportedWeightedFiltration

/-! SAME actual original analytic division and its true weighted filtration.
The original ideal chooses one family/equivalence BEFORE all numerators
and filtration levels. No desired tail/filtration certificate is input.
Blueprint FIRST: hironaka-g10-fibre-remainder-weighted-filtration.tex. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaChowFibreRemainderWeightedFiltration
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaActualJointBaseFibre
  HironakaActualWeightedVertexSmallTails HironakaActualFiniteDegLexWeights
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticFormalNormalPowers
  HironakaChowFibreLiftWeightedFactors HironakaChowFibreLiftUniformTails
  HironakaChowOriginalFibreSupportedDivision HironakaChowFibreSupportModules
  HironakaChowFibreDivisionRemainder HironakaChowFibreLiftWeightedTailSupport
  HironakaChowSupportedWeightedFiltration HironakaActualCauchyMonomialDivision

variable (d t : ℕ)
local notation "A" => HolGerm (ComplexModel d)
local notation "S" => HolGerm (ComplexModel (d+t))
local instance : Algebra A S := tangentAlgebra d t

/-- Any SAME already produced original P/e retains the actual weighted
filtration. The strict tail and masks are derived internally. -/
theorem produced_fibre_division_weighted_filtration (I : Ideal S)
    (P : FibreLiftUniformTailData d t I)
    (e : fibreDivisionModule d t I ≃ₗ[A] S)
    (he : ∀ z, e z = supportedReassembly d t I P z) :
    let W := extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)
    ∀ (g : S) (b : ℕ),
      (∀ α, weightedDegree W α < b →
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t) g) = 0) →
      (∀ j β, weightedDegree W β + weightedDegree W (wordExponent (fibreHeadWords d t I j)) < b →
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t)
          ((e.symm g).1 j : S)) = 0) ∧
      ∀ α, weightedDegree W α < b →
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t)
          (divisionRemainder d t I e g : S)) = 0 := by
  dsimp only
  intro g b hg
  let W := extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)
  let Q := fun j => actualUnshiftedTaylorAlgHom (d+t) ((e.symm g).1 j : S)
  let R := actualUnshiftedTaylorAlgHom (d+t) (divisionRemainder d t I e g : S)
  let T := fun j => actualUnshiftedTaylorAlgHom (d+t) (P.lift (fibreEnumeration d t I j)) -
    MvPowerSeries.monomial (wordExponent (fibreHeadWords d t I j)) 1
  have hNative := he (e.symm g)
  rw [e.apply_symm_apply] at hNative
  change g = (∑ j, ((e.symm g).1 j : S) * P.lift (fibreEnumeration d t I j)) +
    ((e.symm g).2 : S) at hNative
  have hDivision : actualUnshiftedTaylorAlgHom (d+t) g =
      (∑ j, Q j * (MvPowerSeries.monomial (wordExponent (fibreHeadWords d t I j)) 1 + T j)) + R := by
    have hMonomial (j) : MvPowerSeries.monomial (wordExponent (fibreHeadWords d t I j)) 1 + T j =
        actualUnshiftedTaylorAlgHom (d+t) (P.lift (fibreEnumeration d t I j)) := by
      dsimp only [T]
      ring
    simp_rw [hMonomial]
    change actualUnshiftedTaylorAlgHom (d+t) g =
      (∑ j, actualUnshiftedTaylorAlgHom (d+t) ((e.symm g).1 j : S) *
        actualUnshiftedTaylorAlgHom (d+t) (P.lift (fibreEnumeration d t I j))) +
      actualUnshiftedTaylorAlgHom (d+t) ((e.symm g).2 : S)
    simpa only [map_add, map_sum, map_mul] using
      congrArg (actualUnshiftedTaylorAlgHom (d+t)) hNative
  have hTail : ∀ j γ, weightedDegree W γ ≤ weightedDegree W (wordExponent (fibreHeadWords d t I j)) →
      MvPowerSeries.coeff γ (T j) = 0 := by
    intro j γ hγ
    have hBound : weightedDegree W γ ≤ weightedDegree W
        (actualJoinedExponent (0 : Fin d →₀ ℕ)
          (fibreEnumeration d t I j).val) := by
      simpa only [fibreHeadWords, wordExponent_wordOfExponent] using hγ
    simpa only [T, fibreHeadWords, wordExponent_wordOfExponent] using
      coeff_lift_tail_eq_zero_of_weight_le P (fibreEnumeration d t I j) γ hBound
  exact weighted_filtration_of_supported_division (fibreHeadWords d t I) W
    (actualUnshiftedTaylorAlgHom (d+t) g) Q T R hDivision
    (fun j => (mem_fibreQuotientModule_iff d t I j _).mp ((e.symm g).1 j).property)
    ((mem_fibreRemainderModule_iff d t I _).mp (divisionRemainder d t I e g).property)
    hTail b hg

/-- ORIGINAL I alone chooses P/e BEFORE EVERY original numerator and level. -/
theorem exists_original_fibre_weighted_division (I : Ideal S) :
    ∃ (P : FibreLiftUniformTailData d t I) (e : fibreDivisionModule d t I ≃ₗ[A] S),
      (∀ z, e z = supportedReassembly d t I P z) ∧
      let W := extendedWeight d t P.baseWeight (degLexWeight t P.fibre.degreeBound)
      ∀ (g : S) (b : ℕ),
        (∀ α, weightedDegree W α < b →
          MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t) g) = 0) →
        (∀ j β, weightedDegree W β + weightedDegree W (wordExponent (fibreHeadWords d t I j)) < b →
          MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t)
            ((e.symm g).1 j : S)) = 0) ∧
        ∀ α, weightedDegree W α < b →
          MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom (d+t)
            (divisionRemainder d t I e g : S)) = 0 := by
  obtain ⟨P, e, he⟩ := exists_original_fibre_linear_division d t I
  exact ⟨P, e, he, produced_fibre_division_weighted_filtration d t I P e he⟩

end
end Hironaka.HironakaChowFibreRemainderWeightedFiltration
