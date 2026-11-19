import Hironaka.Resolution.HironakaActualHistoricalBlowupSupportedDivision
import Hironaka.Resolution.HironakaActualHistoricalNormalizedSupport

/-! Actual marked normalization itself produces pure-essential leading
agreement. Genuine target marked orders therefore suffice for whole
historical frames and ENTIRE ideal supported division, before target HS. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalNormalizedLeadingFrames
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualCanonicalBlockJacobian
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualNormalizedBlowupDerivative HironakaActualHistoricalNormalizedSupport
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalFormalSupportedDivision
  HironakaActualHistoricalBlowupSupportedDivision HironakaActualCauchyMonomialDivision
  HironakaActualOriginalFormalHSTransfer

variable {n k : ℕ}

/-- Every pure nonpivot normal coefficient at the ACTUAL mark is retained
by the SAME normalization, for arbitrary chart parameter and whole series. -/
theorem actual_normalized_pure_top_coefficient
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F∈actualFormalCoordinateIdeal n A^μ)
    (α : Fin n →₀ ℕ) (hα : (↑α.support : Set (Fin n))⊆A\{e})
    (hDegree : normalExponentDegree α=μ) :
    MvPowerSeries.coeff α (actualNormalizedFormalMember A e he b μ F hF)=MvPowerSeries.coeff α F := by
  have hαe : (↑α.support : Set (Fin n))⊆({e} : Set (Fin n))ᶜ:=fun i hi=>(hα hi).2
  have hDeriv:=congrArg (actualFormalMultiDerivative α)
    (actualNormalizedFormalMember_spec A e he b μ F hF)
  rw [actualFormalMultiDerivative_exceptional_mul e μ α hαe,
    actualFormalMultiDerivative_blowup A e b α hα F,hDegree] at hDeriv
  have hCancel:=mul_left_cancel₀ (pow_ne_zero μ (actualFormalExceptional_ne_zero e)) hDeriv
  have hc:=congrArg MvPowerSeries.constantCoeff hCancel
  rw [constantCoeff_actualFormalMultiDerivative,constantCoeff_actualFormalBlowup,
    constantCoeff_actualFormalMultiDerivative] at hc
  exact mul_right_cancel₀ (actualExponentFactorial_ne_zero α) hc

/-- Actual TARGET MARKS ALONE, together with the real source historical
laws/centre powers and free pivot, produce whole target frames and ENTIRE
old-supported division. Pure-leading agreement is internally derived. -/
theorem actual_normalized_whole_supported_division_of_marks
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (A B : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀j i,i∉B → wordExponent (w j) i=0) (hBA : B⊆A\{e})
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w j)))
    (hTargetMarked : ∀j,actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w j))) :
    (∀q,Function.Bijective (historicalWholeJetMap w (fun j=>actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)) q)) ∧
    HistoricalWholeSupportedDivision w (fun j=>actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)) := by
  apply actual_normalized_whole_supported_division_of_marks_and_pure_leading
    w g hmarked hwhole hSupported A B e he b hHeads hBA hcentre hTargetMarked
  intro j α hDegree hPure
  have hα : (↑α.support : Set (Fin n))⊆A\{e}:=by
    intro i hi
    apply hBA
    by_contra hiB
    exact (Finsupp.mem_support_iff.mp hi) (hPure i hiB)
  exact actual_normalized_pure_top_coefficient A e he b _ (g j) (hcentre j) α hα hDegree

end
end Hironaka.HironakaActualHistoricalNormalizedLeadingFrames
