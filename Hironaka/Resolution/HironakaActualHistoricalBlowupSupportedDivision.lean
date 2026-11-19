import Hironaka.Resolution.HironakaActualHistoricalNormalizedQuotients
import Hironaka.Resolution.HironakaActualPolynomialBlowupLift

/-! Source filtered division and ACTUAL polynomial denominator clearing
produce whole supported division of the SAME normalized family BEFORE
target HS. Target whole frames are derived from genuine marks and finite
pure-essential leading agreement, not supplied as a certificate. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalBlowupSupportedDivision
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualHistoricalWholeJetFrames
  HironakaActualHistoricalPrefixJetFrames HironakaActualHistoricalFormalSupportedDivision
  HironakaActualHistoricalCentreFilteredDivision HironakaActualHistoricalNormalizedQuotients
  HironakaActualPolynomialBlowupLift
  HironakaActualCauchyMonomialDivision HironakaActualOriginalFormalHSTransfer

variable {n k : ℕ}

private theorem pivot_mem (A : Set (Fin n)) (e : Fin n) (he : e∈A) :
    (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)∈actualFormalCoordinateIdeal n A :=
  Ideal.subset_span ⟨e,he,rfl⟩

private theorem blowup_pivot (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ) :
    actualFormalBlowup A e b (MvPowerSeries.X e)=MvPowerSeries.X e := by
  rw [actualFormalBlowup_X]
  simp [actualFormalBlowupCoordinates,he]

/-- Every target polynomial multiple has genuine SAME normalized-family
division in the EXACT original support regions; no target HS is used. -/
theorem actual_normalized_polynomial_multiple_supported_division
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀j : Fin k,(↑(wordExponent (w j)).support : Set (Fin n))⊆A\{e})
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w j)))
    (j : Fin k) (P : MvPolynomial (Fin n) ℂ) :
    ∃Q : Fin k → MvPowerSeries (Fin n) ℂ,
      (P : MvPowerSeries (Fin n) ℂ)*actualNormalizedFormalMember A e he b
          (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)=
        ∑i,Q i*actualNormalizedFormalMember A e he b
          (normalExponentDegree (wordExponent (w i))) (g i) (hcentre i) ∧
      ∀i β,historicalOwner w (β+wordExponent (w i))≠some i → MvPowerSeries.coeff β (Q i)=0 := by
  obtain ⟨N,H,hH,hLift⟩:=exists_actual_polynomial_blowup_lift A e he b P
  let μ:=fun i=>normalExponentDegree (wordExponent (w i))
  let M:=Finset.univ.sup μ
  have hμ (i : Fin k) : μ i≤M:=Finset.le_sup (Finset.mem_univ i)
  let F:=(H : MvPowerSeries (Fin n) ℂ)*(MvPowerSeries.X e)^(M-μ j)*g j
  have hF : F∈actualFormalCoordinateIdeal n A^(N+M) := by
    have hm:=Ideal.mul_mem_mul
      (Ideal.mul_mem_mul hH (Ideal.pow_mem_pow (pivot_mem A e he) (M-μ j))) (hcentre j)
    rw [←pow_add,←pow_add,Nat.add_assoc,Nat.sub_add_cancel (hμ j)] at hm
    exact hm
  have hI : F∈Ideal.span (range g):=
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)
  let G:=fun i=>actualNormalizedFormalMember A e he b (μ i) (g i) (hcentre i)
  have hσ : actualFormalBlowup A e b F=(MvPowerSeries.X e)^(N+M)*((P : MvPowerSeries (Fin n) ℂ)*G j) := by
    change actualFormalBlowup A e b
      ((H : MvPowerSeries (Fin n) ℂ)*(MvPowerSeries.X e)^(M-μ j)*g j)=_
    rw [map_mul,map_mul,map_pow,blowup_pivot A e he b,hLift,
      ←actualNormalizedFormalMember_spec A e he b (μ j) (g j) (hcentre j)]
    change ((MvPowerSeries.X e)^N*(P : MvPowerSeries (Fin n) ℂ))*
      (MvPowerSeries.X e)^(M-μ j)*((MvPowerSeries.X e)^(μ j)*G j)=_
    calc
      _=(MvPowerSeries.X e)^(N+((M-μ j)+μ j))*((P : MvPowerSeries (Fin n) ℂ)*G j):=by
        rw [pow_add,pow_add]
        ring
      _=(MvPowerSeries.X e)^(N+M)*((P : MvPowerSeries (Fin n) ℂ)*G j):=by
        rw [Nat.sub_add_cancel (hμ j)]
  have hNorm : (P : MvPowerSeries (Fin n) ℂ)*G j=actualNormalizedFormalMember A e he b (N+M) F hF:=
    actualNormalizedFormalMember_unique A e he b (N+M) F hF _ hσ.symm
  obtain ⟨Q,hQ,hSupp⟩:=actualNormalizedFormalMember_supported_historical_division
    w g hmarked hwhole hSupported A e he b hHeads hcentre (N+M)
    (fun i=>(hμ i).trans (Nat.le_add_left _ _)) F hI hF
  exact ⟨Q,hNorm.trans hQ,hSupp⟩

/-- Actual normalized marked orders and actual pure-leading agreement
produce target WHOLE historical frames AND ENTIRE ideal supported division.
No target frame, division, quotient-dimension or HS law is a premise. -/
theorem actual_normalized_whole_supported_division_of_marks_and_pure_leading
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (A B : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀j i,i∉B → wordExponent (w j) i=0) (hBA : B⊆A\{e})
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w j)))
    (hTargetMarked : ∀j,actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hPure : ∀j α,normalExponentDegree α=normalExponentDegree (wordExponent (w j)) →
      (∀i,i∉B → α i=0) →
        MvPowerSeries.coeff α (actualNormalizedFormalMember A e he b
          (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j))=MvPowerSeries.coeff α (g j)) :
    (∀q,Function.Bijective (historicalWholeJetMap w (fun j=>actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)) q)) ∧
    HistoricalWholeSupportedDivision w (fun j=>actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)) := by
  let G:=fun j=>actualNormalizedFormalMember A e he b
    (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)
  have hWholeG (q : ℕ) : Function.Bijective (historicalWholeJetMap w G q):=
    historicalWholeJetMap_bijective_of_pure_leading_agreement w g G hmarked hTargetMarked B hHeads hPure q (hwhole q)
  have hLegal : ∀j : Fin k,(↑(wordExponent (w j)).support : Set (Fin n))⊆A\{e} := by
    intro j i hi
    apply hBA
    by_contra hiB
    exact (Finsupp.mem_support_iff.mp hi) (hHeads j i hiB)
  have hPolynomial (j : Fin k) (P : MvPolynomial (Fin n) ℂ) :
      historicalFormalRemainder w G hTargetMarked hWholeG ((P : MvPowerSeries (Fin n) ℂ)*G j)=0 := by
    obtain ⟨Q,hDiv,hQ⟩:=actual_normalized_polynomial_multiple_supported_division
      w g hmarked hwhole hSupported A e he b hLegal hcentre j P
    apply historicalFormalRemainder_eq_of_supported w G hTargetMarked hWholeG _ Q 0
    · simpa only [add_zero] using hDiv
    · exact hQ
    · intro β _
      exact map_zero _
  refine ⟨hWholeG,?_⟩
  intro F hF
  let Q:=fun j=>historicalFormalQuotient w G hTargetMarked hWholeG j F
  refine ⟨Q,?_,?_⟩
  · have hDiv:=historicalFormal_division w G hTargetMarked hWholeG F
    rw [historicalFormalRemainder_whole_ideal_zero w G hTargetMarked hWholeG hPolynomial hF,add_zero] at hDiv
    exact hDiv
  · intro j β hAvoid
    apply historicalFormalQuotient_support w G hTargetMarked hWholeG F j β
    intro hOwner
    exact hAvoid ((historicalOwner_eq_some_iff w _ j).mp hOwner).2

end
end Hironaka.HironakaActualHistoricalBlowupSupportedDivision
