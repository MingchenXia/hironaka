import Hironaka.Resolution.HironakaActualHistoricalAnalyticStrictDictionary
import Hironaka.Resolution.HironakaActualUnshiftedInitialHSTransfer
import Hironaka.Resolution.HironakaActualPointGeometricBennett

/-! Actual normalized point marks produce ENTIRE true geometric strict HS
preservation. Whole supported division and the real strict dictionary are
proved first, never inferred from the desired target HS equality. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalMarkedHSPreservation
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalFormalSupportedDivision
  HironakaActualHistoricalCentreFilteredDivision HironakaActualHistoricalNormalizedLeadingFrames
  HironakaActualCauchyMonomialDivision HironakaActualOriginalFormalHSTransfer
  HironakaActualHistoricalAnalyticStrictDictionary HironakaActualAnalyticBlowupTaylor
  HironakaActualUnshiftedInitialHSTransfer HironakaActualPointGeometricBennett
  HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance

variable {n k : ℕ}

/-- Actual whole supported division makes the SAME old complement compute
BOTH entire ideal HS functions, without a supplied dimension equality. -/
theorem historical_whole_hilbertSamuel_eq
    (w : Fin k → CoordinateWord n) (g h : Fin k → MvPowerSeries (Fin n) ℂ)
    (hg : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hh : ∀j,h j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hWholeG : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hWholeH : ∀q,Function.Bijective (historicalWholeJetMap w h q))
    (hSupportedG : HistoricalWholeSupportedDivision w g)
    (hSupportedH : HistoricalWholeSupportedDivision w h) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n (Ideal.span (range g)) ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.span (range h)) ℓ := by
  let q:=ℓ+1
  let EG:=LinearEquiv.ofBijective (historicalComplementQuotientMap w g q)
    ⟨historicalComplementQuotientMap_injective w g hg hWholeG hSupportedG q,
      historicalComplementQuotientMap_surjective w g hg hWholeG q⟩
  let EH:=LinearEquiv.ofBijective (historicalComplementQuotientMap w h q)
    ⟨historicalComplementQuotientMap_injective w h hh hWholeH hSupportedH q,
      historicalComplementQuotientMap_surjective w h hh hWholeH q⟩
  exact EG.finrank_eq.symm.trans EH.finrank_eq

/-- ACTUAL target marks imply equality of the ENTIRE source/normalized
formal HS profile; all target frames/division are internally derived. -/
theorem actual_normalized_hilbertSamuel_eq_of_marks
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (A B : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀j i,i∉B → wordExponent (w j) i=0) (hBA : B⊆A\{e})
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w j)))
    (hTargetMarked : ∀j,actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w j))) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n (Ideal.span (range fun j=>actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j))) ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.span (range g)) ℓ := by
  have hTarget:=actual_normalized_whole_supported_division_of_marks
    w g hmarked hwhole hSupported A B e he b hHeads hBA hcentre hTargetMarked
  exact (historical_whole_hilbertSamuel_eq w g _ hmarked hTargetMarked hwhole hTarget.1 hSupported hTarget.2 ℓ).symm

private theorem map_taylor_span (Γ : Fin k → HolGerm (ComplexModel n)) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range Γ))=
      Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (Γ j)) := by
  rw [Ideal.map_span,←range_comp]
  rfl

/-- In the TRUE actual geometric strict chart, normalized marked orders
produce the SAME ENTIRE original HS function, not a finite profile cut. -/
theorem actual_geometric_strict_hilbertSamuel_eq_of_marks
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n:=d+t) W)
    (w : Fin k → CoordinateWord (d+t)) (Γ : Fin k → HolGerm (ComplexModel (d+t)))
    (hspan : Ideal.span (range Γ)=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))
    (B : Set (Fin (d+t))) (hHeads : ∀i q,q∉B → wordExponent (w i) q=0)
    (hBA : B⊆actualTangentCentreVariables d t\{j.natAdd d})
    (hCentre : ∀i,Γ i∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^
      normalExponentDegree (wordExponent (w i)))
    (hmarked : ∀i,actualUnshiftedTaylorAlgHom (d+t) (Γ i)∈
      genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)))
    (hTargetMarked : ∀i,actualNormalizedFormalMember (actualTangentCentreVariables d t) (j.natAdd d)
      (⟨j,rfl⟩ : j.natAdd d∈actualTangentCentreVariables d t) b
      (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom (d+t) (Γ i))
      (actualTaylor_mem_coordinateCentre_pow _ _ _ (hCentre i))∈
        genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i))) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t)
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+t) W) 0 ℓ := by
  obtain ⟨N,_hProduct,hTaylor,hStrict⟩:=exists_actual_historical_analytic_strict_generators_of_marks
    d t ht j b W hW w Γ hspan B hHeads hBA hCentre hmarked hwhole hSupported hTargetMarked
  have hFormal:=actual_normalized_hilbertSamuel_eq_of_marks w
    (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)) hmarked hwhole hSupported
    (actualTangentCentreVariables d t) B (j.natAdd d) ⟨j,rfl⟩ b hHeads hBA
    (fun i=>actualTaylor_mem_coordinateCentre_pow _ _ _ (hCentre i)) hTargetMarked ℓ
  rw [hilbertSamuelAt_model_zero,hilbertSamuelAt_model_zero,hStrict,←hspan,
    hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    hilbertSamuelValue_eq_actual_unshifted_formal_extension,map_taylor_span,map_taylor_span]
  simpa only [hTaylor] using hFormal

end
end Hironaka.HironakaActualHistoricalMarkedHSPreservation
