import Hironaka.Resolution.HironakaActualHistoricalNativePointSuccessor
import Hironaka.Resolution.HironakaActualNativeControlledWeightedRecord

/-! One actual native chart and SAME historical quotient family give true
native HS, all five laws, the ENTIRE actual controlled ideal/cut/marked record.
No target identity, target order or common-open certificate is supplied. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalNativeControlledSuccessor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualHistoricalNativePointSuccessor HironakaActualNativeControlledWeightedRecord
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalHSTransfer HironakaActualAnalyticBlowupTaylor
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothCentreCoherentDomain
  HironakaActualHistoricalMovingCentreChart HironakaHolomorphicJetChartInvariance
  HironakaActualCauchyMonomialDivision
  HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
  HironakaSmoothSubmersionGermIdealColon MarkedIdeals OkaRelationSheaf BlowupFlatCoordinates

variable {n k : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Genuine source data internally produce the SAME native historical point
and actual controlled marked-record successor. Whole Qt compression and its
TRUE cut are derived before identifying that cut with native HS persistence. -/
theorem exists_actual_native_same_historical_controlled_successor
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y)
    (c : ℕ) (hc : c+2≤n) (p : Fin n ≃ Fin n)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π z)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (hFlat : ∀{x : X},x∈(chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x∈Φ.source →
      (x∈C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) x)∈
        coordinateSubsetPlane {i : Fin n | c≤(p i).val}))
    (W : Set X) (hC : IsClosedSubmanifold n C) (hW : IsComplexAnalyticSubset (n:=n) W)
    (hHSConst : ∀x∈C,∀y∈C,∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) y ℓ)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hOwn : ∀i,HironakaActualHistoricalWholeJetFrames.historicalOwner w (wordExponent (w i))=some i)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) (π z) Φ) 0))
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆{i : Fin n | c≤(p i).val})
    (hCentre : ∀v,Γ v∈actualAnalyticCoordinateIdeal {i : Fin n | c≤(p i).val}^normalExponentDegree v.val)
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    (hQSource : adaptedIdeal Q.ideal (π z) Φ hΦ0=
      weightedCompression (fun v : V=>normalExponentDegree v.val) Γ)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val)) :
    ∃(e : Fin n) (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0)
      (N : V → HolGerm (ComplexModel n)),
      c≤(p e).val ∧ Θ.source⊆(chartAt (ComplexModel n) z).target ∧
      (∀i : Fin n,(p i).val<c → b i=0) ∧ b e=0 ∧
      (∀i : Fin n,c≤(p i).val → i≠e → ‖b i‖≤1) ∧
      (∀y : Y,y∈(chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y∈Θ.source → π y∈flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
          actualAnalyticBlowupMap {i : Fin n | c≤(p i).val} e b
            (Θ.toFun (chartAt (ComplexModel n) z y))) ∧
      (∀v,(coordinateGerm e)^normalExponentDegree v.val*N v=
        actualAnalyticBlowupPullback {i : Fin n | c≤(p i).val} e b (Γ v)) ∧
      (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ≤
        hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ∧
      (e∈fixedSelectorEssential V →
        toLex (hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z)<
          toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z))) ∧
      (Q.geoTransform C π).ideal.IsCoherent ∧
      adaptedIdeal (Q.geoTransform C π).ideal z Θ hΘ0=
        weightedCompression (fun v : V=>normalExponentDegree v.val) N ∧
      (z∈(Q.geoTransform C π).cosupp ↔
        ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ∧
      (z∈(Q.geoTransform C π).cosupp →
        e∉fixedSelectorEssential V ∧ (∀i∈fixedSelectorEssential V,b i=0) ∧
        ActualHistoricalFivePointLaws S a w N ∧
        (∀R,actualFixedSelectorJacobian S N R=actualFixedSelectorJacobian S Γ R) ∧
        originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) (strictTransform n π W)) z Θ) 0)=
            Ideal.span (range N)) ∧
      (∀(f : V → ComplexModel n → ℂ) (hf : ∀v,HolAt (f v) 0),
        (∀v,N v=HolGerm.mk (f v) (hf v)) →
        ∃U : TopologicalSpace.Opens (ComplexModel n),(0 : ComplexModel n)∈U ∧
          (U : Set (ComplexModel n))⊆Θ.target ∧
          (∀v,DifferentiableOn ℂ (f v) U) ∧
          MarkedIdealBiholomorphism.MarkedIdeal.pullback
            (fun y : U=>actualFlatteningInverseMap z Θ y) (Q.geoTransform C π)=
            ⟨(fun y : U=>actualFlatteningInverseMap z Θ y) ⁻¹' (Q.geoTransform C π).N,
              (Q.geoTransform C π).E.map ((fun y : U=>actualFlatteningInverseMap z Θ y) ⁻¹' ·),
              weightedFunctionIdeal (fun v : V=>normalExponentDegree v.val) (fun v (y : U)=>f v y),
              weightedCommonMark (fun v : V=>normalExponentDegree v.val)⟩) := by
  obtain ⟨e,he,b,Θ,N,hΘsrc,hΘ0,hbT,hbe,hBound,hSquare,hProduct,hLe,hDrop,hMarksIff,hPoint⟩:=
    exists_actual_native_same_historical_point_successor_with_bennett hπ z c hc p Φ hΦsrc hΦ0 hFlat
      W hC hW hHSConst S Γ a w hw hOwn hSpan hSource hHeads hCentre
  let A : Set (Fin n):={i | c≤(p i).val}
  have heA : e∈A:=he
  have hControlled:=actual_native_same_quotients_geometric_ideal hπ z A e heA b Φ hΦsrc hΦ0 hFlat
    Θ hΘsrc hΘ0 hSquare Q hQN hQI (fun v : V=>normalExponentDegree v.val) Γ N hQSource hQMark hProduct
  have hCut:=actual_native_same_quotients_cosupport_iff hπ z A e heA b Φ hΦsrc hΦ0 hFlat
    Θ hΘsrc hΘ0 hSquare Q hQN hQI (fun v : V=>normalExponentDegree v.val) hPositive Γ N
      hQSource hQMark hProduct
  have hCutHS:=hCut.trans hMarksIff.symm
  refine ⟨e,b,Θ,hΘ0,N,he,hΘsrc,hbT,hbe,hBound,hSquare,hProduct,hLe,hDrop,
    hControlled.1,hControlled.2,hCutHS,fun hz=>hPoint (hCutHS.mp hz),?_⟩
  intro f hf hF
  exact exists_actual_native_same_quotients_controlled_record hπ z A e heA b Φ hΦsrc hΦ0 hFlat
    Θ hΘsrc hΘ0 hSquare Q hQN hQI (fun v : V=>normalExponentDegree v.val) Γ N hQSource hQMark
      hProduct f hf hF

end
end Hironaka.HironakaActualHistoricalNativeControlledSuccessor
