import Hironaka.Resolution.HironakaActualNativeSourceChartComposition
import Hironaka.Resolution.HironakaActualHistoricalCompatibleChartFiveLaws

/-! One actual native full-record source window, chosen BEFORE every centre,
internally constructs compatible native source coordinates, all five SAME
weak laws, whole W/Q source spans and genuine whole member centre powers. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalNativeCompatibleSource
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualNativeSourceChartComposition HironakaActualHistoricalCompatibleChartFiveLaws
  HironakaActualHistoricalMovingCentreChart HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualControlledNeighborhoodGenerators HironakaActualFixedFlatteningHSComparison
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaActualFixedInheritedSelector HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualOriginalFormalHSTransfer BlowupFlatCoordinates MarkedIdeals OkaRelationSheaf
  HironakaHolomorphicJetMonomialSpan HironakaActualAnalyticBlowupTaylor

variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem compatible_coordinate_fixed {B : Set (Fin n)} {C : Set (ComplexModel n)} {c : ℕ}
    (D : ActualCompatibleMovingCentreChart B C c) (i : Fin n) (hi : i∈B) :
    (localGermAlgEquiv D.chart D.chart_zero).symm (coordinateGerm i)=coordinateGerm i := by
  have hProj : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (fun z : ComplexModel n=>z i) z:=
    Eventually.of_forall fun _=>(EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hInv:=holomorphic_comp D.chart.invFun (local_invFun_holomorphic D.chart D.chart_zero)
    (local_invFun_zero D.chart D.chart_zero) hProj
  change HolGerm.mk ((fun z : ComplexModel n=>z i)∘D.chart.invFun) hInv=coordinateGerm i
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z=>(D.essentialCoordinates z i hi).2

private theorem map_weighted_compression {ι : Type} [Fintype ι]
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (w : ι → ℕ) (Γ : ι → HolGerm (ComplexModel n)) :
    Ideal.map E.toRingEquiv.toRingHom (weightedCompression w Γ)=
      weightedCompression w (fun v=>E (Γ v)) := by
  rw [weightedCompression,Ideal.map_span,weightedCompression,←range_comp]
  apply congrArg Ideal.span
  apply congrArg range
  funext v
  change E (Γ v^(weightedCommonMark w/w v))=E (Γ v)^(weightedCommonMark w/w v)
  rw [map_pow]

/-- Actual full native source data choose ONE real source window BEFORE
ANY prescribed actual centre, then derive the actual compatible chart,
ALL FIVE SAME weak laws, whole W/Q source spans and whole member powers. -/
theorem exists_actual_native_historical_compatible_source_chart
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (W : Set X) (hW : (vanishingIdeal (n:=n) W).IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Φ) 0))
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    (hQSource : adaptedIdeal Q.ideal x Φ hΦ0=
      weightedCompression (fun v : V=>normalExponentDegree v.val) Γ)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (f : V → ComplexModel n → ℂ) (hf : ∀v,HolAt (f v) 0)
    (hRep : ∀v,Γ v=HolGerm.mk (f v) (hf v)) :
    ∃U : TopologicalSpace.Opens (ComplexModel n),(0 : ComplexModel n)∈U ∧
      (U : Set (ComplexModel n))⊆Φ.target ∧
      (∀v,DifferentiableOn ℂ (f v) U) ∧
      MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (fun z : U=>actualFlatteningInverseMap x Φ z) Q=
        ⟨univ,Q.E.map ((fun z : U=>actualFlatteningInverseMap x Φ z) ⁻¹' ·),
          weightedFunctionIdeal (fun v : V=>normalExponentDegree v.val) (fun v (z : U)=>f v z),
          weightedCommonMark (fun v : V=>normalExponentDegree v.val)⟩ ∧
      ∃O : Set (ComplexModel n),IsOpen O ∧ (0 : ComplexModel n)∈O ∧ O⊆U ∧
      ∀(C : Set X)(c : ℕ),RegularAtDim (n:=n) C x c → C⊆Q.cosupp →
        ∃D : ActualCompatibleMovingCentreChart (fixedSelectorEssential V) (actualFixedFlatteningSet x Φ C) c,
          let Ψ:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D.chart hΦ0
          let hΨ0:=(actual_native_source_chart_comp_geometry x Φ hΦsrc hΦ0 D.chart D.chart_zero).2
          let E:=(localGermAlgEquiv D.chart D.chart_zero).symm
          let p:=D.priorityPermutation.trans (finCongr D.dimension)
          Ψ.source⊆(chartAt (ComplexModel n) x).target ∧
          (∀{y : X},y∈(chartAt (ComplexModel n) x).source →
            chartAt (ComplexModel n) x y∈Ψ.source →
            (y∈C ↔ Ψ.toFun (chartAt (ComplexModel n) x y)∈
              coordinateSubsetPlane {i : Fin n | c≤(p i).val})) ∧
          ActualHistoricalFivePointLaws S a w (fun v=>E (Γ v)) ∧
          (∀R,actualFixedSelectorJacobian S (fun v=>E (Γ v)) R=actualFixedSelectorJacobian S Γ R) ∧
          Ideal.span (range (fun i=>E (Γ (a i))))=originalCoherentOriginIdeal
            (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Ψ) 0) ∧
          adaptedIdeal Q.ideal x Ψ hΨ0=
            weightedCompression (fun v : V=>normalExponentDegree v.val) (fun v=>E (Γ v)) ∧
          (∀v : V,(↑v.val.support : Set (Fin n))⊆{i : Fin n | c≤(p i).val}) ∧
          (∀v : V,E (Γ v)∈actualAnalyticCoordinateIdeal {i : Fin n | c≤(p i).val}^normalExponentDegree v.val) := by
  obtain ⟨U,h0U,hUT,hfU,hRecord⟩:=exists_actual_native_weighted_record_of_adapted_span Q hQI x Φ
    hΦsrc hΦ0 (fun v : V=>normalExponentDegree v.val) Γ hQSource hQMark f hf hRep
  have hRecordSource : MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (fun z : U=>actualFlatteningInverseMap x Φ z) Q=
      ⟨univ,Q.E.map ((fun z : U=>actualFlatteningInverseMap x Φ z) ⁻¹' ·),
        weightedFunctionIdeal (fun v : V=>normalExponentDegree v.val) (fun v (z : U)=>f v z),
        weightedCommonMark (fun v : V=>normalExponentDegree v.val)⟩ := by
    simpa only [hQN,preimage_univ] using hRecord
  let L : List (Set U):=Q.E.map ((fun z : U=>actualFlatteningInverseMap x Φ z) ⁻¹' ·)
  have hRepU (v : V) : HolGerm.mk (f v) (holAt_of_differentiableOn U.isOpen (hfU v) h0U)=Γ v:=
    (hRep v).symm
  obtain ⟨O,hO,h0O,hOU,hCentreFactory⟩:=exists_actual_native_weighted_compatible_centre_chart
    S Γ f U h0U hfU hRepU hPositive (fun R=>(hSource.2.2.2.2.1 R).1)
      (fun R=>(hSource.2.2.2.2.1 R).2) L
  refine ⟨U,h0U,hUT,hfU,hRecordSource,O,hO,h0O,hOU,?_⟩
  intro C c hReg hC
  let C₀:=actualFixedFlatteningSet x Φ C
  have hRegModel : RegularAtDim (n:=n) C₀ 0 c:=
    actual_native_given_chart_regular_model C x c hReg Φ hΦsrc hΦ0
  have hWeightedC : ∀z : U,(z : ComplexModel n)∈C₀ →
      z∈(⟨univ,L,weightedFunctionIdeal (fun v : V=>normalExponentDegree v.val)
        (fun v (q : U)=>f v q),weightedCommonMark (fun v : V=>normalExponentDegree v.val)⟩ : MarkedIdeal n U).cosupp := by
    intro z hzC
    have hzN : actualFlatteningInverseMap x Φ z∈Q.cosupp:=hC hzC.2
    have hp:=actual_marked_cosupport_pullback_forward Q _
      (actual_native_source_inverse_on_open_contMDiff x Φ hΦsrc U hUT) z hzN
    rw [hRecordSource] at hp
    exact hp
  obtain ⟨D,hPower⟩:=hCentreFactory C₀ c hRegModel hWeightedC
  let Ψ:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D.chart hΦ0
  have hGeometry:=actual_native_source_chart_comp_geometry x Φ hΦsrc hΦ0 D.chart D.chart_zero
  let hΨ0 : Ψ.toFun (chartAt (ComplexModel n) x x)=0:=hGeometry.2
  let E:=(localGermAlgEquiv D.chart D.chart_zero).symm
  let p : Fin n ≃ Fin n:=D.priorityPermutation.trans (finCongr D.dimension)
  have hFive:=actual_compatible_source_action_five_laws S Γ a w hw hSource E D.fixedSection
    (compatible_coordinate_fixed D) D.derivative
  have hNativeFlat : ∀{y : X},y∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y∈Ψ.source →
      (y∈C ↔ Ψ.toFun (chartAt (ComplexModel n) x y)∈
        coordinateSubsetPlane {i : Fin n | c≤(p i).val}) := by
    intro y hy hyΨ
    change chartAt (ComplexModel n) x y∈Φ.source ∩ Φ.toFun ⁻¹' D.chart.source at hyΨ
    have hInv : actualFlatteningInverseMap x Φ (Φ.toFun (chartAt (ComplexModel n) x y))=y:=
      flatInverse_flat Φ ⟨hy,hyΨ.1⟩
    have hNativeC : y∈C ↔ Φ.toFun (chartAt (ComplexModel n) x y)∈C₀ := by
      constructor
      · intro hyC
        refine ⟨Φ.mapsTo_toFun hyΨ.1,?_⟩
        change actualFlatteningInverseMap x Φ (Φ.toFun (chartAt (ComplexModel n) x y))∈C
        rwa [hInv]
      · intro hyC
        have h : actualFlatteningInverseMap x Φ (Φ.toFun (chartAt (ComplexModel n) x y))∈C:=hyC.2
        rwa [hInv] at h
    have hD:=D.centre (Φ.toFun (chartAt (ComplexModel n) x y)) hyΨ.2
    change y∈C ↔ D.chart.toFun (Φ.toFun (chartAt (ComplexModel n) x y))∈
      coordinateSubsetPlane {i : Fin n | c≤(p i).val}
    simpa only [p,Equiv.trans_apply,finCongr_apply,Fin.val_cast] using hNativeC.trans hD
  have hOldW : Ideal.span (range (fun i=>Γ (a i)))=adaptedIdeal (vanishingIdeal (n:=n) W) x Φ hΦ0:=
    hSpan.trans (actual_original_translated_flattened_vanishing_origin_eq_adapted x Φ hΦsrc hΦ0 W hW)
  have hWComp:=actual_native_source_chart_comp_ideal x Φ hΦsrc hΦ0 D.chart D.chart_zero
    (vanishingIdeal (n:=n) W)
  have hNewW : Ideal.span (range (fun i=>E (Γ (a i))))=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Ψ) 0) := by
    calc
      Ideal.span (range (fun i=>E (Γ (a i))))=
          Ideal.map E.toRingEquiv.toRingHom (Ideal.span (range (fun i=>Γ (a i)))) := by
        rw [Ideal.map_span,←range_comp]
        rfl
      _=Ideal.map E.toRingEquiv.toRingHom (adaptedIdeal (vanishingIdeal (n:=n) W) x Φ hΦ0):=
        congrArg (Ideal.map E.toRingEquiv.toRingHom) hOldW
      _=adaptedIdeal (vanishingIdeal (n:=n) W) x Ψ hΨ0:=hWComp.symm
      _=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Ψ) 0):=
        (actual_original_translated_flattened_vanishing_origin_eq_adapted x Ψ hGeometry.1 hΨ0 W hW).symm
  have hQComp:=actual_native_source_chart_comp_ideal x Φ hΦsrc hΦ0 D.chart D.chart_zero Q.ideal
  have hNewQ : adaptedIdeal Q.ideal x Ψ hΨ0=
      weightedCompression (fun v : V=>normalExponentDegree v.val) (fun v=>E (Γ v)):=
    hQComp.trans ((congrArg (Ideal.map E.toRingEquiv.toRingHom) hQSource).trans
      (map_weighted_compression E (fun v : V=>normalExponentDegree v.val) Γ))
  have hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆{i : Fin n | c≤(p i).val} := by
    intro v i hi
    have h:=D.normalContains (show i∈fixedSelectorEssential V from ⟨v,Finsupp.mem_support_iff.mp hi⟩)
    simpa only [p,Equiv.trans_apply,finCongr_apply,Fin.val_cast] using h
  refine ⟨D,hGeometry.1,hNativeFlat,hFive.1,hFive.2.1,hNewW,hNewQ,hHeads,?_⟩
  simpa only [p,Equiv.trans_apply,finCongr_apply,Fin.val_cast] using hPower

end
end Hironaka.HironakaActualHistoricalNativeCompatibleSource
