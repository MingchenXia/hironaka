import Hironaka.Resolution.HironakaActualHistoricalNativeCompatibleSource
import Hironaka.Resolution.HironakaActualHistoricalOffCentreSuccessor
import Hironaka.Resolution.HironakaActualHistoricalOriginalSingularReference

/-! A genuine ALL-POINT one-step closure for the actual full native record
and SAME original finite five-law data. Actual source upper bound/cut/point
presentations are the induction invariant; ALL corresponding target facts
are derived in both true native branches. The initial moving-point base and
additional original function/unit historical transport remain separate. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalNativeStageStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualHistoricalNativeCompatibleSource HironakaActualHistoricalNativeControlledSuccessor
  HironakaActualHistoricalOffCentreSuccessor HironakaActualHistoricalOriginalSingularReference
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalFormalHSTransfer
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaSmoothSubmersionGermIdealColon HironakaSmoothCentreCoherentDomain
  HironakaSmoothCentreNearbyStalks HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaActualNativeSourceChartComposition HironakaActualHSConstantCentreBennett
  HironakaActualHistoricalMovingCentreChart HironakaActualAnalyticBlowupTaylor
  HironakaEmbeddedAnalytic
  BlowupControlledTransform BlowupExceptionalDivisor IdealWeightPowers InvertibleIdealQuotient
  MarkedIdeals

variable {m n k : ℕ} {X₀ X Y : Type}
  [TopologicalSpace X₀] [ChartedSpace (ComplexModel m) X₀] [IsComplexManifold m X₀]
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- An ACTUAL source point invariant with SAME finite labels/words/selector
and whole native W/Q ideals. This is a forgetful point invariant, not an
asserted initial moving window or original function/unit history witness. -/
def ActualHistoricalNativePointPresentation
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (W : Set X) (Q : MarkedIdeal n X) (x : X) : Prop :=
  ∃(Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (_hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (Γ : V → HolGerm (ComplexModel n)),
    ActualHistoricalFivePointLaws S a w Γ ∧
    Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Φ) 0) ∧
    adaptedIdeal Q.ideal x Φ hΦ0=weightedCompression (fun v : V=>normalExponentDegree v.val) Γ

private theorem span_enumeration_eq {V : Finset (Fin n →₀ ℕ)} (a : Fin k ≃ V)
    (Γ : V → HolGerm (ComplexModel n)) :
    Ideal.span (range (fun i=>Γ (a i)))=Ideal.span (range Γ) := by
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨a i,rfl⟩
  · rintro ⟨v,rfl⟩
    exact ⟨a.symm v,by simp⟩

/-- BOTH genuine native branches at a true source cut point produce the
next actual cut and a SAME-selector five-law point presentation. No target
presentation, source compatible chart, source centre power or codim cert. -/
theorem actual_native_successor_at_source_cut
    (W₀ : Set X₀) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : X₀)
    (ha₀ : a₀∈singularSet (n:=m) W₀)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hOwn : ∀i,HironakaActualHistoricalWholeJetFrames.historicalOwner w (wordExponent (w i))=some i)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ})
    {C : Set X} (hC : IsClosedSubmanifold n C) (hCcut : C⊆Q.cosupp)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y) (hzSource : π z∈Q.cosupp)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q (π z)) :
    (z∈(Q.geoTransform C π).cosupp ↔
      ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ∧
    (z∈(Q.geoTransform C π).cosupp →
      ActualHistoricalNativePointPresentation S a w (strictTransform n π W) (Q.geoTransform C π) z) := by
  obtain ⟨Φ,hΦsrc,hΦ0,Γ,hFive,hSpan,hCompression⟩:=hAt
  by_cases hzC : π z∈C
  · obtain ⟨c,hReg⟩:=hC.2 (π z) hzC
    obtain ⟨_hSing,hCodim,hHSConst⟩:=actual_original_reference_current_cut_centre_geometry
      W₀ hW₀ a₀ ha₀ W hW Q hCut C hCcut (π z) c hReg
    choose f hf hRep using fun v=>HolGerm.exists_eq_mk (Γ v)
    obtain ⟨U,_h0U,_hUT,_hfU,_hRecord,O,_hO,_h0O,_hOU,hSources⟩:=
      exists_actual_native_historical_compatible_source_chart (π z) Φ hΦsrc hΦ0 W
        (CartanIrreducible.cartanCoherence W hW) S Γ a w hw hPositive hFive hSpan
        Q hQN hQI hCompression hQMark f hf hRep
    obtain ⟨D,hΨsrc,hFlat,hFiveD,_hJacD,hSpanD,hCompD,hHeadsD,hCentreD⟩:=hSources C c hReg hCcut
    let Ψ:=RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D.chart hΦ0
    let hΨ0:=(actual_native_source_chart_comp_geometry (π z) Φ hΦsrc hΦ0 D.chart D.chart_zero).2
    let E:=(localGermAlgEquiv D.chart D.chart_zero).symm
    let p:=D.priorityPermutation.trans (finCongr D.dimension)
    obtain ⟨e,b,Θ,hΘ0,N,_he,hΘsrc,_hbT,_hbe,_hBound,_hSquare,_hProduct,_hLe,_hDrop,
      _hCoherent,hTargetCompression,hCutLocal,hPoint,_hWindow⟩:=
      exists_actual_native_same_historical_controlled_successor hπ z c hCodim p Ψ hΨsrc hΨ0 hFlat W hC hW
        hHSConst S (fun v=>E (Γ v)) a w hw hPositive hOwn hSpanD hFiveD hHeadsD hCentreD
          Q hQN hQI hCompD hQMark
    refine ⟨hCutLocal,?_⟩
    intro hz
    have hPointAt:=hPoint hz
    refine ⟨Θ,hΘsrc,hΘ0,N,hPointAt.2.2.1,?_,hTargetCompression⟩
    exact (span_enumeration_eq a N).trans hPointAt.2.2.2.2.symm
  · obtain ⟨Θ,hΘ0,hΘsrc,_hSquare,_hCoherent,hTargetCompression,hHS,hOffCut,hFiveSame,hStrictSpan,_hWindow⟩:=
      exists_actual_native_same_historical_off_centre_successor hπ z hzC Φ hΦsrc hΦ0 W hW S Γ a w
        hFive hSpan Q hQN hQI hCompression hQMark
    refine ⟨⟨fun _=>hHS,fun _=>hOffCut.mpr hzSource⟩,?_⟩
    intro _hz
    exact ⟨Θ,hΘsrc,hΘ0,Γ,hFiveSame,(span_enumeration_eq a Γ).trans hStrictSpan.symm,hTargetCompression⟩

/-- The REAL native blowup propagates the actual ALL-POINT upper bound,
ENTIRE actual cut and SAME finite five-law point invariant. Every target
fact is derived; actual original function/unit history is a separate layer. -/
theorem actual_native_all_point_stage_step
    (W₀ : Set X₀) (hW₀ : IsComplexAnalyticSubset (n:=m) W₀) (a₀ : X₀)
    (ha₀ : a₀∈singularSet (n:=m) W₀)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hOwn : ∀i,HironakaActualHistoricalWholeJetFrames.historicalOwner w (wordExponent (w i))=some i)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ})
    (hUpper : ∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ)
    (hAt : ∀x∈Q.cosupp,ActualHistoricalNativePointPresentation S a w W Q x)
    {C : Set X} (hC : IsClosedSubmanifold n C) (hCcut : C⊆Q.cosupp)
    {π : Y → X} (hπ : IsBlowupAlong n C π) :
    IsComplexAnalyticSubset (n:=n) (strictTransform n π W) ∧
    (Q.geoTransform C π).N=univ ∧ (Q.geoTransform C π).ideal.IsCoherent ∧
    (Q.geoTransform C π).d=weightedCommonMark (fun v : V=>normalExponentDegree v.val) ∧
    (∀z ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ) ∧
    (Q.geoTransform C π).cosupp={z | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ} ∧
    (∀z∈(Q.geoTransform C π).cosupp,
      ActualHistoricalNativePointPresentation S a w (strictTransform n π W) (Q.geoTransform C π) z) ∧
    (Q.geoTransform C π).cosupp⊆singularSet (n:=n) (strictTransform n π W) := by
  have hCentreProfiles (x : X) (hx : x∈C) : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ := by
    have h:=hCcut hx
    rw [hCut] at h
    exact h
  have hHSConst : ∀x∈C,∀y∈C,∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) y ℓ:=
    fun x hx y hy ℓ=>(hCentreProfiles x hx ℓ).trans (hCentreProfiles y hy ℓ).symm
  have hLe (z : Y) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ:=
    hilbertSamuelAt_actual_hs_constant_smooth_centre_blowup_le hπ hC hW hHSConst z ℓ
  have hSubset : (Q.geoTransform C π).cosupp⊆π ⁻¹' Q.cosupp:=
    TransformOffCentre.cosupp_geoTransform_subset_preimage Q (hQN ▸ isClosed_univ)
      (fun _ _ hg=>holomorphicAt_of_mem_coherent Q.ideal hQI hg) hπ hCcut
  have hLocal (z : Y) (hz : π z∈Q.cosupp):=
    actual_native_successor_at_source_cut W₀ hW₀ a₀ ha₀ W hW Q hQN hQI S a w hw hPositive hOwn hQMark
      hCut hC hCcut hπ z hz (hAt (π z) hz)
  have hSourceProfile (z : Y) (hz : π z∈Q.cosupp) :
      ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ := by
    rw [hCut] at hz
    exact hz
  have hSourceOfProfile (z : Y)
      (hz : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ) : π z∈Q.cosupp := by
    rw [hCut]
    intro ℓ
    apply Nat.le_antisymm (hUpper (π z) ℓ)
    calc
      hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ:=(hz ℓ).symm
      _≤hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ:=hLe z ℓ
  have hNewCut : (Q.geoTransform C π).cosupp={z | ∀ℓ,
      hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=m) W₀) a₀ ℓ} := by
    ext z
    constructor
    · intro hz
      have hsrc:=hSubset hz
      exact fun ℓ=>((hLocal z hsrc).1.mp hz ℓ).trans (hSourceProfile z hsrc ℓ)
    · intro hz
      have hsrc:=hSourceOfProfile z hz
      apply (hLocal z hsrc).1.mpr
      exact fun ℓ=>(hz ℓ).trans (hSourceProfile z hsrc ℓ).symm
  have hTargetW:=HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hW
  have hTargetI : (Q.geoTransform C π).ideal.IsCoherent := by
    rw [Q.geoTransform_ideal_eq_controlledTransform hQN hQI hπ]
    exact CoherentIdealColon.isCoherent_colon_of_isCoherent
      (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hQI)
      (GermIdealPullbackCalculus.isCoherent_idealPow
        (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) Q.d)
  refine ⟨hTargetW,Q.geoTransform_N_eq_univ hQN hπ,hTargetI,
    (MarkedIdeals.MarkedIdeal.geoTransform_d Q C π).trans hQMark,
    (fun z ℓ=>(hLe z ℓ).trans (hUpper (π z) ℓ)),hNewCut,?_,?_⟩
  · intro z hz
    exact (hLocal z (hSubset hz)).2 hz
  · intro z hz
    rw [hNewCut] at hz
    exact actual_original_singular_profile_locus_subset_current_singular W₀ hW₀ a₀ ha₀
      (strictTransform n π W) hTargetW hz

end
end Hironaka.HironakaActualHistoricalNativeStageStep
