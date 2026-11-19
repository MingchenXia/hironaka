import Hironaka.Resolution.HironakaActualOffCentreGivenCoordinates
import Hironaka.Resolution.HironakaActualHistoricalNativeControlledSuccessor
import Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS
import Hironaka.MarkedIdeal.TransformOffCentre

/-! The actual off-centre native successor retains the LITERAL SAME weak
family, all five laws, whole true strict ideal and full controlled record.
The actual native chart, unit denominator and whole ideal dictionaries are
derived from real geometry, with every ordered old/born boundary retained. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalOffCentreSuccessor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualOffCentreGivenCoordinates HironakaActualControlledNeighborhoodGenerators
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaActualFixedFlatteningHSComparison HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualFixedInheritedSelector HironakaActualCauchyMonomialDivision
  HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalHSTransfer HironakaActualUnshiftedInitialHSTransfer
  HironakaActualPointGeometricBennett BlowupTowers
  HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  RelativePrincipalizationSpan BlowupFlatCoordinates InvertibleIdealQuotient
  BlowupControlledTransform BlowupExceptionalDivisor IdealWeightPowers MarkedIdeals OkaRelationSheaf

variable {n k : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Actual unit-denominator cancellation off the centre gives the ENTIRE
actual target controlled ideal in the SAME identity-square coordinates. -/
theorem actual_off_centre_geometric_adapted_ideal
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y) (hzC : π z∉C)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) z).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0)
    (hSquare : ∀y : Y,y∈(chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y∈Θ.source → π y∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=Θ.toFun (chartAt (ComplexModel n) z y))
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent) :
    (Q.geoTransform C π).ideal.IsCoherent ∧
      adaptedIdeal (Q.geoTransform C π).ideal z Θ hΘ0=adaptedIdeal Q.ideal (π z) Φ hΦ0 := by
  let P:=GermIdeal.pullback (m:=n) π Q.ideal
  let L:=idealPow (exceptionalDivisor hπ).ideal Q.d
  have hP : P.IsCoherent:=GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hQI
  have hL : L.IsCoherent:=GermIdealPullbackCalculus.isCoherent_idealPow
    (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) Q.d
  have hOne : L.mem z (1 : Y → ℂ) := by
    change (idealPow (exceptionalDivisor hπ).ideal Q.d).mem z 1
    rw [exceptionalDivisor_ideal]
    exact MarkedIdeals.MarkedIdeal.one_mem_idealPow (n:=n)
      (MarkedIdeals.MarkedIdeal.one_mem_pullback_vanishingIdeal (n:=n) (π:=π) hzC hπ.1.1) Q.d
  have hMem (g : Y → ℂ) : (controlledTransform hπ Q.ideal Q.d).mem z g ↔ P.mem z g := by
    constructor
    · intro hg
      have h:=(mem_colon_iff.mp hg).2 (1 : Y → ℂ) hOne
      simpa only [Pi.one_apply,one_mul] using h
    · intro hg
      apply mem_colon_iff.mpr
      refine ⟨holomorphicAt_of_mem_coherent P hP hg,fun a ha=>?_⟩
      exact GermIdeal.mem_pullback_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.mul_left
        (holomorphicAt_of_mem_coherent L hL ha) (GermIdeal.mem_pullback_iff.mp hg))
  have hControlled:=(Q.geoTransform_ideal_eq_controlledTransform hQN hQI hπ)
  have hTarget : (Q.geoTransform C π).ideal.IsCoherent := by
    rw [hControlled]
    exact CoherentIdealColon.isCoherent_colon_of_isCoherent hP hL
  refine ⟨hTarget,?_⟩
  have hAdapted : adaptedIdeal (Q.geoTransform C π).ideal z Θ hΘ0=adaptedIdeal P z Θ hΘ0 := by
    unfold adaptedIdeal
    apply congrArg Ideal.span
    ext g
    constructor
    · rintro ⟨F,hF,hIF,rfl⟩
      rw [hControlled] at hIF
      exact ⟨F,hF,(hMem F).mp hIF,rfl⟩
    · rintro ⟨F,hF,hIF,rfl⟩
      refine ⟨F,hF,?_,rfl⟩
      rw [hControlled]
      exact (hMem F).mpr hIF
  exact hAdapted.trans (actual_native_identity_square_adapted_ideal Q.ideal hQI π hπ.contMDiff z
    Φ hΦ0 Θ hΘsrc hΘ0 hSquare)

private theorem original_vanishing_origin_congr_near_zero (S T : Set (ComplexModel n))
    (hST : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈S ↔ z∈T) :
    originalCoherentOriginIdeal (vanishingIdeal (n:=n) S)=
      originalCoherentOriginIdeal (vanishingIdeal (n:=n) T) := by
  ext g
  obtain ⟨G,hG,rfl⟩:=HolGerm.exists_eq_mk g
  rw [mk_mem_original_vanishing_origin_ideal_iff,mk_mem_original_vanishing_origin_ideal_iff]
  constructor
  · intro h
    filter_upwards [h,hST] with z hz hzt hzT
    exact hz (hzt.mpr hzT)
  · intro h
    filter_upwards [h,hST] with z hz hzt hzS
    exact hz (hzt.mp hzS)

/-- The ENTIRE true native strict origin ideal off the centre is literally
the old entire source origin ideal in these SAME given native coordinates. -/
theorem actual_off_centre_strict_origin_eq_source
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π z)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) z).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0)
    (hSquare : ∀y : Y,y∈(chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y∈Θ.source → π y∉C ∧ π y∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=Θ.toFun (chartAt (ComplexModel n) z y))
    (W : Set X) (hW : IsClosed W) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) (strictTransform n π W)) z Θ) 0)=
      originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) (π z) Φ) 0) := by
  rw [originalFlattenedVanishingOriginIdeal_eq_model z Θ hΘsrc hΘ0,
    originalFlattenedVanishingOriginIdeal_eq_model (π z) Φ hΦsrc hΦ0]
  apply original_vanishing_origin_congr_near_zero
  have h0T : (0 : ComplexModel n)∈Θ.target:=by
    simpa only [hΘ0] using Θ.mapsTo_toFun Θ.center_mem_source
  filter_upwards [Θ.isOpen_target.mem_nhds h0T] with u hu
  let y:=actualFlatteningInverseMap z Θ u
  have hm:=flatInverse_mem Θ hu hΘsrc
  have hs:=hSquare y hm.1.1 hm.1.2
  have hPhi : Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=u:=hs.2.2.trans hm.2
  have huΦ : u∈Φ.target := by
    rw [←hPhi]
    exact Φ.mapsTo_toFun hs.2.1.2
  have hCoord:=congrArg Φ.invFun hPhi
  rw [Φ.left_inv _ hs.2.1.2] at hCoord
  have hInv : π y=actualFlatteningInverseMap (π z) Φ u:=
    ((chartAt (ComplexModel n) (π z)).left_inv hs.2.1.1).symm.trans
      (congrArg (chartAt (ComplexModel n) (π z)).symm hCoord)
  have hyE : y∉exceptionalLocus n π:=fun h=>
    hs.1 (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
  have hStrict:=HironakaAdmissibleCalculus.mem_strictTransform_iff_of_notMem hπ.contMDiff.continuous hW hyE
  change (u∈Θ.target ∧ y∈strictTransform n π W) ↔
    (u∈Φ.target ∧ actualFlatteningInverseMap (π z) Φ u∈W)
  constructor
  · rintro ⟨_,hy⟩
    refine ⟨huΦ,?_⟩
    rw [←hInv]
    exact hStrict.mp hy
  · rintro ⟨_,hy⟩
    refine ⟨hu,hStrict.mpr ?_⟩
    rw [hInv]
    exact hy

/-- TRUE off-centre geometry internally produces target coordinates in
which the target family is the LITERAL SAME Γ, with all five laws, entire
true strict ideal and entire controlled record. Empty boundary tags remain. -/
theorem exists_actual_native_same_historical_off_centre_successor
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y) (hzC : π z∉C)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π z)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) (π z) Φ) 0))
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    (hQSource : adaptedIdeal Q.ideal (π z) Φ hΦ0=
      weightedCompression (fun v : V=>normalExponentDegree v.val) Γ)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val)) :
    ∃(Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0),
      Θ.source⊆(chartAt (ComplexModel n) z).target ∧
      (∀y : Y,y∈(chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y∈Θ.source → π y∉C ∧ π y∈flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=Θ.toFun (chartAt (ComplexModel n) z y)) ∧
      (Q.geoTransform C π).ideal.IsCoherent ∧
      adaptedIdeal (Q.geoTransform C π).ideal z Θ hΘ0=
        weightedCompression (fun v : V=>normalExponentDegree v.val) Γ ∧
      (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ∧
      (z∈(Q.geoTransform C π).cosupp ↔ π z∈Q.cosupp) ∧
      ActualHistoricalFivePointLaws S a w Γ ∧
      originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) (strictTransform n π W)) z Θ) 0)=
          Ideal.span (range Γ) ∧
      (∀(f : V → ComplexModel n → ℂ)(hf : ∀v,HolAt (f v) 0),
        (∀v,Γ v=HolGerm.mk (f v) (hf v)) →
        ∃U : TopologicalSpace.Opens (ComplexModel n),(0 : ComplexModel n)∈U ∧
          (U : Set (ComplexModel n))⊆Θ.target ∧ (∀v,DifferentiableOn ℂ (f v) U) ∧
          MarkedIdealBiholomorphism.MarkedIdeal.pullback
            (fun y : U=>actualFlatteningInverseMap z Θ y) (Q.geoTransform C π)=
            ⟨(fun y : U=>actualFlatteningInverseMap z Θ y) ⁻¹' (Q.geoTransform C π).N,
              (Q.geoTransform C π).E.map ((fun y : U=>actualFlatteningInverseMap z Θ y) ⁻¹' ·),
              weightedFunctionIdeal (fun v : V=>normalExponentDegree v.val) (fun v (y : U)=>f v y),
              weightedCommonMark (fun v : V=>normalExponentDegree v.val)⟩) := by
  obtain ⟨Θ,hΘsrc,hΘ0,hSquare⟩:=exists_actual_off_centre_given_coordinates hπ z hzC Φ hΦ0
  have hIdSquare:=fun y hy hyΘ=>(hSquare y hy hyΘ).2
  obtain ⟨hCoherent,hIdeal⟩:=actual_off_centre_geometric_adapted_ideal hπ z hzC Φ hΦ0 Θ hΘsrc hΘ0
    hIdSquare Q hQN hQI
  have hCompression:=hIdeal.trans hQSource
  have hStrictOrigin:=actual_off_centre_strict_origin_eq_source hπ z Φ hΦsrc hΦ0 Θ hΘsrc hΘ0
    hSquare W hW.isClosed
  have hRange : range (fun i=>Γ (a i))=range Γ := by
    ext g
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨a i,rfl⟩
    · rintro ⟨v,rfl⟩
      exact ⟨a.symm v,by simp⟩
  have hSpanAll : Ideal.span (range Γ)=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) (π z) Φ) 0):=by
    rw [←hRange]
    exact hSpan
  have hCut:=TransformOffCentre.mem_cosupp_geoTransform_iff Q (hQN ▸ isClosed_univ)
    (fun _ _ hg=>holomorphicAt_of_mem_coherent Q.ideal hQI hg) hπ hzC
  have hHS (ℓ : ℕ) :=HironakaActualBlowupOffCentreIntrinsicHS.hilbertSamuelAt_actual_strict_blowup_off_centre
    (X:=CMfd.of (n:=n) X) (Y:=CMfd.of (n:=n) Y) hπ hW z hzC ℓ
  refine ⟨Θ,hΘ0,hΘsrc,hSquare,hCoherent,hCompression,hHS,hCut,hSource,
    hStrictOrigin.trans hSpanAll.symm,?_⟩
  intro f hf hF
  exact exists_actual_native_weighted_record_of_adapted_span (Q.geoTransform C π) hCoherent z Θ hΘsrc hΘ0
    (fun v : V=>normalExponentDegree v.val) Γ hCompression ((MarkedIdeals.MarkedIdeal.geoTransform_d Q C π).trans hQMark)
      f hf hF

end
end Hironaka.HironakaActualHistoricalOffCentreSuccessor
