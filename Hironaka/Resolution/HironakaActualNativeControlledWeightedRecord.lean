import Hironaka.Resolution.HironakaActualNativeExceptionalControlledStalk
import Hironaka.Resolution.HironakaActualNativeAdaptedPullbackSquare
import Hironaka.Resolution.HironakaActualControlledNeighborhoodGenerators
import Hironaka.Resolution.HironakaActualHistoricalCentreFilteredDivision

/-! The actual full controlled marked record in its SAME given native chart.
The whole ideal, cut and one same-representative open are derived, with every
ordered boundary entry and the original mark retained. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeControlledWeightedRecord
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualNativeExceptionalControlledStalk HironakaActualNativeAdaptedPullbackSquare
  HironakaActualControlledNeighborhoodGenerators HironakaSmoothSubmersionGermIdealColon
  HironakaActualHistoricalCentreFilteredDivision HironakaActualHistoricalMovingCentreChart
  HironakaActualAnalyticBlowupTaylor HironakaActualWeightedCoefficientCompression
  HironakaActualOriginalFormalHSTransfer HironakaActualCoefficientPresentationCentrePower
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaActualInvertibleIntrinsicHS HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicPointJets
  HironakaHolomorphicJetRankLoci HironakaActualCoherentWeightedCoefficientMarked
  RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers OrderTaylor HadamardBridge
  BlowupFlatCoordinates InvertibleIdealQuotient BlowupControlledTransform BlowupExceptionalDivisor
  MarkedIdeals MarkedIdeals.MarkedIdeal OkaRelationSheaf

variable {n : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

private theorem adapted_germ_mem_maximal_power_iff (y : Y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (h0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (f : Y → ℂ) (hf : HolomorphicAt n f y) (q : ℕ) :
    adaptedGerm y Θ h0 f hf∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q ↔
      (idealPow (pointIdeal n y) q).mem y f := by
  have h0T:=actualFlattening_target_zero_mem y Θ h0
  have hInv:=actualFlatteningInverseMap_zero y Θ h0
  have hfat : HolAt ((f∘actualFlatteningInverseMap y Θ)∘actualAffineTranslation n 0) 0 := by
    simpa only [actualAffineTranslation,zero_add,Function.comp_def,actualFlatteningInverseMap] using
      (holomorphic_adapted_iff y Θ h0 f).mpr hf
  have hfInv : HolomorphicAt n f (actualFlatteningInverseMap y Θ 0) := by rwa [hInv]
  have h:=actualNearbyGermEquiv_original_function y Θ hsrc 0 h0T f hfInv hfat
  have hL : HolGerm.mk ((f∘actualFlatteningInverseMap y Θ)∘actualAffineTranslation n 0) hfat=
      adaptedGerm y Θ h0 f hf := by
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z=>by
      simp only [Function.comp_def,actualAffineTranslation,zero_add,actualFlatteningInverseMap]
  have hInvFun : Θ.invFun 0=chartAt (ComplexModel n) y y := by
    rw [←h0,Θ.left_inv _ Θ.center_mem_source]
  have hR : chartTranslatedGerm y (actualFlatteningInverseMap y Θ 0)
      (actualNearbyPoint_mem_chart_source y Θ hsrc 0 h0T) f hfInv=
      chartTranslatedGerm y y (mem_chart_source _ y) f hf := by
    unfold chartTranslatedGerm translatedGerm
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z=>by
      rw [actualNearbyPoint_chart_value y Θ hsrc 0 h0T,hInvFun]
  have he : actualNearbyGermEquiv Θ 0 h0T (adaptedGerm y Θ h0 f hf)=
      chartTranslatedGerm y y (mem_chart_source _ y) f hf :=
    (congrArg (actualNearbyGermEquiv Θ 0 h0T) hL.symm).trans (h.trans hR)
  rw [←actual_maximal_power_map_algEquiv_iff (actualNearbyGermEquiv Θ 0 h0T) q,
    he,chartTranslatedGerm_mem_maximal_pow_iff]

private theorem adapted_ideal_cut_iff (I : GermIdeal n Y) (y : Y)
    (hI : ∀f,I.mem y f → HolomorphicAt n f y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (h0 : Θ.toFun (chartAt (ComplexModel n) y y)=0) (q : ℕ) :
    y∈cosupport n univ I q ↔
      adaptedIdeal I y Θ h0≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  constructor
  · intro hy
    apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    exact (adapted_germ_mem_maximal_power_iff y Θ hsrc h0 f hf q).mpr
      (mem_idealPow_of_vanishesToOrderOn_univ (hy.2 f hIf))
  · intro h
    refine ⟨mem_univ y,fun f hf=>?_⟩
    have hm:=h (Ideal.subset_span ⟨f,hI f hf,hf,rfl⟩)
    exact ⟨f,(adapted_germ_mem_maximal_power_iff y Θ hsrc h0 f (hI f hf) q).mp hm,
      Eventually.of_forall fun _ _=>rfl⟩

private theorem germ_power_cut_iff (g : HolGerm (ComplexModel n))
    (w r : ℕ) (hr : 0<r) :
    g^r∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(w*r) ↔
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^w := by
  constructor
  · intro hg
    obtain ⟨f,hf,rfl⟩:=HolGerm.exists_eq_mk g
    rw [←HolGerm.mk_pow _ hf r] at hg
    have hm:=(mem_maximalIdeal_pow_iff_point_power (eventually_differentiableAt_pow hf r) (w*r)).mp hg
    rw [Nat.mul_comm w r] at hm
    have hroot:=OrderMultiplicativity.mem_idealPow_of_pow_mem
      (hf.mono fun _ h=>h.mdifferentiableAt) (show 1≤r by omega) hm
    exact (mem_maximalIdeal_pow_iff_point_power hf w).mpr hroot
  · intro hg
    have hp:=Ideal.pow_mem_pow hg r
    simpa only [←pow_mul] using hp

private theorem weighted_compression_cut_iff {ι : Type} [Fintype ι]
    (w : ι → ℕ) (hw : ∀i,0<w i) (g : ι → HolGerm (ComplexModel n)) :
    weightedCompression w g≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^weightedCommonMark w ↔
      ∀i,g i∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^w i := by
  constructor
  · intro h i
    have hi : g i^(weightedCommonMark w/w i)∈
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^weightedCommonMark w : Ideal (HolGerm (ComplexModel n))):=
      h (Ideal.mem_span_range_self (x:=i))
    apply (germ_power_cut_iff (g i) (w i) _ (compressionExponent_pos w hw i)).mp
    simpa only [weight_mul_compressionExponent] using hi
  · intro h
    apply Ideal.span_le.mpr
    rintro x ⟨i,rfl⟩
    change g i^(weightedCommonMark w/w i)∈
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^weightedCommonMark w : Ideal (HolGerm (ComplexModel n)))
    have hp:=(germ_power_cut_iff (g i) (w i) _ (compressionExponent_pos w hw i)).mpr (h i)
    simpa only [weight_mul_compressionExponent] using hp

section Square
variable {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (y : Y)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y))=0)
    (hFlat : ∀{x : X},x∈(chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) x∈Φ.source →
      (x∈C ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x)∈coordinateSubsetPlane A))
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (hSquare : ∀z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source → π z∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=
        actualAnalyticBlowupMap A e b (Θ.toFun (chartAt (ComplexModel n) y z)))

include hπ he hΦsrc hFlat hΘsrc hΘ0 hSquare

/-- The ENTIRE genuine native controlled ideal, in its GIVEN target square. -/
theorem actual_native_controlled_stalk (I : GermIdeal n X) (hI : I.IsCoherent) (q : ℕ) :
    adaptedIdeal (controlledTransform hπ I q) y Θ hΘ0=
      (Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
        (adaptedIdeal I (π y) Φ hΦ0)).colon {(coordinateGerm e)^q} := by
  unfold controlledTransform
  rw [adaptedIdeal_colon_eq _ _ (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hI)
    (GermIdealPullbackCalculus.isCoherent_idealPow
      (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) q),
    actual_native_adapted_pullback_square I hI π hπ.contMDiff y A e b Φ hΦsrc hΦ0 Θ hΘsrc hΘ0 hSquare,
    actual_native_exceptional_power_stalk hπ y A e he b Φ hFlat Θ hΘsrc hΘ0 hSquare q,
    Ideal.colon_span]

/-- ANY SAME analytic quotient equations give the coherent WHOLE ideal of
the actual transformed record, before target orders, cuts or HS are used. -/
theorem actual_native_same_quotients_geometric_ideal
    (Q : MarkedIdeal n X) (hN : Q.N=univ) (hI : Q.ideal.IsCoherent)
    {ι : Type} [Fintype ι] (w : ι → ℕ) (F N : ι → HolGerm (ComplexModel n))
    (hSource : adaptedIdeal Q.ideal (π y) Φ hΦ0=weightedCompression w F)
    (hd : Q.d=weightedCommonMark w)
    (hProduct : ∀i,(coordinateGerm e)^w i*N i=actualAnalyticBlowupPullback A e b (F i)) :
    (Q.geoTransform C π).ideal.IsCoherent ∧
      adaptedIdeal (Q.geoTransform C π).ideal y Θ hΘ0=weightedCompression w N := by
  have hCoherent : (controlledTransform hπ Q.ideal Q.d).IsCoherent:=
    CoherentIdealColon.isCoherent_colon_of_isCoherent
      (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hI)
      (GermIdealPullbackCalculus.isCoherent_idealPow
        (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) Q.d)
  rw [geoTransform_ideal_eq_controlledTransform hN hI hπ]
  refine ⟨hCoherent,?_⟩
  rw [actual_native_controlled_stalk hπ y A e he b Φ hΦsrc hΦ0 hFlat Θ hΘsrc hΘ0 hSquare Q.ideal hI,
    hSource,hd,actual_same_normalized_quotients_weighted_colon A e b w F N hProduct]

/-- The actual native transformed cut is DERIVED from its whole ideal and
is exactly the original marks on the SAME normalized analytic quotients. -/
theorem actual_native_same_quotients_cosupport_iff
    (Q : MarkedIdeal n X) (hN : Q.N=univ) (hI : Q.ideal.IsCoherent)
    {ι : Type} [Fintype ι] (w : ι → ℕ) (hw : ∀i,0<w i) (F N : ι → HolGerm (ComplexModel n))
    (hSource : adaptedIdeal Q.ideal (π y) Φ hΦ0=weightedCompression w F)
    (hd : Q.d=weightedCommonMark w)
    (hProduct : ∀i,(coordinateGerm e)^w i*N i=actualAnalyticBlowupPullback A e b (F i)) :
    y∈(Q.geoTransform C π).cosupp ↔
      ∀i,actualUnshiftedTaylorAlgHom n (N i)∈genuineFormalVariables n^w i := by
  obtain ⟨hCoherent,hIdeal⟩:=actual_native_same_quotients_geometric_ideal hπ y A e he b Φ hΦsrc hΦ0
    hFlat Θ hΘsrc hΘ0 hSquare Q hN hI w F N hSource hd hProduct
  rw [MarkedIdeal.cosupp,geoTransform_N_eq_univ hN hπ,
    adapted_ideal_cut_iff _ y (fun _ hf=>holomorphicAt_of_mem_coherent _ hCoherent hf) Θ hΘsrc hΘ0,
    hIdeal,geoTransform_d,hd,weighted_compression_cut_iff w hw N]
  apply forall_congr'
  intro i
  exact (actual_maximal_power_iff_formal_coefficients_zero n (w i) (N i)).trans
    (mem_genuineFormalVariables_pow_iff_coefficients_zero n (w i) _).symm

/-- ANY representatives of the SAME analytic quotients realize the ENTIRE
actual marked transform on ONE produced open, including ALL ordered boundary
members and the born inverse centre, even when some members are empty. -/
theorem exists_actual_native_same_quotients_controlled_record
    (Q : MarkedIdeal n X) (hN : Q.N=univ) (hI : Q.ideal.IsCoherent)
    {ι : Type} [Fintype ι] (w : ι → ℕ) (F N : ι → HolGerm (ComplexModel n))
    (hSource : adaptedIdeal Q.ideal (π y) Φ hΦ0=weightedCompression w F)
    (hd : Q.d=weightedCommonMark w)
    (hProduct : ∀i,(coordinateGerm e)^w i*N i=actualAnalyticBlowupPullback A e b (F i))
    (f : ι → ComplexModel n → ℂ) (hf : ∀i,HolAt (f i) 0)
    (hF : ∀i,N i=HolGerm.mk (f i) (hf i)) :
    ∃U : TopologicalSpace.Opens (ComplexModel n),(0 : ComplexModel n)∈U ∧
      (U : Set (ComplexModel n))⊆Θ.target ∧
      (∀i,DifferentiableOn ℂ (f i) U) ∧
      MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (fun z : U=>actualFlatteningInverseMap y Θ z) (Q.geoTransform C π)=
        ⟨(fun z : U=>actualFlatteningInverseMap y Θ z) ⁻¹' (Q.geoTransform C π).N,
          (Q.geoTransform C π).E.map ((fun z : U=>actualFlatteningInverseMap y Θ z) ⁻¹' ·),
          weightedFunctionIdeal w (fun i (z : U)=>f i z),weightedCommonMark w⟩ := by
  obtain ⟨hCoherent,hIdeal⟩:=actual_native_same_quotients_geometric_ideal hπ y A e he b Φ hΦsrc hΦ0
    hFlat Θ hΘsrc hΘ0 hSquare Q hN hI w F N hSource hd hProduct
  exact exists_actual_native_weighted_record_of_adapted_span (Q.geoTransform C π) hCoherent y Θ
    hΘsrc hΘ0 w N hIdeal ((geoTransform_d Q C π).trans hd) f hf hF

end Square
end
end Hironaka.HironakaActualNativeControlledWeightedRecord
