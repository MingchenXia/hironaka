import Hironaka.Resolution.HironakaActualCentreWeightedControlledStalk
import Hironaka.Resolution.HironakaActualInheritedNeighborhoodMarkedHS
import Hironaka.Resolution.HironakaActualNormalAllDirectionGeometricConverse
import Hironaka.Resolution.HironakaActualLocalStrictSaturation
import Hironaka.Resolution.HironakaActualStrictContactBlowupCoordinates
import Hironaka.Resolution.HironakaActualInvertibleIntrinsicHS

/-! A genuine global native controlled cut internally supplies the SAME analytic
quotients, the whole actual geometric strict stalk, intrinsic HS equality,
and the original historical selector's actual contacts and Jacobians.
Only one step in normal codimension at least two is asserted; there is no
second-step state or global G8 closure claim.
Blueprint: hironaka-actual-global-inherited-cut-extension.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGlobalInheritedCut
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
 OkaRelationSheaf HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
 HironakaSmoothSubmersionGermIdealColon HironakaActualInvertibleIntrinsicHS
 HironakaSmoothCentreNearbyStalks HironakaSmoothCentreCoherentDomain
 HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
 HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
 RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers OrderTaylor HadamardBridge
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
 [IsComplexManifold n Y]

private theorem actual_equiv_mem_maximal_power_iff
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)) (q : ℕ)
    (g : HolGerm (ComplexModel n)) :
    E g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q ↔
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  have hmap (D : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)) :
      Ideal.map D.toRingEquiv.toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q)=
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
    rw [Ideal.map_pow]
    exact congrArg (fun J : Ideal (HolGerm (ComplexModel n))=>J^q)
      (IsLocalRing.map_ringEquiv_maximalIdeal D.toRingEquiv)
  constructor
  · intro hg
    have h:=Ideal.mem_map_of_mem E.symm.toRingEquiv.toRingHom hg
    rw [hmap] at h
    change E.symm (E g)∈_ at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · intro hg
    have h:=Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hg
    rwa [hmap] at h

private theorem actual_adapted_germ_mem_maximal_power_iff (y : Y)
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
  have h := actualNearbyGermEquiv_original_function y Θ hsrc 0 h0T f hfInv hfat
  have hL : HolGerm.mk ((f∘actualFlatteningInverseMap y Θ)∘actualAffineTranslation n 0) hfat=
      adaptedGerm y Θ h0 f hf := by
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z=>by simp only [Function.comp_def,actualAffineTranslation,zero_add,actualFlatteningInverseMap]
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
  rw [←actual_equiv_mem_maximal_power_iff (actualNearbyGermEquiv Θ 0 h0T) q,
    he,chartTranslatedGerm_mem_maximal_pow_iff]

private theorem actual_adapted_ideal_cut_iff (A : GermIdeal n Y) (y : Y)
    (hA : ∀f,A.mem y f → HolomorphicAt n f y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (h0 : Θ.toFun (chartAt (ComplexModel n) y y)=0) (q : ℕ) :
    y∈cosupport n univ A q ↔
      adaptedIdeal A y Θ h0≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  constructor
  · intro hy
    apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hAf,rfl⟩
    exact (actual_adapted_germ_mem_maximal_power_iff y Θ hsrc h0 f hf q).mpr
      (mem_idealPow_of_vanishesToOrderOn_univ (hy.2 f hAf))
  · intro h
    refine ⟨mem_univ y,fun f hf=>?_⟩
    have hm := h (Ideal.subset_span ⟨f,hA f hf,hf,rfl⟩)
    exact ⟨f,(actual_adapted_germ_mem_maximal_power_iff y Θ hsrc h0 f (hA f hf) q).mp hm,
      Eventually.of_forall fun _ _=>rfl⟩

private theorem actual_germ_power_cut_iff (g : HolGerm (ComplexModel n))
    (w r : ℕ) (hr : 0<r) :
    g^r∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(w*r) ↔
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^w := by
  constructor
  · intro hg
    obtain ⟨f,hf,rfl⟩:=HolGerm.exists_eq_mk g
    rw [←HolGerm.mk_pow _ hf r] at hg
    have hm := (mem_maximalIdeal_pow_iff_point_power (eventually_differentiableAt_pow hf r) (w*r)).mp hg
    rw [Nat.mul_comm w r] at hm
    have hroot := OrderMultiplicativity.mem_idealPow_of_pow_mem
      (hf.mono fun _ h=>h.mdifferentiableAt) (show 1≤r by omega) hm
    exact (mem_maximalIdeal_pow_iff_point_power hf w).mpr hroot
  · intro hg
    have hp:=Ideal.pow_mem_pow hg r
    simpa only [←pow_mul] using hp

open HironakaActualWeightedCoefficientCompression
private theorem actual_weighted_compression_cut_iff {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (hw : ∀i,0<w i) (g : ι → HolGerm (ComplexModel n)) :
    weightedCompression w g≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^weightedCommonMark w ↔
      ∀i,g i∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^w i := by
  constructor
  · intro h i
    have hi : g i^(weightedCommonMark w/w i)∈
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^weightedCommonMark w : Ideal (HolGerm (ComplexModel n))) :=
      h (Ideal.mem_span_range_self (x:=i))
    apply (actual_germ_power_cut_iff (g i) (w i) _ (compressionExponent_pos w hw i)).mp
    simpa only [weight_mul_compressionExponent] using hi
  · intro h
    apply Ideal.span_le.mpr
    rintro x ⟨i,rfl⟩
    change g i^(weightedCommonMark w/w i)∈
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^weightedCommonMark w : Ideal (HolGerm (ComplexModel n)))
    have hp:=(actual_germ_power_cut_iff (g i) (w i) _ (compressionExponent_pos w hw i)).mpr (h i)
    simpa only [weight_mul_compressionExponent] using hp

open HironakaActualCentreWeightedControlledStalk HironakaActualCoherentWeightedCoefficientMarked
 HironakaActualFiniteCoefficientIdeals HironakaActualLocalCoefficientStrictGenerators
 HironakaActualAnalyticBlowupTaylor HironakaActualCoefficientPresentationCentrePower
 HironakaActualCoefficientAnalyticBlowup HironakaRelativeNormalIdeal
 HironakaActualFormalBlowupMemberGeneration HironakaActualFormalCoordinatePowerDivision
 MarkedIdeals MarkedIdeals.MarkedIdeal BlowupControlledTransform InvertibleIdealQuotient
section CoordinateActual
variable {d t : ℕ} {Z : Type} [TopologicalSpace Z]
 [ChartedSpace (ComplexModel (d+t)) Z] [IsComplexManifold (d+t) Z]

theorem exists_actual_global_controlled_weighted_cut
    (U : TopologicalSpace.Opens (ComplexModel (d+t))) (h0U : (0 : ComplexModel (d+t))∈U)
    {ι : Type*} [Fintype ι] (w : ι → ℕ) (hw : ∀i,0<w i)
    (c : ι → ComplexModel (d+t) → ℂ)
    (hc : ∀i,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (c i) U)
    (hCos : ∀i,(U : Set (ComplexModel (d+t)))∩complexCoordinatePlane (d+t) d⊆
      cosupport (d+t) univ (actualPrincipalCoefficientIdeal (d+t) (c i)) (w i))
    (π : Z → U)
    (hπ : IsBlowupAlong (d+t) ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+t))=0) :
    let cg:=fun i=>HolGerm.mk (c i)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U).mono fun _ hz=>hz.differentiableAt)
    let M : MarkedIdeal (d+t) U:=⟨univ,[],weightedFunctionIdeal w (fun i (z : U)=>c i z),weightedCommonMark w⟩
    ∃(e : Fin (d+t))(b : Fin (d+t) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0),
      d≤e.val ∧ (∀i : Fin (d+t),i.val<d → b i=0) ∧ b e=0 ∧
      Θ.source⊆(chartAt (ComplexModel (d+t)) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
        chartAt (ComplexModel (d+t)) y z∈Θ.source →
        (π z : ComplexModel (d+t))=actualAnalyticBlowupMap (actualTangentCentreVariables d t) e b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z))) ∧
      ∃H : ι → HolGerm (ComplexModel (d+t)),
        (∀i,coordinateGerm e^w i*H i=actualAnalyticBlowupPullback (actualTangentCentreVariables d t) e b (cg i)) ∧
        (∃hp : ∀i,cg i∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^w i,
          ∃heS : e∈actualTangentCentreVariables d t,∀i,actualUnshiftedTaylorAlgHom (d+t) (H i)=
            actualNormalizedFormalMember (actualTangentCentreVariables d t) e heS b (w i) (actualUnshiftedTaylorAlgHom (d+t) (cg i))
              (actualTaylor_mem_coordinateCentre_pow _ _ _ (hp i))) ∧
        adaptedIdeal (M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π).ideal y Θ hΘ0=weightedCompression w H ∧
        (y∈(M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π).cosupp ↔∀i,H i∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^w i) := by
  let cg:=fun i=>HolGerm.mk (c i)
    ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U).mono fun _ hz=>hz.differentiableAt)
  let M : MarkedIdeal (d+t) U:=⟨univ,[],weightedFunctionIdeal w (fun i (z : U)=>c i z),weightedCommonMark w⟩
  have hPower (i) : cg i∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^w i := by
    rw [actualAnalyticCoordinateIdeal_normal]
    exact mk_mem_normalIdeal_pow_of_local_cosupport d t (w i)
      (actualPrincipalCoefficientIdeal (d+t) (c i)) U U.isOpen h0U
      (coherentOn_actualPrincipalCoefficientIdeal (d+t) (c i) U U.isOpen (hc i)) (hCos i) _
      (isInSpanAt_self (S := (·=c i)) rfl (holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U))
  obtain ⟨e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hSquare,hStalk⟩:=
    exists_actual_coordinate_centre_weighted_stalk U h0U d π hπ y hy w c hc
  have heS : e∈actualTangentCentreVariables d t := by rw [actualTangentCentreVariables_eq_tail];exact he
  rw [←actualTangentCentreVariables_eq_tail d t] at hSquare hStalk
  obtain ⟨_hR,H,hH,hT,_hTotal,hColon⟩:=
    exists_actual_weighted_compression_blowup (actualTangentCentreVariables d t) e heS b w hw cg hPower
  have hcu (i : ι) : MDifferentiable 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (fun z : U=>c i z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) z.property).comp_contMDiff
      (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=U)).contMDiffAt)).mdifferentiableAt
  have hI := isCoherent_weightedFunctionIdeal w (fun i (z : U)=>c i z) hcu
  have hIdeal : adaptedIdeal (M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π).ideal y Θ hΘ0=weightedCompression w H := by
    rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M) rfl hI hπ,hStalk,hColon]
  refine ⟨e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hSquare,H,hH,⟨hPower,heS,hT⟩,hIdeal,?_⟩
  rw [MarkedIdeal.cosupp,geoTransform_N_eq_univ (𝔪:=M) rfl hπ]
  change y∈cosupport (d+t) univ (M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π).ideal (weightedCommonMark w) ↔ _
  rw [actual_adapted_ideal_cut_iff _ y (fun f hf=>?_) Θ hΘsrc hΘ0,hIdeal,
    actual_weighted_compression_cut_iff w hw H]
  rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M) rfl hI hπ] at hf
  exact (mem_colon_iff.mp hf).1
end CoordinateActual

open HironakaActualRelativeNormalJetDivision HironakaActualFormalInitialDiagram
 HironakaActualNormalZeroAnalyticSaturation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualNormalAllDirectionGeometricConverse HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaActualRelativeNormalJetDivision
open HironakaRelativeNormalMonomialBasis HironakaActualRelativeStandardnessBlockSupport
private theorem same_inherited_quotients_hs_and_historical_legality
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀a,G.germs a∈I)
    (q e : Fin n) (hqe : q≤e) (b : Fin n → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (H : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → HolGerm (ComplexModel n))
    (hH : ∀a,coordinateGerm e^normalExponentDegree a.val*H a=
      actualAnalyticBlowupPullback (Set.Ici q) e b (G.germs a))
    (hOrder : ∀a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀k,actualFixedSelectorContactAt S G.germs k) :
    (∀ℓ,hilbertSamuelValue (Ideal.span (range H)) ℓ=hilbertSamuelValue I ℓ) ∧
      ∀k,actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I) k⊆(Set.Ici q)\{e} ∧
        ∀i∈actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal n I) k,b i=0 := by
  have hEq (a) : sameAnalyticNormalNormalizedVertex n I G q e hqe b hp a=H a := by
    apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val)
      (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
    exact (sameAnalyticNormalNormalizedVertex_product n I G q e hqe b hp a).trans (hH a).symm
  have hOrders : ∀a,sameAnalyticNormalNormalizedVertex n I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val := by
    intro a
    rw [hEq]
    exact hOrder a
  have hHS (ℓ) := hilbertSamuelValue_same_normal_ideal_eq_of_marked_orders n I G hmem q e hqe b hp hOrders ℓ
  have hLegal := actual_normal_marked_orders_preserve_same_historical_selector n I G hmem
    q e hqe b hp hOrders S hred hadapt
  refine ⟨?_,?_⟩
  · intro ℓ
    have hFun : sameAnalyticNormalNormalizedVertex n I G q e hqe b hp = H := funext hEq
    simpa only [sameAnalyticNormalNormalizedIdeal,hFun] using hHS ℓ
  · obtain ⟨_hFormal,hAll⟩:=hLegal
    exact fun k=>(hAll k).1

section ActualHistoricalCut
variable {d t : ℕ} {Z : Type} [TopologicalSpace Z]
 [ChartedSpace (ComplexModel (d+t)) Z] [IsComplexManifold (d+t) Z]
theorem exists_actual_cut_hs_and_historical_legality
    (ht : 0<t) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (G : ActualAnalyticInheritedFamily (d+t) 0 (analyticZeroTaylorIdeal (d+t) I))
    [Fintype (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I))]
    (hmem : ∀a,G.germs a∈I)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I),0<normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀k,actualFixedSelectorContactAt S G.germs k)
    (U : TopologicalSpace.Opens (ComplexModel (d+t))) (h0U : (0 : ComplexModel (d+t))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) → ComplexModel (d+t) → ℂ)
    (hc : ∀a,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀a,HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀a,(U : Set (ComplexModel (d+t)))∩complexCoordinatePlane (d+t) d⊆
      cosupport (d+t) univ (actualPrincipalCoefficientIdeal (d+t) (c a)) (normalExponentDegree a.val))
    (π : Z → U)
    (hπ : IsBlowupAlong (d+t) ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+t))=0) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)=>normalExponentDegree a.val
    let M : MarkedIdeal (d+t) U:=⟨univ,[],weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    y∈(M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π).cosupp →
    ∃(e : Fin (d+t))(b : Fin (d+t) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
      (H : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) → HolGerm (ComplexModel (d+t))),
      d≤e.val ∧ b e=0 ∧ Θ.source⊆(chartAt (ComplexModel (d+t)) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
        chartAt (ComplexModel (d+t)) y z∈Θ.source →
        (π z : ComplexModel (d+t))=actualAnalyticBlowupMap (actualTangentCentreVariables d t) e b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z))) ∧
      (∀a,G.germs a∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^w a) ∧
      (∀a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^w a) ∧
      (∀a,coordinateGerm e^w a*H a=actualAnalyticBlowupPullback (actualTangentCentreVariables d t) e b (G.germs a)) ∧
      adaptedIdeal (M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π).ideal y Θ hΘ0=weightedCompression w H ∧
      (∀ℓ,hilbertSamuelValue (Ideal.span (range H)) ℓ=hilbertSamuelValue I ℓ) ∧
      (e∉fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)) ∧
        ∀i∈fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)),b i=0) ∧
      ∀k,actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) k⊆
        (actualTangentCentreVariables d t)\{e} ∧
        ∀i∈actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) k,b i=0 := by
  dsimp only
  intro hcut
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)=>normalExponentDegree a.val
  obtain ⟨e,b,Θ,hΘ0,he,_hbt,hbe,hΘsrc,hSquare,H,hH,⟨hp,_heS,_hTaylor⟩,hIdeal,hCut⟩ :=
    exists_actual_global_controlled_weighted_cut U h0U w hw c hc hCos π hπ y hy
  have hOrders:=hCut.mp hcut
  have hProducts : ∀a,coordinateGerm e^normalExponentDegree a.val*H a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) e b (G.germs a) := by
    intro a
    simpa only [hrep] using hH a
  let q : Fin (d+t):=⟨d,by omega⟩
  have hTail : actualTangentCentreVariables d t=Set.Ici q := by
    ext i
    rw [actualTangentCentreVariables_eq_tail]
    rfl
  have hPower : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val := by
    intro a
    simpa only [hrep,hTail] using hp a
  have hProducts' : ∀a,coordinateGerm e^normalExponentDegree a.val*H a=
      actualAnalyticBlowupPullback (Set.Ici q) e b (G.germs a) := by
    simpa only [hTail] using hProducts
  obtain ⟨hHS,hLegal⟩ := same_inherited_quotients_hs_and_historical_legality I G hmem q e he b
    hPower H hProducts' hOrders S hred hadapt
  have hEssential : e∉fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)) ∧
      ∀i∈fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)),b i=0 := by
    constructor
    · rintro ⟨a,ha⟩
      have hBlock : e∈actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) (normalExponentDegree a.val) := ⟨a,le_rfl,ha⟩
      exact ((hLegal _).1 hBlock).2 rfl
    · rintro i ⟨a,ha⟩
      exact (hLegal (normalExponentDegree a.val)).2 i ⟨a,le_rfl,ha⟩
  have hPowerTail : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^w a := by
    simpa only [hrep] using hp
  refine ⟨e,b,Θ,hΘ0,H,he,hbe,hΘsrc,hSquare,hPowerTail,hOrders,hProducts,hIdeal,hHS,hEssential,?_⟩
  simpa only [hTail] using hLegal
end ActualHistoricalCut

open HironakaActualPointGeometricBennett BlowupFlatCoordinates HironakaActualLocalStrictSaturation HironakaActualStrictContactBlowupCoordinates
 HironakaActualFixedFlatteningHSComparison HironakaActualCoefficientPresentationCentrePower
section ActualGlobalStrict
variable {d t : ℕ} {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]
 [ChartedSpace (ComplexModel (d+t)) X] [ChartedSpace (ComplexModel (d+t)) Z]
 [IsComplexManifold (d+t) X] [IsComplexManifold (d+t) Z]
private theorem same_quotients_actual_global_strict_stalk
    (ht : 2≤t) (π : Z → X)
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ π)
    (y : Z) (W : Set X) (hW : (vanishingIdeal (n:=d+t) W).IsCoherent)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+t)) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π y))=0)
    (e : Fin (d+t)) (he : d≤e.val) (b : Fin (d+t) → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel (d+t)) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
    (hnormal : ∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π z))=
        actualAnalyticBlowupMap (actualTangentCentreVariables d t) e b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z)))
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+t) W) (π y) Φ) 0))
    (G : ActualAnalyticInheritedFamily (d+t) 0 (analyticZeroTaylorIdeal (d+t) I))
    (hmem : ∀a,G.germs a∈I)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^normalExponentDegree a.val)
    (H : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) → HolGerm (ComplexModel (d+t)))
    (hH : ∀a,coordinateGerm e^normalExponentDegree a.val*H a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) e b (G.germs a))
    (hOrder : ∀a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^normalExponentDegree a.val) :
    let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+t) (strictTransform (d+t) π W)) y Θ) 0)
    K=Ideal.span (range H) ∧
      ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t) π W)) y ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=d+t) W) (π y) ℓ := by
  let q : Fin (d+t):=⟨d,by omega⟩
  let j : Fin t:=⟨e.val-d,by have hlt:=e.isLt;omega⟩
  have hj : j.natAdd d=e := by apply Fin.ext;dsimp only [j,Fin.natAdd];omega
  have hTail : actualTangentCentreVariables d t=Set.Ici q := by
    rw [actualTangentCentreVariables_eq_tail];rfl
  have hPower : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val := by
    simpa only [hTail] using hp
  have hEq (a) : sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower a=H a := by
    apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val)
      (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
    exact (sameAnalyticNormalNormalizedVertex_product (d+t) I G q e he b hPower a).trans
      (by simpa only [hTail,coordinateGerm] using (hH a).symm)
  have hFun : sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower=H:=funext hEq
  have hOrders : ∀a,sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^normalExponentDegree a.val := by
    simpa only [hFun] using hOrder
  obtain ⟨_M,_hBound,_hColon,hSat,hHS⟩:=
    exists_same_normal_analytic_fixed_colon_and_hs_of_marked_orders (d+t) I G hmem q e he b hPower hOrders
  have hA : actualTangentCentreVariables d t={i : Fin (d+t) | d ≤ i.val}:=actualTangentCentreVariables_eq_tail d t
  have hnormal' : ∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π z))=
        actualAnalyticBlowupMap {i : Fin (d+t) | d ≤ i.val} e b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z)) := by simpa only [hA] using hnormal
  have hchart:=strictFlattenedOriginIdeal_eq_model hπ y d Φ hΦsrc e b Θ hΘsrc hΘ0 hnormal' W
  rw [←hA,←hj] at hchart
  have hK : originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+t) (strictTransform (d+t) π W)) y Θ) 0)=
      sameAnalyticNormalNormalizedIdeal (d+t) I G q e he b hPower := by
    ext g
    rw [hchart,mem_fixedFlattening_strict_iff_power ht j b W hW (π y) Φ hΦsrc hΦ0]
    rw [←hI]
    simpa only [hj,hTail] using (hSat g).symm
  refine ⟨?_,?_⟩
  · simpa only [sameAnalyticNormalNormalizedIdeal,hFun] using hK
  · intro ℓ
    have hTarget:=hilbertSamuelAt_strict_eq_fixedFlattening_model hπ y d Φ hΦsrc e b Θ hΘsrc hΘ0 hnormal' W ℓ
    rw [←hA,←hj,hilbertSamuelAt_model_zero,←hchart,hK] at hTarget
    rw [hTarget,hHS]
    rw [hilbertSamuelAt_eq_fixedFlattening_model (π y) Φ hΦsrc hΦ0 W ℓ,
      hilbertSamuelAt_model_zero,←originalFlattenedVanishingOriginIdeal_eq_model (π y) Φ hΦsrc hΦ0,←hI]
end ActualGlobalStrict

open HironakaActualInheritedNextBlockGraph HironakaActualCauchyCoefficientLimits
 HironakaActualFixedInheritedSelectorBlowup HironakaActualInheritedAnalyticBlockJacobian
 HironakaActualOriginalTaylorDerivatives
private theorem normalized_same_historical_selector_contact_and_jacobian
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀a,G.germs a∈I)
    (q e : Fin n) (hqe : q≤e) (b : Fin n → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex n I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀k,actualFixedSelectorContactAt S G.germs k) :
    let H:=sameAnalyticNormalNormalizedVertex n I G q e hqe b hp
    (∀k,actualFixedSelectorContactAt S H k) ∧
      ∀k,actualFixedSelectorJacobian S H k=actualFixedSelectorJacobian S G.germs k := by
  obtain ⟨hpf,hAll⟩:=actual_normal_marked_orders_preserve_same_historical_selector n I G hmem
    q e hqe b hp hOrder S hred hadapt
  let H:=sameAnalyticNormalNormalizedVertex n I G q e hqe b hp
  have hDerivative (k) (j : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) k) :
      actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S H (fixedSelectorBlockEssential k j))=
        actualNormalizedFixedSelectorDerivative G S k (Set.Ici q) e (Set.mem_Ici.mpr hqe) b hpf j := by
    unfold actualFixedSelectorDerivative actualNormalizedFixedSelectorDerivative
    rw [actualTaylor_actualAnalyticMultiDerivative,actualTaylor_sameAnalyticNormalNormalizedVertex]
  constructor
  · intro k j
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ _).mpr
    rw [map_actualAnalyticCoordinateBlockIdeal_actualTaylor]
    have hm:=(hAll k).2.1 j
    rw [←hDerivative k j] at hm
    exact hm
  · intro k
    ext j i
    have heq:=congrArg (fun A=>A j i) ((hAll k).2.2.1)
    change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualFixedSelectorDerivative S H (fixedSelectorBlockEssential k j)))=_
    rw [←actualTaylor_coeff_zero,actualTaylor_actualAnalyticCoordinateDerivative,hDerivative k j]
    exact heq


section CompleteActualCut
variable {d t : ℕ} {Z : Type} [TopologicalSpace Z]
 [ChartedSpace (ComplexModel (d+t)) Z] [IsComplexManifold (d+t) Z]
theorem exists_actual_global_cut_strict_hs_and_historical_legality
    (ht : 2≤t) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (G : ActualAnalyticInheritedFamily (d+t) 0 (analyticZeroTaylorIdeal (d+t) I))
    [Fintype (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I))]
    (hmem : ∀a,G.germs a∈I)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I),0<normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀k,actualFixedSelectorContactAt S G.germs k)
    (U : TopologicalSpace.Opens (ComplexModel (d+t))) (h0U : (0 : ComplexModel (d+t))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) → ComplexModel (d+t) → ℂ)
    (hc : ∀a,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀a,HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀a,(U : Set (ComplexModel (d+t)))∩complexCoordinatePlane (d+t) d⊆
      cosupport (d+t) univ (actualPrincipalCoefficientIdeal (d+t) (c a)) (normalExponentDegree a.val))
    (π : Z → U)
    (hπ : IsBlowupAlong (d+t) ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+t))=0)
    (W : Set U) (hW : (vanishingIdeal (n:=d+t) W).IsCoherent)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+t)) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π y))=0)
    (hΦid : Φ.toFun=id) (hΦdom : Φ.source=(U : Set (ComplexModel (d+t))))
    (hI : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+t) W) (π y) Φ) 0)) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)=>normalExponentDegree a.val
    let M : MarkedIdeal (d+t) U:=⟨univ,[],weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    y∈(M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π).cosupp →
    ∃(e : Fin (d+t))(b : Fin (d+t) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
      (H : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) → HolGerm (ComplexModel (d+t))),
      adaptedIdeal (M.geoTransform ((Subtype.val : U → ComplexModel (d+t)) ⁻¹' complexCoordinatePlane (d+t) d) π).ideal y Θ hΘ0=weightedCompression w H ∧
      originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+t) (strictTransform (d+t) π W)) y Θ) 0)=Ideal.span (range H) ∧
      (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t) π W)) y ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=d+t) W) (π y) ℓ) ∧
      (e∉fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)) ∧
        ∀i∈fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I)),b i=0) ∧
      (∀k,actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) k⊆
        (actualTangentCentreVariables d t)\{e} ∧
        ∀i∈actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) k,b i=0) ∧
      (∀k,actualFixedSelectorContactAt S H k) ∧
      ∀k,actualFixedSelectorJacobian S H k=actualFixedSelectorJacobian S G.germs k := by
  dsimp only
  intro hcut
  obtain ⟨e,b,Θ,hΘ0,H,he,_hbe,hΘsrc,hSquare,hp,hOrders,hProducts,hIdeal,_hHS,hEssential,hLegal⟩ :=
    exists_actual_cut_hs_and_historical_legality (by omega) I G hmem hw S hred hadapt U h0U c hc hrep hCos π hπ y hy hcut
  have hnormal : ∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π z))=
        actualAnalyticBlowupMap (actualTangentCentreVariables d t) e b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z)) := by
    intro z hz hzΘ
    constructor
    · change π z∈(chartAt (ComplexModel (d+t)) (π y)).source ∩ _
      constructor
      · rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
        rw [OpenPartialHomeomorph.subtypeRestr_source]
        exact mem_univ _
      · rw [hΦdom]
        change chartAt (ComplexModel (d+t)) (π y) (π z)∈U
        rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
        exact (π z).property
    · rw [hΦid]
      change chartAt (ComplexModel (d+t)) (π y) (π z)=_
      rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
      exact hSquare z hz hzΘ
  obtain ⟨hStrict,hIntrinsic⟩:=same_quotients_actual_global_strict_stalk ht π hπ.contMDiff y W hW
    Φ hΦsrc hΦ0 e he b Θ hΘsrc hΘ0 hnormal I hI G hmem hp H hProducts hOrders
  let q : Fin (d+t):=⟨d,by omega⟩
  have hTail : actualTangentCentreVariables d t=Set.Ici q := by
    rw [actualTangentCentreVariables_eq_tail];rfl
  have hPower : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val := by
    intro a
    rw [←hTail]
    exact hp a
  have hEq (a) : sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower a=H a := by
    apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val)
      (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
    exact (sameAnalyticNormalNormalizedVertex_product (d+t) I G q e he b hPower a).trans
      (by simpa only [hTail,coordinateGerm] using (hProducts a).symm)
  have hFun : sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower=H:=funext hEq
  have hStockOrders : ∀a,sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^normalExponentDegree a.val := by
    simpa only [hFun] using hOrders
  obtain ⟨hContact,hJac⟩:=normalized_same_historical_selector_contact_and_jacobian I G hmem
    q e he b hPower hStockOrders S hred hadapt
  rw [hFun] at hContact hJac
  exact ⟨e,b,Θ,hΘ0,H,hIdeal,hStrict,hIntrinsic,hEssential,hLegal,hContact,hJac⟩
end CompleteActualCut

end
end Hironaka.HironakaActualGlobalInheritedCut
