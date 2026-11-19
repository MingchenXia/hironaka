import Hironaka.Resolution.HironakaG1ProperNormalLowerCanonical
import Hironaka.Resolution.HironakaOriginalFamilyDepthStability
import Hironaka.Resolution.HironakaActualNativeSectionInitialBar
import Hironaka.Resolution.HironakaActualSectionMemberRestriction
import Hironaka.Resolution.HironakaActualSectionInitialBoundaryRegime

/-! Actual native histories from ordinary original proper-normal lower CAN.
Whole initial native records and every chronological comparison are derived.
Blueprint FIRST: hironaka-g1-proper-normal-native-history.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperNormalNativeHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport BlowupTowerIsomorphism
  ResolutionInvariantSpec CanonicalCentres ResolutionDriver HomogenizedIdealAlong
  StepOneValue CoefficientIdealRestriction GermIdealPullbackCalculus
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaActualNativeSectionInitialBar HironakaActualSectionMemberRestriction
  HironakaActualSectionInitialBoundaryRegime HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeInvariantDomain HironakaActualNativeHistoryExistence
  HironakaActualNativeSectionOrderHistory HironakaActualNativeRecursiveValues
  HironakaOriginalFamilyDepthStability HironakaActualRawRecordPullbacks
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalLowerCanonical
  HironakaG1CoefficientRecodingCanonical HironakaG8CoefficientBoundaryLocal
  HironakaG11InvBMClass SubmanifoldChartedSpace NormalCrossings
  HironakaSmoothSubmersionOrderedChoiceImageTrace

private theorem section_domain {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) : IsInvDomain k (sectionMarked Q) :=
  section_projected_domain k Q.N Q.E Q.ideal Q.d hQ

/-- ENTIRE actual zero-section coefficient/bar record, at its TRUE double
mark and with the original proper carrier and whole boundary. -/
theorem section_coefficient_bar_record {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    HironakaSmoothSubmersionCoefficientIdeals.markedPullback (m := n) (zeroSection U)
      (sectionBarCoefficient Q)=coeffMarkedAlong (barMarked (X := CMfd.of (n := n) U) Q) := by
  let S := sectionMarked Q
  have hSI := isCoherent_pullback (projection_contMDiff U) hQ.isWellFormed.isCoherent
  have hTrace : GermIdeal.pullback (m := n) (zeroSection U)
      (GermIdeal.pullback (m := n+1) (projection U) Q.ideal)=Q.ideal := by
    have he : projection U ∘ zeroSection U=id := by
      funext x
      apply Subtype.ext
      exact HironakaRelativeNormalIdeal.tangentProjection_tangentInclusion n 1 x.val
    rw [←coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U)
      Q.ideal hQ.isWellFormed.isCoherent,he,BlowupControlledTransform.pullback_id hQ.isWellFormed.isCoherent]
  have hBarTrace := bar_ideal_section Q.N hQ.isWellFormed.isClosedSubmanifold_N Q.E
    (GermIdeal.pullback (m := n+1) (projection U) Q.ideal) hSI Q.d
  rw [hTrace] at hBarTrace
  have hS := section_domain Q hQ
  have hBS := HironakaCoherentTransformExtension.isInvDomain_barMarked
    (X := CMfd.of (n := n+1) (productOpen U)) S hS
  have h := markedPullback_section_coeffMarkedAlong Q.N hQ.isWellFormed.isClosedSubmanifold_N Q.E
    (barMarked (X := CMfd.of (n := n+1) (productOpen U)) S).ideal hBS.isWellFormed.isCoherent
    (barMarked (X := CMfd.of (n := n+1) (productOpen U)) S).d
  have hBase : (⟨Q.N,Q.E,GermIdeal.pullback (m := n) (zeroSection U)
      (barMarked (X := CMfd.of (n := n+1) (productOpen U)) S).ideal,
      (barMarked (X := CMfd.of (n := n+1) (productOpen U)) S).d⟩ : MarkedIdeal n U)=
      barMarked (X := CMfd.of (n := n) U) Q := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · rfl
    · exact hBarTrace
    · rfl
  rw [hBase] at h
  exact h

/-- Actual native zero-plane input, derived from the WHOLE original record
and genuine marked-pullback composition, without a supplied trace packet. -/
theorem native_input_record {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    MarkedIdeal.pullback (nativeZeroSectionEquiv U)
      (nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionBarCoefficient Q))=
      coeffMarkedAlong (barMarked (X := CMfd.of (n := n) U) Q) := by
  let := chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  have := isComplexManifold_chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  have hV := (kept_normal_lower_data Q hQ).2.1
  have hComp := HironakaSmoothSubmersionOrderedChoiceImageTrace.whole_markedPullback_comp
    (contMDiff_val (Nat.le_succ n) (zeroPlane_regular U))
    (nativeZeroSectionEquiv U).contMDiff (sectionBarCoefficient Q) hV.isWellFormed.isCoherent
  exact hComp.symm.trans (section_coefficient_bar_record Q hQ)

private theorem zeroPlane_closed {n : ℕ} (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n) (M := U))).1

/-- Ordinary Q and actual ORIGINAL kept-lower CAN INTERNALLY produce the
genuine native Lift/base history, whole labels/cosupport/maps/values/centres.
No native CAN, trace, lift or desired comparison packet is supplied. -/
theorem exists_original_kept_normal_native_history {n k : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hCan : IsCanonical (keptNormalLower Q) ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q)) T) :
    ∃(C : Set Y)(hCc : IsClosed C)(hC : ∀y∈C,RegularAtDim (n := n+1) C y n)
      (N : BlowupTower (nativeManifold (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Y := Y) (Nat.le_succ n) C hC)),
      Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U)
        (sectionBarCoefficient Q).E T C hCc hC N ∧
      let H := transport (nativeZeroSectionEquiv U) N
      let j : H.target → Y := fun z => (H.back z).val
      let D := coeffMarkedAlong (barMarked (X := CMfd.of (n := n) U) Q)
      H.tower.length=T.length ∧
        IsCanonical D ((invFamily hn k).inv D) H.tower ∧
        IsCanonical (barMarked (X := CMfd.of (n := n) U) Q)
          ((invFamily hn k).inv (barMarked (X := CMfd.of (n := n) U) Q)) H.tower ∧
        IsGeoTestTower D H.tower ∧ IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) Q) H.tower ∧
        (∀z,T.proj (j z)=zeroSection U (H.tower.proj z)) ∧
        (geoTransformAlong D H.tower).E=(geoTransformAlong (keptNormalLower Q) T).E.map (j ⁻¹' ·) ∧
        (geoTransformAlong D H.tower).cosupp=j ⁻¹' (geoTransformAlong (keptNormalLower Q) T).cosupp ∧
        j '' (geoTransformAlong D H.tower).cosupp=(geoTransformAlong (keptNormalLower Q) T).cosupp ∧
        (∀z∈(geoTransformAlong D H.tower).cosupp,
          (invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q) T (j z)=
            HironakaActualSectionBoundaryDimension.sameIndexMap 1 k ((invFamily hn k).inv D H.tower z)) ∧
        maxLocus ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q) T)
            (geoTransformAlong (keptNormalLower Q) T).cosupp=
          j '' maxLocus ((invFamily hn k).inv D H.tower) (geoTransformAlong D H.tower).cosupp ∧
        maxLocus ((invFamily (Nat.succ_pos n) k).inv (keptNormalLower Q) T)
            (geoTransformAlong (keptNormalLower Q) T).cosupp=
          j '' maxLocus ((invFamily hn k).inv (barMarked (X := CMfd.of (n := n) U) Q) H.tower)
            (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) Q) H.tower).cosupp ∧
        (IsGeoResolution (keptNormalLower Q) T ↔ IsGeoResolution D H.tower) ∧
        (IsGeoResolution (keptNormalLower Q) T ↔
          IsGeoResolution (barMarked (X := CMfd.of (n := n) U) Q) H.tower) := by
  let R := keptNormalLower Q
  let V := sectionBarCoefficient Q
  let D := coeffMarkedAlong (barMarked (X := CMfd.of (n := n) U) Q)
  obtain ⟨hR,hV,hN,hE,hd,hL,_hDim,_hGapR,_hGapV,_hNorm,_hExp⟩ := kept_normal_lower_data Q hQ
  have hCanV := (invFamily_isCanonical_kept_section_iff Q hQ T).mp hCan
  have hTestR := (invFamily (Nat.succ_pos n) k).isInvValue.isGeoTestTower_of_isCanonical hR T hCan
  have hTestV := (invFamily (Nat.succ_pos n) k).isInvValue.isGeoTestTower_of_isCanonical hV T hCanV
  have hCosRV := (hL.wEquiv.2 T).2 hTestR
  have hSupport : V.N⊆zeroPlane U := fun _ hz => ⟨mem_univ _,hz.2⟩
  have hTrans : IsTransverse (n+1) (zeroPlane U) V.E := by
    change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  obtain ⟨C,hCc,hC,N,hLift,hNativeTest⟩ := exists_native_history_of_original_test
    (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U)
    V hV hSupport hTrans T hTestV
  let B := nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) V
  have hB : IsInvDomain k B := isInvDomain_nativePullback
    (X := CMfd.of (n := n+1) (productOpen U)) (W := zeroPlane U) (Nat.succ_pos n) (Nat.le_succ n)
    (zeroPlane_regular U) V hV hSupport hTrans
  have hNative := HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    (n := n+1) (k := n) (q := k) (X := CMfd.of (n := n+1) (productOpen U))
    (hk := Nat.le_succ n) (W := zeroPlane U) (hWc := zeroPlane_closed U)
    (hW := zeroPlane_regular U) (Y := Y) (T := T) (V := C) (hVc := hCc) (hV := hC) (Q := N)
    (Nat.succ_pos n) hn V hV hSupport hTrans hLift hCanV
  have hNativeCan := hNative.1
  let H := transport (nativeZeroSectionEquiv U) N
  let j : H.target → Y := fun z => (H.back z).val
  have hIso := transport_isTowerIso (nativeZeroSectionEquiv U) N
  have hInput : MarkedIdeal.pullback (nativeZeroSectionEquiv U) B=D := native_input_record Q hQ
  have hCanD : IsCanonical D ((invFamily hn k).inv D) H.tower := by
    have h := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
      (invFamily hn k) hB (nativeZeroSectionEquiv U) hIso hNativeCan
    simpa only [hInput] using h
  have hBarDom := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := CMfd.of (n := n) U) Q hQ
  have hD : IsInvDomain k D := HironakaActualInitialNonmonomialCoefficientBoundary.coefficient_isInvDomain _ hBarDom
  have hTestD := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hD H.tower hCanD
  have hBarCan := (invFamily_isCanonical_bar_coefficient_iff hn Q hQ H.tower).mpr hCanD
  have hBarTest := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hBarDom H.tower hBarCan
  have hVhol : ∀x f,V.ideal.mem x f → HolomorphicAt (n+1) f x :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hV.isWellFormed.isCoherent hf
  have hWholeNative := hLift.whole_records (Nat.succ_pos n) hV.isWellFormed.isSNCDivisor hTrans V rfl hSupport hVhol
  have hWholeBase : geoTransformAlong D H.tower=MarkedIdeal.pullback H.back (geoTransformAlong B N) := by
    have h := BlowupTowerIsomorphism.IsTowerIso.geoTransformAlong_eq (nativeZeroSectionEquiv U)
      hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent hIso hNativeTest
    simpa only [hInput] using h
  have hNativeCos := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift (Nat.succ_pos n)
    hV.isWellFormed.isSNCDivisor hTrans V rfl hSupport hVhol
  have hCurrentB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB N hNativeTest
  have hBaseCos : (geoTransformAlong D H.tower).cosupp=H.back ⁻¹' (geoTransformAlong B N).cosupp := by
    rw [hWholeBase,cosupp_pullback_eq hCurrentB.isWellFormed.isCoherent]
  have hCos : (geoTransformAlong D H.tower).cosupp=j ⁻¹' (geoTransformAlong R T).cosupp := by
    rw [hBaseCos,hNativeCos,←hCosRV]
    rfl
  have hRVE : (geoTransformAlong R T).E=(geoTransformAlong V T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := R) (𝔫 := V) hE T
  have hBoundary : (geoTransformAlong D H.tower).E=(geoTransformAlong R T).E.map (j ⁻¹' ·) := by
    have h1 := congrArg (fun M : MarkedIdeal n H.target => M.E) hWholeBase
    have h2 := congrArg (fun M : MarkedIdeal n (nativeManifold (Y := Y) (Nat.le_succ n) C hC) => M.E) hWholeNative
    change (geoTransformAlong D H.tower).E=(geoTransformAlong B N).E.map (H.back ⁻¹' ·) at h1
    change (geoTransformAlong B N).E=(geoTransformAlong V T).E.map ((Subtype.val : C → Y) ⁻¹' ·) at h2
    rw [h2,←hRVE] at h1
    simpa only [j,List.map_map,Function.comp_def,preimage_preimage] using h1
  have hImage : j '' (geoTransformAlong D H.tower).cosupp=(geoTransformAlong R T).cosupp := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (Set.ext_iff.mp hCos z).mp hz
    · intro hy
      have hyV : y∈(geoTransformAlong V T).cosupp := hCosRV ▸ hy
      have hyC := HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift V hSupport
        ((geoTransformAlong V T).cosupp_subset_N hyV)
      let p : nativeManifold (Y := Y) (Nat.le_succ n) C hC := ⟨y,hyC⟩
      let z : H.target := H.back.symm p
      have hj : j z=y := by simp only [j,z,H.back.apply_symm_apply,p]
      refine ⟨z,?_,hj⟩
      rw [hCos]
      change j z∈(geoTransformAlong R T).cosupp
      rwa [hj]
  have hValues : ∀z∈(geoTransformAlong D H.tower).cosupp,
      (invFamily (Nat.succ_pos n) k).inv R T (j z)=
        HironakaActualSectionBoundaryDimension.sameIndexMap 1 k ((invFamily hn k).inv D H.tower z) := by
    intro z hz
    have hzR : j z∈(geoTransformAlong R T).cosupp := (Set.ext_iff.mp hCos z).mp hz
    have hzV : j z∈(geoTransformAlong V T).cosupp := hCosRV ▸ hzR
    have hzNative : H.back z∈(geoTransformAlong B N).cosupp := by
      rw [hNativeCos]
      exact hzV
    have hIsoVal := (invFamily hn k).isInvValue.towerIso (nativeZeroSectionEquiv U) B hB
      H.tower N H.back hIso hNativeCan z hzNative
    rw [hInput] at hIsoVal
    have hVal := hNative.2 (H.back z) hzV
    have hdim : (n+1)-n=1 := by omega
    rw [hdim] at hVal
    exact (invFamily_values_kept_section Q hQ T hCan (j z) hzR).trans
      (hVal.trans (congrArg (HironakaActualSectionBoundaryDimension.sameIndexMap 1 k) hIsoVal.symm))
  have hMax : maxLocus ((invFamily (Nat.succ_pos n) k).inv R T) (geoTransformAlong R T).cosupp=
      j '' maxLocus ((invFamily hn k).inv D H.tower) (geoTransformAlong D H.tower).cosupp := by
    ext y
    constructor
    · rintro ⟨hy,hMax⟩
      obtain ⟨z,hz,rfl⟩ := hImage.symm ▸ hy
      refine ⟨z,⟨hz,fun w hw => ?_⟩,rfl⟩
      apply (HironakaActualSectionBoundaryDimension.strictMono_sameIndexMap 1 k).le_iff_le.mp
      rw [←hValues w hw,←hValues z hz]
      exact hMax (j w) (hImage ▸ mem_image_of_mem j hw)
    · rintro ⟨z,⟨hz,hMax⟩,rfl⟩
      refine ⟨hImage ▸ mem_image_of_mem j hz,fun y hy => ?_⟩
      obtain ⟨w,hw,rfl⟩ := hImage.symm ▸ hy
      rw [hValues w hw,hValues z hz]
      exact (HironakaActualSectionBoundaryDimension.strictMono_sameIndexMap 1 k).monotone (hMax w hw)
  have hBarMax := invFamily_maxLocus_bar_coefficient hn Q hQ H.tower hBarCan
  have hResolved : IsGeoResolution R T ↔ IsGeoResolution D H.tower := by
    constructor
    · intro h
      exact ⟨hTestD,by rw [hCos,h.2,preimage_empty]⟩
    · intro h
      exact ⟨hTestR,by rw [←hImage,h.2,image_empty]⟩
  have hBarCos := ((coefficient_local_any_boundary
    (barMarked (X := CMfd.of (n := n) U) Q) hBarDom).wEquiv.2 H.tower).2 hBarTest
  have hBarResolved : IsGeoResolution D H.tower ↔
      IsGeoResolution (barMarked (X := CMfd.of (n := n) U) Q) H.tower := by
    constructor
    · intro h
      exact ⟨hBarTest,hBarCos.trans h.2⟩
    · intro h
      exact ⟨hTestD,hBarCos.symm.trans h.2⟩
  refine ⟨C,hCc,hC,N,hLift,?_,hCanD,hBarCan,hTestD,hBarTest,?_,hBoundary,hCos,hImage,
    hValues,hMax,?_,hResolved,hResolved.trans hBarResolved⟩
  · exact (length_transport (nativeZeroSectionEquiv U) N).trans hLift.length
  · intro z
    exact (hLift.square (H.back z)).trans
      (congrArg Subtype.val (proj_transport (nativeZeroSectionEquiv U) N z)).symm
  · exact hMax.trans (congrArg (fun A => j '' A) hBarMax.symm)

/-- Honest zero-native-dimensional branch: only chronological EMPTY centres
and the actual resolved endpoint, without an invented value comparison. -/
theorem zero_native_empty_history {k : ℕ} {U : Opens (ComplexModel 0)}
    (Q : MarkedIdeal 0 U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} 1} (T : BlowupTower (CMfd.of (n := 1) (productOpen U)) Y)
    (hCan : IsCanonical (keptNormalLower Q) ((invFamily (Nat.succ_pos 0) k).inv (keptNormalLower Q)) T) :
    ResolutionInvariantExt.IsEmptyTower T ∧ IsGeoResolution (keptNormalLower Q) T := by
  have hR := (kept_normal_lower_data Q hQ).1
  have hSup : (keptNormalLower Q).N⊆zeroPlane U := fun _ hz => ⟨mem_univ _,hz.2⟩
  have hZero : IsInvDomain 0 (keptNormalLower Q) := isInvDomain_native_support_bound
    (X := CMfd.of (n := 1) (productOpen U)) (W := zeroPlane U)
    (Nat.le_succ 0) (zeroPlane_regular U)
    (keptNormalLower Q) hR hSup
  have hEmpty := (isCanonical_iff_isEmptyTower_of_dimZero hZero
    ((invFamily (Nat.succ_pos 0) k).inv (keptNormalLower Q)) T).mp hCan
  have hTest := (invFamily (Nat.succ_pos 0) k).isInvValue.isGeoTestTower_of_isCanonical hR T hCan
  exact ⟨hEmpty,hTest,cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hZero T hTest⟩

end
end Hironaka.HironakaG1ProperNormalNativeHistory
