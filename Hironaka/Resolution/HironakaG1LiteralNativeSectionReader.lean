import Hironaka.Resolution.HironakaG1SectionReaderCanonical
import Hironaka.Resolution.HironakaG1LiteralSupportedStepOne
import Hironaka.Resolution.HironakaG8LocalTransport

/-! The section reader with the literal original source record and tower. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1LiteralNativeSectionReader

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  RelativePrincipalizationSpan GermIdealPullbackCalculus
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HomogenizedIdealAlong HomogenizedGlueingTower
  NormalCrossings SubmanifoldChartedSpace
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaActualNativeSectionInitialBar HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeInvariantDomain HironakaActualNativeSectionContactChoices
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperNormalOriginalTest HironakaG1SectionReaderCanonical
  HironakaActualSectionBoundaryDimension HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionCoefficientIdeals HironakaG8LocalTransport

variable {n q : ℕ} {U : Opens (ComplexModel n)}

private abbrev ambient (U : Opens (ComplexModel n)) :=
  CMfd.of (n := n + 1) (productOpen U)

private theorem plane_closed (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold (isClosedSubmanifold_univ (n := n) (M := U))).1

/-- The literal source chart of the section record recovers the original
marked ideal, including every boundary member in order. -/
theorem section_native_input_record (Q : MarkedIdeal n U) (hQ : IsInvDomain q Q) :
    MarkedIdeal.pullback (nativeZeroSectionEquiv U)
      (nativePullback (Y := ambient U) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
        (sectionMarked Q)) = Q := by
  let := chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  have := isComplexManifold_chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  let M := sectionMarked Q
  have hM : IsInvDomain q M := section_projected_domain q Q.N Q.E Q.ideal Q.d hQ
  have hProj : projection U ∘ zeroSection U = id := by
    funext z
    apply Subtype.ext
    exact tangentProjection_tangentInclusion n 1 z
  have hTrace : markedPullback (m := n) (zeroSection U) M = Q := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext x
      have h : projection U (zeroSection U x) = x := congrFun hProj x
      change (projection U (zeroSection U x) ∈ Q.N ∧
        actualJointNormalProjection n 1 (zeroSection U x).val = 0) ↔ x ∈ Q.N
      rw [h]
      simp [zeroSection]
    · change (Q.E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·) = _
      rw [List.map_map]
      change Q.E.map ((projection U ∘ zeroSection U) ⁻¹' ·) = _
      rw [hProj]
      simp
    · change GermIdeal.pullback (m := n) (zeroSection U)
        (GermIdeal.pullback (m := n + 1) (projection U) Q.ideal) = _
      rw [← coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U)
        Q.ideal hQ.isWellFormed.isCoherent, hProj]
      exact BlowupControlledTransform.pullback_id hQ.isWellFormed.isCoherent
    · rfl
  exact (whole_markedPullback_comp (contMDiff_val (Nat.le_succ n) (zeroPlane_regular U))
    (nativeZeroSectionEquiv U).contMDiff M hM.isWellFormed.isCoherent).symm.trans hTrace

set_option maxHeartbeats 1200000 in
/-- Any actual padded test tower has a literal original native test tower.
The original section reader on the cylindrical history preserves and
reflects original Step One canonicality of that native tower. Its
canonical values and maxima compare on the actual endpoint maps. -/
theorem exists_literal_native_section_reader (hn : 0 < n) (Q : MarkedIdeal n U)
    (hQ : IsInvDomain (q + 1) Q) (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (ambient U) Y)
    (hTest : IsGeoTestTower (properNormalMarked Q) T) :
    let X := ambient U
    let M := sectionMarked Q
    let P := properNormalMarked Q
    let f : ∀ {Z : CMfd.{0} (n + 1)}, BlowupTower X Z → Z → ℕ ×ₗ WithTop (ValTy q) :=
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) M
    let g : ∀ {Z : CMfd.{0} n}, BlowupTower (CMfd.of (n := n) U) Z → Z → ℕ ×ₗ WithTop (ValTy q) :=
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) Q
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n)
      (N : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Nat.le_succ n) V hV)),
      let H := transport (X' := CMfd.of (n := n) U) (nativeZeroSectionEquiv U) N
      let i := fun z : H.target => (H.back z).val
      let D := (geoTransformAlong P T).cosupp
      let E := (geoTransformAlong Q H.tower).cosupp
      Lift (Nat.le_succ n) (zeroPlane U) (plane_closed U) (zeroPlane_regular U) M.E T V hVc hV N ∧
        H.tower.length = T.length ∧ IsGeoTestTower Q H.tower ∧ E = i ⁻¹' D ∧ i '' E = D ∧
        (IsCanonical P f T ↔ IsCanonical Q g H.tower) ∧
        (IsCanonical P f T →
          (∀ z : H.target, i z ∈ D →
            f T (i z) = stepDimensionMap (sameIndexMap 1 q) (g H.tower z)) ∧
          maxLocus (g H.tower) E = i ⁻¹' maxLocus (f T) D ∧
          i '' maxLocus (g H.tower) E = maxLocus (f T) D) := by
  intro X M P f g
  obtain ⟨V, hVc, hV, N, hLift, _, _, hLen, hQTest, _, _, hPre, hImage, _⟩ :=
    exists_literal_original_native_test_history Q hQ T hTest
  let F := nativeZeroSectionEquiv U
  let H := transport (X' := CMfd.of (n := n) U) F N
  let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  let gB : ∀ {Z : CMfd.{0} n}, BlowupTower
        (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)) Z →
        Z → ℕ ×ₗ WithTop (ValTy q) := Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) B
  have hM : IsInvDomain (q + 1) M := section_projected_domain (q + 1) Q.N Q.E Q.ideal Q.d hQ
  have hSupport : M.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hTrans : IsTransverse (n + 1) (zeroPlane U) M.E :=
    isTransverse_liftedCarrier univ Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hB : IsInvDomain (q + 1) B :=
    isInvDomain_nativePullback (X := X) (W := zeroPlane U)
      (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U)
      M hM hSupport hTrans
  have hMmax := sectionMarked_maximalOrder Q hQ hMax
  have hBMax : IsMaximalOrderAlong B.N B.ideal B.d :=
    (native_source_geometry (X := X) (W := zeroPlane U) (Nat.le_succ n) (zeroPlane_regular U)
      M hSupport hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hMmax).2.2.1
  have hInput : MarkedIdeal.pullback F B = Q := section_native_input_record Q hQ
  have hBack : MarkedIdeal.pullback F.symm Q = B := by
    rw [← hInput]
    exact pullback_symm_pullback F hB.isWellFormed.isCoherent
  have hIso := transport_isTowerIso (X' := CMfd.of (n := n) U) F N
  have hStep := StepOneSeq.isMaxOrderValue_stepOneInvM (k := q + 1) (invFamily hn q) hn
  have hCanB_Q : IsCanonical B gB N ↔ IsCanonical Q g H.tower := by
    constructor
    · intro h
      have h' := hStep.isCanonical_of_isTowerIso hB hBMax F hIso h
      rwa [hInput] at h'
    · intro h
      have h' := hStep.isCanonical_of_isTowerIso hQ hMax F.symm hIso.symm h
      rwa [hBack] at h'
  obtain ⟨hCanP_B, hCompare⟩ := Lift.original_native_section_reader hn Q hQ hMax hLift
  refine ⟨V, hVc, hV, N, hLift, hLen, hQTest, hPre, hImage, hCanP_B.trans hCanB_Q, fun hCan => ?_⟩
  have hBcan := hCanP_B.mp hCan
  have hBtest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn q) B hB hBMax hn N hBcan).2.1
  have hBCos := IsTowerIso.cosupp_geoTransformAlong (X' := CMfd.of (n := n) U) F
    hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent hIso hBtest
  rw [hInput] at hBCos
  have hLocal (z : H.target) (hz : H.back z ∈ (geoTransformAlong B N).cosupp) :
      g H.tower z = gB N (H.back z) := by
    have h := hStep.towerIso F B hB hBMax H.tower N H.back hIso hBcan z hz
    rwa [hInput] at h
  obtain ⟨hValue, hMaxPre, hMaxImage⟩ := hCompare hCan
  let i₀ : nativeManifold (Nat.le_succ n) V hV → Y := Subtype.val
  let D := (geoTransformAlong P T).cosupp
  let E := (geoTransformAlong Q H.tower).cosupp
  have hs : Function.Surjective (H.back : H.target → nativeManifold (Nat.le_succ n) V hV) :=
    H.back.surjective
  change E = H.back ⁻¹' (geoTransformAlong B N).cosupp at hBCos
  have hMaxH := ResolutionInvariantSegments.maxLocus_preimage_of_surjective hs hLocal
  rw [← hBCos] at hMaxH
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hq : z ∈ E := (show E = (i₀ ∘ H.back) ⁻¹' D from hPre).symm ▸ hz
    have hBz : H.back z ∈ (geoTransformAlong B N).cosupp := by
      change z ∈ H.back ⁻¹' (geoTransformAlong B N).cosupp
      rwa [← hBCos]
    exact (hValue (H.back z) hz).trans
      (congrArg (stepDimensionMap (sameIndexMap 1 q)) (hLocal z hBz).symm)
  · change maxLocus (g H.tower) E = (i₀ ∘ H.back) ⁻¹' maxLocus (f T) D
    rw [hMaxH, hMaxPre]
    rfl
  · calc
      _ = i₀ '' (H.back '' maxLocus (g H.tower) E) :=
        (image_image i₀ (H.back : H.target → nativeManifold (Nat.le_succ n) V hV) _).symm
      _ = _ := by
        rw [hMaxH, hs.image_preimage]
        exact hMaxImage

end

end Hironaka.HironakaG1LiteralNativeSectionReader
