import Hironaka.Resolution.HironakaG1SupportedStepOne
import Hironaka.Resolution.HironakaG1ProperNormalOriginalTest

/-! # A supported Step One history on the literal original source -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LiteralSupportedStepOne

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowerIsomorphism MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec CanonicalCentres
  NormalCrossings HomogenizedIdealAlong HomogenizedGlueingTower
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionInitialBar HironakaActualSectionBoundaryGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionContactChoices
  HironakaActualNativeInvariantDomain HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperNormalOriginalTest
  HironakaG1SupportedStepOne HironakaOriginalFamilyDepthStability
  HironakaActualSectionBoundaryDimension HironakaSmoothSubmersionCanonicalValueDimensionShift

private theorem zeroPlane_closed {n : ℕ} (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold (isClosedSubmanifold_univ (n := n) (M := U))).1

set_option maxHeartbeats 1600000 in
/-- An ordinary padded upper test produces the literal original native
tower. When the supported whole record is Step One canonical, this tower
is canonical for `Q` and gives the exact supported Step One values. -/
theorem exists_literal_supported_step_one_history {n q : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (a : ℕ) (Q : MarkedIdeal n U) (hQ : IsInvDomain (q + 1) Q)
    (hQMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hTest : IsGeoTestTower (properNormalMarked Q) T) :
    let M := supportedNormalMarked Q
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n)
      (N : BlowupTower (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Y := Y) (Nat.le_succ n) V hV)),
      Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U) M.E T V hVc hV N ∧
      let H := transport (nativeZeroSectionEquiv U) N
      IsGeoTestTower Q H.tower ∧ H.tower.length = T.length ∧
      (IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (a + q)) M) T →
        IsCanonical Q (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) Q) H.tower ∧
        ∀ z : H.target, (H.back z).val ∈ (geoTransformAlong M T).cosupp →
          Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (a + q)) M T (H.back z).val =
            stepDimensionMap (depthPadMap a q ∘ sameIndexMap 1 q)
              (Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) Q H.tower z)) := by
  let M := supportedNormalMarked Q
  let F := nativeZeroSectionEquiv U
  let B := nativePullback (Y := CMfd.of (n := n + 1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  obtain ⟨V, hVc, hV, N, hLift, _, _, hLen, hQTest, _, _, _, _, _⟩ :=
    exists_literal_original_native_test_history Q hQ T hTest
  let H := transport F N
  have hM : IsInvDomain (q + 1) M := (supported_normal_data Q hQ).2.1
  have hMMax : IsMaximalOrderAlong M.N M.ideal M.d := supported_normal_maximal_order Q hQ hQMax
  have hSupport : M.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hTrans : IsTransverse (n + 1) (zeroPlane U) M.E := by
    change IsTransverse (n + 1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier univ Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hB : IsInvDomain (q + 1) B :=
    isInvDomain_nativePullback (X := CMfd.of (n := n + 1) (productOpen U)) (W := zeroPlane U)
      (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U) M hM hSupport hTrans
  have hBMax : IsMaximalOrderAlong B.N B.ideal B.d :=
    (native_source_geometry (X := CMfd.of (n := n + 1) (productOpen U)) (W := zeroPlane U)
      (Nat.le_succ n) (zeroPlane_regular U) M hSupport
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hMMax).2.2.1
  have hInput : MarkedIdeal.pullback F B = Q := native_supported_input_record Q hQ
  have hIso := transport_isTowerIso F N
  have hStep := StepOneSeq.isMaxOrderValue_stepOneInvM (k := q + 1) (invFamily hn q) hn
  refine ⟨V, hVc, hV, N, hLift, hQTest, hLen, fun hCan => ?_⟩
  obtain ⟨hIff, hValue⟩ := Lift.original_step_one_with_depth
    (X := CMfd.of (n := n + 1) (productOpen U)) (hk := Nat.le_succ n)
    (W := zeroPlane U) (hW := zeroPlane_regular U) (T := T) (V := V) (hV := hV) (Q := N)
    (Nat.succ_pos n) hn a M hM hSupport hTrans hMMax hLift
  have hCanB := hIff.mpr hCan
  have hCanQ := hStep.isCanonical_of_isTowerIso hB hBMax F hIso hCanB
  rw [hInput] at hCanQ
  refine ⟨hCanQ, fun z hz => ?_⟩
  have hCos := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift
    (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg)
  have hzB : H.back z ∈ (geoTransformAlong B N).cosupp := by rw [hCos]; exact hz
  have hIsoValue := hStep.towerIso F B hB hBMax H.tower N H.back hIso hCanB z hzB
  rw [hInput] at hIsoValue
  have hCodim : n + 1 - n = 1 := by omega
  rw [hCodim] at hValue
  exact (hValue hCan (H.back z) hz).trans
    (congrArg (stepDimensionMap (depthPadMap a q ∘ sameIndexMap 1 q)) hIsoValue.symm)

end
end Hironaka.HironakaG1LiteralSupportedStepOne
