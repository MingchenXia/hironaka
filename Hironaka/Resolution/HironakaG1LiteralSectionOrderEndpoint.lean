import Hironaka.Resolution.HironakaG1OrdinaryNativeEvaluatorEndpoint
import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative
import Hironaka.Resolution.HironakaG1CartierTwoAnchors

/-! # Actual native order dispatcher -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LiteralSectionOrderEndpoint
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked StepOneRegime
  HomogenizedIdealAlong HomogenizedGlueingTower BoundaryCount MemberInterTowerAlong NormalCrossings SubmanifoldChartedSpace RelativePrincipalizationSpan
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionOriginalCuts HironakaActualNativeCompanionHistories
  HironakaActualNativeInvariantDomain HironakaOriginalFamilyDepthStability
  HironakaActualSectionBoundaryDimension HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveSuccessorRead
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime GeneralValue CompanionRebase

open HironakaG1ActualNativeCompanionPhase

open HironakaG1OrdinaryNativeEvaluatorEndpoint HironakaG1NativeOrderDispatcher
  MonomialCaseAlong HironakaG1ProperNormalPhaseNative HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionInitialBar HomogenizedGlueingTower

variable {n q : ℕ} {U : Opens (ComplexModel n)}
  {Y : CMfd.{0} (n+1)}
  {T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y}

local notation "X" => CMfd.of (n := n+1) (productOpen U)
private theorem plane_closed (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n) (M := U))).1

/-- The literal section-supported original record has the prescribed
initial ordered boundary transverse to the actual zero plane. -/
theorem literal_section_source_geometry (Q : MarkedIdeal n U) (hQ : IsInvDomain (q+1) Q) :
    (sectionMarked Q).N ⊆ zeroPlane U ∧
    IsTransverse (n+1) (zeroPlane U) (sectionMarked Q).E := by
  constructor
  · exact fun _ hx => ⟨mem_univ _,hx.2⟩
  · change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)

set_option maxHeartbeats 1800000 in
/-- Any padded upper canonical history supplies the genuine literal-section
test and a native lift on the very same blowups. The whole current literal
record, strict carrier, and ordered transversality are exact. -/
theorem exists_literal_section_lift_of_padded_canonical
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (q+1) Q)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q+1)) (properNormalMarked Q)) T) :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ y ∈ V, RegularAtDim (n := n+1) V y n)
      (N : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Nat.le_succ n) V hV)),
      let S := sectionMarked Q
      let K := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) S
      IsGeoTestTower S T ∧
      Lift (Nat.le_succ n) (zeroPlane U) (plane_closed U) (zeroPlane_regular U) S.E T V hVc hV N ∧
      IsGeoTestTower K N ∧
      V = strictAlong T (zeroPlane U) ∧
      IsTransverse (n+1) V (geoTransformAlong S T).E ∧
      geoTransformAlong K N = nativePullback (Nat.le_succ n) V hV (geoTransformAlong S T) := by
  let P := properNormalMarked Q
  let S := sectionMarked Q
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := q+2)
    (invFamily (Nat.succ_pos n) (q+1)) (properNormalMarked Q) hP hMax (Nat.succ_pos n) T hCan).2.1
  have hSecTest : IsGeoTestTower S T :=
    ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 T).1.mp hTest
  have hDom : IsInvDomain (q+1) S := section_projected_domain (q+1) Q.N Q.E Q.ideal Q.d hQ
  obtain ⟨hSub,hTr⟩ := literal_section_source_geometry Q hQ
  obtain ⟨V,hVc,hV,N,hLift,hNT⟩ := HironakaActualNativeHistoryExistence.exists_native_history_of_original_test
    (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane U) (plane_closed U) (zeroPlane_regular U) S hDom hSub hTr T hSecTest
  have hBoundary : (geoTransformAlong S T).E = boundary S.E T :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := S) (𝔫 := (⟨univ,S.E,IdealWeightPowers.unitIdeal (n+1) (productOpen U),1⟩ :
        MarkedIdeal (n+1) X)) rfl T
  have hCurrentTr := hBoundary ▸ (hLift.geometry (Nat.succ_pos n) hDom.isWellFormed.isSNCDivisor hTr).2
  have hWhole := hLift.whole_records (Nat.succ_pos n) hDom.isWellFormed.isSNCDivisor hTr
    S rfl hSub (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hDom.isWellFormed.isCoherent hg)
  exact ⟨V,hVc,hV,N,hSecTest,hLift,hNT,hLift.carrier,hCurrentTr,hWhole⟩

set_option maxHeartbeats 2300000 in
/-- The literal normal closed reembedding on its own original-family
canonical history has the genuine full native evaluator at every endpoint.
The recursive comparison uses the codimension-one index map. -/
theorem exists_literal_section_original_evaluator
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (q+1) Q)
    (hCan : IsCanonical (sectionMarked Q)
        ((invFamily (Nat.succ_pos n) (q+1)).inv (sectionMarked Q)) T) :
    let M := sectionMarked Q
    ∃ (V' : Set Y) (hV'c : IsClosed V') (hV' : ∀ y ∈ V', RegularAtDim (n := n+1) V' y n)
      (N' : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)) (nativeManifold (Nat.le_succ n) V' hV')),
      Lift (Nat.le_succ n) (zeroPlane U) (plane_closed U) (zeroPlane_regular U) M.E T V' hV'c hV' N' ∧
      IsInvDomain (q+1) (nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M) ∧
      IsCanonical (nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M)
        ((invFamily hn (q+1)).inv (nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M)) N' ∧
      (IsGeoResolution M T → IsGeoResolution (nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M) N') ∧
      (∀ (z : nativeManifold (Nat.le_succ n) V' hV') (o : ℕ), 0 < o →
        ActualOrderHeadCoefficients (plane_closed U) M T N' z o) ∧
      ∀ (z : nativeManifold (Nat.le_succ n) V' hV'), z.val ∈ (geoTransformAlong M T).cosupp →
        let K := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
        let A := geoTransformAlong M T
        let B := geoTransformAlong K N'
        let o := nmOrd A z.val
        let v := (invFamily (Nat.succ_pos n) (q+1)).inv M T z.val
        let w := (invFamily hn (q+1)).inv K N' z
        IsInvDomain (q+1) K ∧ B = nativePullback (Nat.le_succ n) V' hV' A ∧
        IsCanonical K ((invFamily hn (q+1)).inv K) N' ∧
        z ∈ B.cosupp ∧ o = nmOrd B z ∧ v = sameIndexMap 1 (q+1) w ∧
        if o = 0 then
          v = monomialRead (q := q) A z.val ∧ w = monomialRead (q := q) B z ∧
          gammaAlong (n+1) A.N A.ideal A.E A.d z.val =
            dimensionValue 1 (gammaAlong n B.N B.ideal B.E B.d z)
        else
          regimeRun (OrdRegime M o) T z.val = regimeRun (OrdRegime K o) N' z ∧
          ∃ a b : ℕ ×ₗ WithTop (ValTy q),
            v = positiveSuccessorRead o a ∧ w = positiveSuccessorRead o b ∧
            PositiveOrderCompanionWitness (k := q) (Nat.succ_pos n) M T z.val o (fun x => x = positiveSuccessorRead o a) ∧
            PositiveOrderCompanionWitness (k := q) hn K N' z o (fun x => x = positiveSuccessorRead o b) ∧
            a = stepDimensionMap (sameIndexMap 1 q) b ∧
            (ofLex a).1 = (ofLex b).1 ∧ ((ofLex a).2 = ⊤ ↔ (ofLex b).2 = ⊤) := by
  have hDom := section_projected_domain (q+1) Q.N Q.E Q.ideal Q.d hQ
  obtain ⟨hSub,hTr⟩ := literal_section_source_geometry Q hQ
  have h := exists_ordinary_native_order_evaluator (T := T)
    (hk := Nat.le_succ n) (W := zeroPlane U) (hWc := plane_closed U) (hW := zeroPlane_regular U)
    (Nat.succ_pos n) hn hDom hSub hTr hCan
  have hDim : n+1-n = 1 := by omega
  rw [hDim] at h
  exact h

section Cartier
open HironakaG1CartierTwoAnchors
local notation "Z₀" => HironakaG1LaterPositiveNormalExample.Y
local notation "B₀" => HironakaG1LaterPositiveNormalExample.B
local notation "pInv" => Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) P
local notation "sInv" => Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) S

/-- The concrete common Cartier prefix admits no shared nonempty canonical
next centre, for any genuine blowup map. Both canonical clocks accept
the first prefix, while the next occupied step must distinguish them. -/
theorem cartier_no_shared_nonempty_canonical_step
    {Z : CMfd.{0} 3} (D : Set Z₀) (hD : D.Nonempty) (π : Z → Z₀)
    (hπ : IsBlowupAlong 3 D π) :
    ¬ (IsCanonical P pInv (.step B₀ D π hπ) ∧
        IsCanonical S sInv (.step B₀ D π hπ)) := by
  intro h
  have hP := h.1.2.resolve_left hD.ne_empty
  have hS := h.2.2.resolve_left hD.ne_empty
  exact cartier_common_prefix_maximum_discrepancy (hP.symm.trans hS)

end Cartier
end
end Hironaka.HironakaG1LiteralSectionOrderEndpoint
