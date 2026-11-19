import Hironaka.Resolution.HironakaG1PositiveNormalChronology
import Hironaka.Resolution.HironakaActualNativeSectionPositiveLowerRecords
import Hironaka.Resolution.HironakaDisjointNativeOpenLift

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalOwnTail
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowerIsomorphism HironakaDisjointNativeReferenceWindow
  MarkedIdealBiholomorphism NormalCrossings HironakaSmoothSubmersionCoefficientIdeals
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionInitialBar
  HironakaActualOpenZeroSectionDifferentials HironakaDisjointNativeOpenLift
  HironakaActualNativeSectionOriginalCuts HironakaActualNativeSectionStepOneHistory
  HironakaActualNativeSectionPositiveMask HironakaActualNativeSectionPositiveLowerRecords
  HironakaG1PositiveNormalPhase HironakaG1PositiveNormalChronology HironakaG8HomStable
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain
open HomogenizedGlueingTower (strictAlong)

private theorem zeroPlane_closed {n : ℕ} (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n) (M := U))).1

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual section and native histories cut at the section run.
Their lower records use the literal section and native masks, with
source and endpoint projections along the same lifted history. -/
theorem positive_normal_own_native_tail_records {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hSecNS : ¬ IsSpecial (sectionMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let Sec := sectionMarked Q
    let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) Sec
    let r := regimeRun (stepRegime Sec (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n + 1) V z n)
      (N : BlowupTower (nativeManifold (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Nat.le_succ n) V hV))
      (z : nativeManifold (Nat.le_succ n) V hV),
      Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U) Sec.E T V hVc hV N ∧
      z.val = y ∧ regimeRun (stepRegime B (s + 1)) N z = r ∧ ¬ IsSpecial B N z ∧
      ∃ (A : Set (split T r).1) (hAc : IsClosed A)
        (hA : ∀ x ∈ A, RegularAtDim (n := n + 1) A x n)
        (e : (split N r).1 = nativeManifold (Nat.le_succ n) A hA),
        let NH := recastTarget e (head N r)
        let NS := recastSource e (tail N r)
        let a := NS.proj z
        let O := maskA Sec H a.val
        let L := lowerMarkedM Sec (s + 1) H a.val
        let ON := maskA B NH a
        let LN := lowerMarkedM B (s + 1) NH a
        Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U) Sec.E H A hAc hA NH ∧
        ∃ hTail : Lift (Nat.le_succ n) A hAc hA (boundary Sec.E H) S V hVc hV NS,
        a.val = p ∧ nativeWindow (Nat.le_succ n) A hA O = ON ∧
        (∃ (hZc : IsClosed (openSection V (openPreimage S O)))
          (hZ : ∀ x ∈ openSection V (openPreimage S O),
            RegularAtDim (n := n + 1) (openSection V (openPreimage S O)) x n)
          (K : BlowupTower
            (nativeManifold (Nat.le_succ n) (openSection A O) (openSection_regular hA O))
            (nativeManifold (Nat.le_succ n) (openSection V (openPreimage S O)) hZ)),
          Lift (Nat.le_succ n) (openSection A O) (hAc.preimage continuous_subtype_val)
            (openSection_regular hA O)
            ((boundary Sec.E H).map ((Subtype.val : O → (split T r).1) ⁻¹' ·))
            (restrict O S) (openSection V (openPreimage S O)) hZc hZ K ∧
          IsTowerIso (windowEquiv (Nat.le_succ n) A hA hAc O) K
            (restrict (nativeWindow (Nat.le_succ n) A hA O) NS) (endpointEquiv hTail O)) ∧
        ∃ (f : ON → O) (g : openPreimage NS ON → openPreimage S O)
          (w : openPreimage NS ON),
          w.val = z ∧ (g w).val = y ∧
          (∀ q, (f q).val = q.val.val) ∧ (∀ q, (g q).val = q.val.val) ∧
          markedPullback (m := n) f L = LN ∧
          geoTransformAlong LN (restrict ON NS) =
            markedPullback (m := n) g (geoTransformAlong L (restrict O S)) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) Sec
  let r := regimeRun (stepRegime Sec (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  have hP := properNormalMarked_isInvDomain Q hQ
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hBar := bar_local_any_boundary (X := X) P hP
  have hyBar : y ∈ (geoTransformAlong (barMarked P) T).cosupp :=
    (hBar.wEquiv.2 T).2 hT ▸ hy
  obtain ⟨V, hVc, hV, N, hLift, _, _, _, _, _, _⟩ := exists_upper_native_test_history Q hQ T hT
  have hyV : y ∈ V := by
    rw [hLift.carrier]
    exact bar_cosupport_subset_strict_zeroPlane Q hQ T hT hyBar
  let z : nativeManifold (Nat.le_succ n) V hV := ⟨y, hyV⟩
  have hChron := actual_section_step_one_chronology U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d
    (T := T) (V := V) (Q := N) hLift
  have hClock : regimeRun (stepRegime B (s + 1)) N z = r :=
    (hChron.2.2.2.2 (s + 1) z).symm
  have hNativeNS : ¬ IsSpecial B N z := fun h => hSecNS ((hChron.2.2.1 z).2.mpr h)
  refine ⟨V, hVc, hV, N, z, hLift, rfl, hClock, hNativeNS, ?_⟩
  obtain ⟨A, hAc, hA, e, hHead, hTail, hOpen⟩ := exists_original_reference_lift hLift r
  let NH := recastTarget e (head N r)
  let NS := recastSource e (tail N r)
  let a := NS.proj z
  have ha : a.val = p := (hTail.square z).symm
  let Oa := maskA Sec H a.val
  let ON := maskA B NH a
  let LN := lowerMarkedM B (s + 1) NH a
  have hMask : (Subtype.val : A → (split T r).1) ⁻¹' (Oa : Set (split T r).1) = (ON : Set (nativeManifold (Nat.le_succ n) A hA)) :=
    actual_section_maskA U Q.N hQ.isWellFormed.isClosedSubmanifold_N Q.E
      hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d hHead a
  have hWindow : nativeWindow (Nat.le_succ n) A hA Oa = ON := Opens.ext hMask
  refine ⟨A, hAc, hA, e, hHead, hTail, ha, hWindow, hOpen Oa, ?_⟩
  have hSecEq := properNormalMarked_locWPEquiv_section Q hQ
  have hBarSec := bar_local_any_boundary (X := X) Sec hSec
  have hTestSec := ((hSecEq.trans hBarSec).wEquiv.2 T).1.mp hT
  have hySec : y ∈ (geoTransformAlong (barMarked Sec) T).cosupp :=
    ((hSecEq.trans hBarSec).wEquiv.2 T).2 hT ▸ hy
  have hLevelSec := (HironakaG8MemberLoci.level_eq_of_E_eq (show P.E = Sec.E from rfl) T y).symm.trans hLevel
  have hReg := stepRegime_and_mem_cosupp_head Sec hSec.isWellFormed T hTestSec hySec hSecNS
  rw [hLevelSec] at hReg
  have hTestHead := ((isGeoTestTower_iff_head_tail (barMarked Sec) T r).mp hTestSec).1
  have hpO : p ∈ maskA Sec H p :=
    mem_maskA (X := X) Sec hSec.isWellFormed hSec.one_le_d (Nat.succ_pos n) H hTestHead
      (hReg.1.1 ▸ Nat.succ_pos s) hReg.1.2
  have haON : a ∈ ON := by
    change a ∈ (ON : Set (nativeManifold (Nat.le_succ n) A hA))
    rw [← hMask]
    change a.val ∈ maskA Sec H a.val
    rw [ha]
    exact hpO
  let w : openPreimage NS ON := ⟨z, haON⟩
  have hInit := actual_section_lowerMarkedM_succ U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d hHead s a
  have hCurrent := actual_section_lowerMarkedM_succ_tail U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d hHead hTail s a
  let f := positiveMaskSection (U := U) (A := Q.N) (hA := hQ.isWellFormed.isClosedSubmanifold_N)
    (E := Q.E) (hE := hQ.isWellFormed.isSNCDivisor) (J := Sec.ideal)
    (hJ := hSec.isWellFormed.isCoherent) (d := Q.d) (h := hHead) a
  let g := positiveEndpointSection (U := U) (A := Q.N) (hA := hQ.isWellFormed.isClosedSubmanifold_N)
    (E := Q.E) (hE := hQ.isWellFormed.isSNCDivisor) (J := Sec.ideal)
    (hJ := hSec.isWellFormed.isCoherent) (d := Q.d) (h := hHead) (hTail := hTail) a
  exact ⟨f, g, w, rfl, rfl, fun _ => rfl, fun _ => rfl, hInit, hCurrent⟩

end
end Hironaka.HironakaG1PositiveNormalOwnTail
