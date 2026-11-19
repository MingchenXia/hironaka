import Hironaka.Resolution.HironakaG1PositiveNormalOwnTail
import Hironaka.Resolution.HironakaG1PositiveNormalRestartCarrier

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalAlignedTail
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
/-- The literal native lower record comparison at the specified positive run cut. -/
abbrev NativeTailRecordsAt {n : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (y : Y) (s r : ℕ) : Prop :=
    let X := CMfd.of (n := n + 1) (productOpen U)
    let Sec := sectionMarked Q
    let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) Sec
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
            markedPullback (m := n) g (geoTransformAlong L (restrict O S))

/-- The record comparison at the padded history's positive run cut. -/
abbrev PaddedCutNativeTailRecords {n : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (y : Y) (s : ℕ) : Prop :=
  NativeTailRecordsAt Q T y s (regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y)

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- When the positive runs agree, the corresponding cut of the actual native
history uses its own lower mask. Its source and transformed lower records are
the pullbacks along the actual source and endpoint inclusions. -/
theorem positive_normal_aligned_native_tail_records {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hSecNS : ¬ IsSpecial (sectionMarked Q) T y)
    (hAligned : ∀ i, 1 ≤ i → i ≤ regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y →
      ¬ IsSpecial (sectionMarked Q) (head T i) ((tail T i).proj y)) :
    PaddedCutNativeTailRecords Q T y s := by
  have hClock := (positive_normal_section_run Q hQ (s := s) T hT y).2.mpr hAligned
  exact (congrArg (NativeTailRecordsAt Q T y s) hClock).mp
    (HironakaG1PositiveNormalOwnTail.positive_normal_own_native_tail_records Q hQ T hT y hy hLevel hSecNS)

/-- At a positive nonspecial section endpoint, the actual native cut is the
padded run cut. The native mask, restricted tower and records are those of
the native history at that cut. -/
theorem positive_normal_native_tail_records_of_nonspecial {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hSecNS : ¬ IsSpecial (sectionMarked Q) T y) :
    PaddedCutNativeTailRecords Q T y s := by
  have hClock := HironakaG1PositiveNormalRestartCarrier.positive_normal_section_run_eq_of_nonspecial
    Q hQ T hT y hy hLevel hSecNS
  exact (congrArg (NativeTailRecordsAt Q T y s) hClock).mp
    (HironakaG1PositiveNormalOwnTail.positive_normal_own_native_tail_records Q hQ T hT y hy hLevel hSecNS)

/-- The section endpoint condition supplies the section-head condition of
the shared native test theorem at the actual padded cut. -/
theorem positive_normal_section_head_nonspecial_of_endpoint {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) (y : Y)
    (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hSecNS : ¬ IsSpecial (sectionMarked Q) T y) :
    let r := regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y
    ¬ IsSpecial (sectionMarked Q) (head T r) ((tail T r).proj y) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let Sec := sectionMarked Q
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hClass := (properNormalMarked_locWPEquiv_section Q hQ).trans
    (bar_local_any_boundary (X := X) Sec hSec)
  have hBarTest := (hClass.wEquiv.2 T).1.mp hT
  have hyBar : y ∈ (geoTransformAlong (barMarked Sec) T).cosupp :=
    (hClass.wEquiv.2 T).2 hT ▸ hy
  have hLevelSec := (HironakaG8MemberLoci.level_eq_of_E_eq
    (show (properNormalMarked Q).E = Sec.E from rfl) T y).symm.trans hLevel
  have hClock := HironakaG1PositiveNormalRestartCarrier.positive_normal_section_run_eq_of_nonspecial
    Q hQ T hT y hy hLevel hSecNS
  have hReg := stepRegime_and_mem_cosupp_head Sec hSec.isWellFormed T hBarTest hyBar hSecNS
  rw [hLevelSec, hClock] at hReg
  exact hReg.1.2

end
end Hironaka.HironakaG1PositiveNormalAlignedTail
