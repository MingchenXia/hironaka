import Hironaka.Resolution.HironakaG1PositiveNormalRepairDepth

/-! Exact lower bounds for the unrepaired positive nonspecial section cut. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalSectionDomain

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres NormalCrossings RelativePrincipalizationSpan
  StepOneValue StepOneValueMasked StepOneLowerDomain InvDomainMemberRestriction InvDomainRebase
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaG1PositiveNormalPhase HironakaG1SeparateCarrierMemberCut HironakaG1RecursiveMemberValueTransport
  HironakaActualNativeSectionFiniteHistory HironakaActualSectionBoundaryGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaDisjointNativeOpenLift
  HironakaActualNativeSectionInitialBar HironakaG8HomStable
  NormalCrossingsComparison NormalCrossingsInvariance
  HironakaG1PositiveNormalRepairDepth HironakaOriginalFamilyDepthStability
  HironakaActualSectionBoundaryDimension
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open HomogenizedIdealAlong

set_option maxHeartbeats 1000000 in
/-- At the actual common nonspecial head, the literal ambient section cut
and its native pullback both have the exact lower bound. -/
theorem positive_normal_section_depth_data {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (sectionMarked Q) H p) :
    let Sec := sectionMarked Q
    let O := maskA Sec H p
    let W := openSection (strictAlong H (zeroPlane U)) O
    let J := positiveMemberOn Sec H p O
    p ∈ O ∧ ∃ hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n,
      RepairDepthData k (Nat.le_succ n) W hW J := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let Sec := sectionMarked Q
  let O := maskA Sec H p
  let W := openSection (strictAlong H (zeroPlane U)) O
  let J := positiveMemberOn Sec H p O
  let B := geoTransformAlong (barMarked Sec) H
  obtain ⟨hp, hW, hDomain⟩ := positive_normal_native_domain_on_section_mask Q hQ H hH p hLevel hNS
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hSecTest := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBarTest := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hSecTest
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked Sec hSec.isWellFormed) H hBarTest
  have hJ : J.IsWellFormed :=
    IsWellFormed.pullback_val (isWellFormed_memberRestrict (Nat.succ_pos n) hB _) O
  have hSupport : J.N ⊆ W := by
    intro z hz
    have hzB : (z : Y) ∈ B.N := hz.1
    rw [show B.N = strictAlong H (barMarked Sec).N from N_geoTransformAlong _ _] at hzB
    exact MemberInterTowerAlong.strictAlong_mono H
      (show (barMarked Sec).N ⊆ zeroPlane U from fun _ hz => ⟨mem_univ _, hz.2⟩) hzB
  obtain ⟨A, _, _, _, hLift, _, _, _, hATr, _, _⟩ :=
    exists_upper_native_test_history Q hQ H hH
  have hBoundary : B.E = (geoTransformAlong (sectionBarCoefficient Q) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked Sec) (𝔫 := sectionBarCoefficient Q) rfl H
  have hStrictTr : IsTransverse (n + 1) (strictAlong H (zeroPlane U)) B.E := by
    rw [← hLift.carrier, hBoundary]
    exact hATr
  have hWTr : IsTransverse (n + 1) W (B.E.map ((Subtype.val : O → Y) ⁻¹' ·)) :=
    isTransverse_preimage (pullsBackCoordinates_val O) hStrictTr
  have hSub : J.E.Sublist (B.E.map ((Subtype.val : O → Y) ⁻¹' ·)) := by
    have hMember : (memberRestrict B (membersThrough B.E (origMembers Sec H) p)).E.Sublist B.E := by
      rw [memberRestrict_membersThrough_E]
      exact List.filter_sublist
    exact hMember.map ((Subtype.val : O → Y) ⁻¹' ·)
  have hTr : IsTransverse (n + 1) W J.E := isTransverse_of_forall_mem hWTr hSub.subset
  exact ⟨hp, hW, isInvDomain_of_supported_nativePullback (Nat.le_succ n) hW J hJ hSupport hDomain,
    hDomain, hSupport, hTr⟩

/-- The selected cut used by the recursive evaluator has the lower ambient domain. -/
theorem positive_normal_selected_section_isInvDomain {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (sectionMarked Q) H p) :
    IsInvDomain (k - 1) (lowerMarkedM (sectionMarked Q) (s + 1) H p) := by
  obtain ⟨_, _, hDepth⟩ := positive_normal_section_depth_data Q hQ H hH p hLevel hNS
  exact hDepth.ambient_domain

set_option maxHeartbeats 1000000 in
/-- On the actual selected section mask, any paired lift compares the full
canonical continuation at ambient depth k and native depth k - 1. -/
theorem positive_normal_selected_section_canonical_iff {n k s : ℕ}
    {U : Opens (ComplexModel n)} (hn : 0 < n) (hk : 0 < k)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (sectionMarked Q) H p)
    {W : Set (CMfd.of (n := n + 1) (maskA (sectionMarked Q) H p))}
    (hEq : W = openSection (strictAlong H (zeroPlane U)) (maskA (sectionMarked Q) H p))
    (hWc : IsClosed W) (hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n)
    {Z : CMfd.{0} (n + 1)} {S : BlowupTower Y Z}
    {V : Set (CMfd.of (n := n + 1) (openPreimage S (maskA (sectionMarked Q) H p)))}
    {hVc : IsClosed V} {hV : ∀ z ∈ V, RegularAtDim (n := n + 1) V z n}
    {N : BlowupTower (nativeManifold (Nat.le_succ n) W hW) (nativeManifold (Nat.le_succ n) V hV)} :
    let O := maskA (sectionMarked Q) H p
    let J := positiveMemberOn (sectionMarked Q) H p O
    let T := restrict O S
    let B := nativePullback (Nat.le_succ n) W hW J
    Lift (Nat.le_succ n) W hWc hW J.E T V hVc hV N →
      (IsCanonical B ((invFamily hn (k - 1)).inv B) N ↔
        IsCanonical J ((invFamily (Nat.succ_pos n) k).inv J) T) ∧
      (IsCanonical J ((invFamily (Nat.succ_pos n) k).inv J) T →
        ∀ z : nativeManifold (Nat.le_succ n) V hV,
          z ∈ (geoTransformAlong B N).cosupp →
            (invFamily (Nat.succ_pos n) k).inv J T z.val =
              cast (congrArg ValTy (show 1 + (k - 1) = k by omega))
                (depthPadMap 1 (k - 1)
                  (sameIndexMap 1 (k - 1) ((invFamily hn (k - 1)).inv B N z)))) := by
  subst W
  obtain ⟨_, _, hDepth⟩ := positive_normal_section_depth_data Q hQ H hH p hLevel hNS
  intro O J T B hLift
  have hCodim : n + 1 - n = 1 := by omega
  simpa only [hCodim] using hDepth.compare_continuation (Nat.succ_pos n) hn hk hLift

end Hironaka.HironakaG1PositiveNormalSectionDomain
