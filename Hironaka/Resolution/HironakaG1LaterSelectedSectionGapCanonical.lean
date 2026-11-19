import Hironaka.Resolution.HironakaG1LaterSelectedSectionClass
import Hironaka.Resolution.HironakaG1ChosenCommonContactClassData
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaG1DifferentCarrierMemberClassData

/-! Cosupport gaps discharge the normalized divisor comparison on the later contact window. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterSelectedSectionGapCanonical

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealRestrictOpen ResolutionInvariantSpec CanonicalCentres StepOneValue InvDomainMemberRestriction
  CoefficientIdealRestriction HomogenizedIdealAlong TangentDirectionAlong DivisorExponentAlong
  HironakaG8LocalHistory HironakaG8HomStable HironakaG8GapNormalizedExponent HironakaG11InvBMClass
  HironakaG1LaterSelectedSectionClass HironakaG1ChosenCommonContactClassData
  HironakaG1CoefficientCarrierClassData HironakaG1DifferentCarrierMemberClassData
  HironakaG1OriginalUnequalMarkCanonical
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1RecursiveMemberValueTransport HironakaActualCoefficientDivisorExponentGap
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaActualRelativeNormalGeometry
open HomogenizedGlueingTower (strictAlong)

set_option maxHeartbeats 1200000 in
/-- The genuine contact and the literal section cut have equal normalized
exponents and the same original canonical continuations on the actual window.
Both cosupport gaps follow from their coefficient constructions. -/
theorem later_selected_section_canonical_iff_of_contact_domain {n k l : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) (W : Opens Y)
    (u : Y → ℂ) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    let A := CMfd.of (n := n + 1) W
    let L := positiveMemberOn P H p W
    let S := positiveMemberOn Sec H p W
    let C := withN (coeffMarkedAlong L) (L.N ∩ {z : W | u z.val = 0})
    IsInvDomain k L →
    IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) →
    L.N ∩ {z : W | u z.val = 0} = L.N ∩ (Subtype.val : W → Y) ⁻¹' D →
    IsInvDomain l C →
    IsInvDomain l S ∧
      (∀ F ∈ C.E, ∀ x ∈ C.cosupp, x ∈ F →
        S.d * divExpAlong (n + 1) C.N C.ideal F x =
          C.d * divExpAlong (n + 1) S.N S.ideal F x) ∧
      (∀ {Z : CMfd.{0} (n + 1)} (T : BlowupTower A Z),
        IsCanonical C ((invFamily (Nat.succ_pos n) l).inv C) T ↔
          IsCanonical S ((invFamily (Nat.succ_pos n) l).inv S) T) := by
  intro P Sec D A L S C hL hu hTrace hC
  let X := CMfd.of (n := n + 1) (productOpen U)
  obtain ⟨hN, _, hE, hClass⟩ :=
    selected_normal_contact_section_class_on_window Q hQ H hH p W u hL hu hTrace
  have hGapC : HasCosupportGap (X := A) C := by
    intro x _ hx
    change x ∈ GermIdealOrder.cosupport (n + 1) C.N (coeffMarkedAlong L).ideal 1 at hx
    change x ∈ GermIdealOrder.cosupport (n + 1) C.N (coeffMarkedAlong L).ideal (coeffMarkedAlong L).d
    rw [← coefficient_restriction_cosupport_gap L hL.isWellFormed.isClosedSubmanifold_N
      hL.isWellFormed.isCoherent hL.one_le_d C.N (fun _ h => h.1)]
    exact hx
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBT := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
  have hBS := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) Sec hSec
  have hStage := InvDomainTowerAlong.isInvDomain_geoTransformAlong hBS H hBT
  let B := geoTransformAlong (barMarked (X := X) Sec) H
  let I := membersThrough B.E (origMembers Sec H) p
  have hBWF : B.IsWellFormed := (show IsInvDomain k B from hStage).isWellFormed
  have hSWF : S.IsWellFormed :=
    IsWellFormed.pullback_val (isWellFormed_memberRestrict (Nat.succ_pos n) hBWF I) W
  have hSd : 1 ≤ S.d := one_le_memberRestrict_d B I
  have hS : IsInvDomain l S :=
    isInvDomain_of_sameCarrier_cosupp (X := A) S C hC hSWF.isCoherent hSd
      hN.symm hE.symm hClass.cosupp_eq_base.symm
  have hGapS : HasCosupportGap (X := A) S :=
    member_open_hasCosupportGap B hStage I W
  have hDim := SameCarrierDim.of_N_eq hN
  have hExp := normalized_exponents_of_gap_sameCarrierDim (Nat.succ_pos n) C S hC hS hClass
    hDim hGapC hGapS
  exact ⟨hS, hExp, fun T =>
    invFamily_isCanonical_iff_of_local (Nat.succ_pos n) C S hC hS hClass hDim hExp T⟩

end Hironaka.HironakaG1LaterSelectedSectionGapCanonical
