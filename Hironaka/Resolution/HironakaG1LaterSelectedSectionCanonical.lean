import Hironaka.Resolution.HironakaG1LaterSelectedSectionClass
import Hironaka.Resolution.HironakaG1ChosenCommonContactClassData
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical

/-! Recursive domain and canonicality for later normal contact and its supported section. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Classical

namespace Hironaka.HironakaG1LaterSelectedSectionCanonical

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres StepOneValue InvDomainMemberRestriction InvDomainRebase
  CoefficientIdealRestriction HomogenizedIdealAlong TangentDirectionAlong DivisorExponentAlong
  HironakaG8LocalHistory HironakaG8HomStable
  HironakaG1LaterSelectedSectionClass HironakaG1ChosenCommonContactClassData
  HironakaG1OriginalUnequalMarkCanonical HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1RecursiveMemberValueTransport
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaActualRelativeNormalGeometry
open HomogenizedGlueingTower (strictAlong)

/-- Every retained member meeting the actual positive mask comes from the
born suffix of the current ordered boundary. -/
theorem exists_born_member_of_mem_retained_on_mask {n : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (H : BlowupTower X Y) (p : Y) (W : Opens Y)
    (hWM : W ≤ maskA P H p) {F : Set W}
    (hF : F ∈ (positiveMemberOn P H p W).E) {z : W} (hz : z ∈ F) :
    ∃ G ∈ (geoTransformAlong (barMarked P) H).E.drop P.E.length,
      (Subtype.val : W → Y) ⁻¹' G = F := by
  let B := geoTransformAlong (barMarked P) H
  change F ∈ (memberRestrict B (membersThrough B.E (origMembers P H) p)).E.map
    ((Subtype.val : W → Y) ⁻¹' ·) at hF
  rw [memberRestrict_membersThrough_E] at hF
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
  have hG' := List.mem_filter.mp hG
  have hGnot : G ∉ origMembers P H := by
    intro hOld
    have hpG := (interior_subset (hWM z.property)).1 G hOld hz
    exact of_decide_eq_true hG'.2 ⟨hOld, hpG⟩
  have hAll : B.E.take P.E.length ++ B.E.drop P.E.length = B.E :=
    List.take_append_drop P.E.length B.E
  have hSplit := List.mem_append.mp (hAll ▸ hG'.1)
  exact ⟨G, hSplit.resolve_left hGnot, rfl⟩

set_option maxHeartbeats 1500000 in
/-- The supported section acquires the exact recursive bound of the contact
record. The normalized exponent hypothesis for original canonicality only
ranges over born members meeting that record's cosupport on the window. -/
theorem later_selected_section_domain_and_canonical_iff {n k l : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) (W : Opens Y)
    (hWM : W ≤ maskA (properNormalMarked Q) H p) (u : Y → ℂ) :
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
      ((∀ G ∈ (geoTransformAlong (barMarked P) H).E.drop P.E.length,
        let F := (Subtype.val : W → Y) ⁻¹' G
        F ∈ C.E → ∀ x ∈ C.cosupp, x ∈ F →
          S.d * divExpAlong (n + 1) C.N C.ideal F x =
            C.d * divExpAlong (n + 1) S.N S.ideal F x) →
      ∀ {Z : CMfd.{0} (n + 1)} (T : BlowupTower A Z),
        IsCanonical C ((invFamily (Nat.succ_pos n) l).inv C) T ↔
          IsCanonical S ((invFamily (Nat.succ_pos n) l).inv S) T) := by
  intro P Sec D A L S C hL hu hTrace hC
  let X := CMfd.of (n := n + 1) (productOpen U)
  obtain ⟨hN, hEL, hE, hClass⟩ :=
    selected_normal_contact_section_class_on_window Q hQ H hH p W u hL hu hTrace
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBT := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
  have hBS := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) Sec hSec
  have hStage := InvDomainTowerAlong.isInvDomain_geoTransformAlong hBS H hBT
  have hSelected := isWellFormed_memberRestrict (Nat.succ_pos n) hStage.isWellFormed
    (membersThrough (geoTransformAlong (barMarked Sec) H).E (origMembers Sec H) p)
  have hSWF : S.IsWellFormed := IsWellFormed.pullback_val hSelected W
  have hSd : 1 ≤ S.d :=
    one_le_memberRestrict_d (geoTransformAlong (barMarked (X := X) Sec) H)
      (membersThrough (geoTransformAlong (barMarked (X := X) Sec) H).E (origMembers Sec H) p)
  have hS : IsInvDomain l S :=
    isInvDomain_of_sameCarrier_cosupp (X := A) S C hC hSWF.isCoherent hSd
      hN.symm hE.symm hClass.cosupp_eq_base.symm
  refine ⟨hS, fun hBorn Z T => ?_⟩
  apply invFamily_isCanonical_iff_of_local (Nat.succ_pos n) C S hC hS hClass
    (HironakaG11InvBMClass.SameCarrierDim.of_N_eq hN) _ T
  intro F hF x hx hxF
  obtain ⟨G, hG, rfl⟩ := exists_born_member_of_mem_retained_on_mask P H p W hWM
    (hEL ▸ hF) hxF
  exact hBorn G hG hF x hx hxF

end Hironaka.HironakaG1LaterSelectedSectionCanonical
