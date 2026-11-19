import Hironaka.Resolution.HironakaG1LaterSelectedSectionGapCanonical
import Hironaka.Resolution.HironakaG8PowerLowerMarks

/-! Actual later contact and section comparisons at two independent cuts. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1LaterSectionPairOrder

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres DivisorExponentAlong HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaG8PowerLowerMarks
  HironakaG1OriginalUnequalMarkCanonical HironakaG1LaterSelectedSectionClass
  HironakaG1LaterSelectedSectionGapCanonical HironakaG1RecursiveMemberValueTransport
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HomogenizedIdealAlong InvDomainMemberRestriction StepOneValue TangentDirectionAlong
  CoefficientIdealRestriction
open HomogenizedGlueingTower (strictAlong)

/-- The class data of a later contact and section cut, with their
literal marks fixed by the original source mark. -/
structure LaterSectionComparison {n : ℕ} (d k : ℕ) {X : CMfd.{0} (n+1)}
    (C S : MarkedIdeal (n+1) X) : Prop where
  contactDomain : IsInvDomain k C
  sectionDomain : IsInvDomain k S
  localClass : LocWPEquiv C S
  carrier : C.N = S.N
  exponents : ∀ H ∈ C.E, ∀ x ∈ C.cosupp, x ∈ H →
    S.d * divExpAlong (n+1) C.N C.ideal H x = C.d * divExpAlong (n+1) S.N S.ideal H x
  contactMark : C.d = coefficientMark (coefficientMark (coefficientMark d))
  sectionMark : S.d = coefficientMark (coefficientMark d)

private theorem positiveMemberOn_mark {n : ℕ} {X Y : CMfd.{0} n} (J : MarkedIdeal n X)
    (T : BlowupTower X Y) (p : Y) (W : Opens Y) :
    (positiveMemberOn J T p W).d = coefficientMark (coefficientMark J.d) := by
  change (memberRestrict (geoTransformAlong (barMarked J) T)
    (membersThrough (geoTransformAlong (barMarked J) T).E (origMembers J T) p)).d = _
  rw [memberRestrict_d, coeffMarkedAlong_mark, d_geoTransformAlong]
  rfl

set_option maxHeartbeats 1300000 in
/-- The actual later contact comparison has marks independent of its
chosen chronological cut and open window. -/
theorem later_section_comparison {n k l : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (H : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) (W : Opens Y) (u : Y → ℂ) :
    let P := properNormalMarked Q
    let L := positiveMemberOn P H p W
    let S := positiveMemberOn (sectionMarked Q) H p W
    let D := strictAlong H (P.N ∩ {x | relativeNormalCoordinate U x = 0})
    let C := withN (coeffMarkedAlong L) (L.N ∩ {x : W | u x.val = 0})
    IsInvDomain k L →
    IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) →
    L.N ∩ {x : W | u x.val = 0} = L.N ∩ (Subtype.val : W → Y) ⁻¹' D →
    IsInvDomain l C → LaterSectionComparison (X := CMfd.of (n := n+1) W) Q.d l C S := by
  intro P L S D C hL hu hTrace hC
  obtain ⟨hS, hExp, _⟩ :=
    later_selected_section_canonical_iff_of_contact_domain Q hQ H hH p W u hL hu hTrace hC
  obtain ⟨hN, _, _, hClass⟩ :=
    selected_normal_contact_section_class_on_window Q hQ H hH p W u hL hu hTrace
  have hLd : L.d = coefficientMark (coefficientMark Q.d) := positiveMemberOn_mark P H p W
  have hCd : C.d = coefficientMark (coefficientMark (coefficientMark Q.d)) := by
    change (coeffMarkedAlong L).d = _
    rw [coeffMarkedAlong_mark, hLd]
  exact ⟨hC, hS, hClass, hN, hExp, hCd, positiveMemberOn_mark (sectionMarked Q) H p W⟩

/-- Two later prescribed contacts compare at their actual canonical
endpoints by comparing the corresponding supported section values.
The two upper cuts and the two lower histories can be independent. -/
theorem LaterSectionComparison.lt_iff {n d k : ℕ}
    {X₁ X₂ Y₁ Y₂ : CMfd.{0} (n+1)}
    {C₁ S₁ : MarkedIdeal (n+1) X₁} {C₂ S₂ : MarkedIdeal (n+1) X₂}
    (h₁ : LaterSectionComparison d k C₁ S₁) (h₂ : LaterSectionComparison d k C₂ S₂)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (hCan₁ : IsCanonical C₁ ((invFamily (Nat.succ_pos n) k).inv C₁) T₁)
    (hCan₂ : IsCanonical C₂ ((invFamily (Nat.succ_pos n) k).inv C₂) T₂)
    (x : Y₁) (hx : x ∈ (geoTransformAlong C₁ T₁).cosupp)
    (y : Y₂) (hy : y ∈ (geoTransformAlong C₂ T₂).cosupp) :
    let R := invFamily (Nat.succ_pos n) k
    R.inv C₁ T₁ x < R.inv C₂ T₂ y ↔ R.inv S₁ T₁ x < R.inv S₂ T₂ y := by
  have hDim₁ := SameCarrierDim.of_N_eq h₁.carrier
  have hDim₂ := SameCarrierDim.of_N_eq h₂.carrier
  have hSC₁ := (invFamily_isCanonical_iff_of_local (Nat.succ_pos n) C₁ S₁
    h₁.contactDomain h₁.sectionDomain h₁.localClass hDim₁ h₁.exponents T₁).mp hCan₁
  have hSC₂ := (invFamily_isCanonical_iff_of_local (Nat.succ_pos n) C₂ S₂
    h₂.contactDomain h₂.sectionDomain h₂.localClass hDim₂ h₂.exponents T₂).mp hCan₂
  exact canonicalTwoPairCuts_invFamily (Nat.succ_pos n) k C₁ S₁ C₂ S₂
    h₁.contactDomain h₁.sectionDomain h₂.contactDomain h₂.sectionDomain
    h₁.localClass hDim₁ h₁.exponents h₂.localClass hDim₂ h₂.exponents
    (h₁.contactMark.trans h₂.contactMark.symm) (h₁.sectionMark.trans h₂.sectionMark.symm)
    trivial trivial trivial trivial T₁ T₂ hCan₁ hSC₁ hCan₂ hSC₂ x hx y hy

end Hironaka.HironakaG1LaterSectionPairOrder
