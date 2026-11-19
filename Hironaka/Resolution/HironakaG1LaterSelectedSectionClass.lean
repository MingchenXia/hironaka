import Hironaka.Resolution.HironakaG1LaterPositiveMaskContact
import Hironaka.Resolution.HironakaG1ClassReferenceContact
import Hironaka.Resolution.HironakaG1SeparateCarrierMemberCut

/-! Comparison of later selected normal contact with the literal section cut. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterSelectedSectionClass

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec StepOneValue BoundaryCount InvDomainMemberRestriction
  CoefficientIdealRestriction HomogenizedIdealAlong TangentDirectionAlong ContactEquivalenceAlong
  HironakaG8LocalHistory HironakaG8ContactMax
  HironakaG1LaterPositiveMaskContact HironakaG1ClassReferenceContact HironakaG1SeparateCarrierMemberCut
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1RecursiveMemberValueTransport
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaActualRelativeNormalGeometry
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)

/-- A genuine contact on a given later window compares directly to the
literal supported section member record on the same window. -/
theorem selected_normal_contact_section_class_on_window {n k : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) (W : Opens Y) (u : Y → ℂ) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    let L := positiveMemberOn P H p W
    let S := positiveMemberOn Sec H p W
    let C := withN (coeffMarkedAlong L) (L.N ∩ {z : W | u z.val = 0})
    IsInvDomain k L →
    IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) →
    L.N ∩ {z : W | u z.val = 0} = L.N ∩ (Subtype.val : W → Y) ⁻¹' D →
    C.N = S.N ∧ C.E = L.E ∧ C.E = S.E ∧
      LocWPEquiv (X := CMfd.of (n := n + 1) W) C S := by
  intro P Sec D L S C hL hu hTrace
  let X := CMfd.of (n := n + 1) (productOpen U)
  let B := geoTransformAlong (barMarked P) H
  let B' := geoTransformAlong (barMarked Sec) H
  have hP := properNormalMarked_isInvDomain Q hQ
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hPS := properNormalMarked_locWPEquiv_section Q hQ
  let A := CMfd.of (n := n + 1) W
  have hLS : LocWPEquiv (X := A) L S :=
    member_stage_local_of_local (X := X) (Nat.succ_pos n) P Sec hP hSec hPS H hH W p
  have hCN : IsClosedSubmanifold (X := A) (n + 1) C.N := by
    change IsClosedSubmanifold (X := A) (n + 1) (L.N ∩ {z : W | u z.val = 0})
    simpa only [Set.inter_univ, Function.comp_apply] using isClosedSubmanifold_contact_along
      hL.isWellFormed.isClosedSubmanifold_N hL.isWellFormed.isCoherent hu
  have hRef : MaxContact L C.N := by
    change MaxContact L (L.N ∩ {z : W | u z.val = 0})
    simpa only [Set.inter_univ, Function.comp_apply] using maxContact_base L hL.isWellFormed.isCoherent hu
  have hLC : LocWPEquiv (X := A) L C :=
    locWPEquiv_of_reference_maxContact L L
      hL.isWellFormed.isClosedSubmanifold_N hL.isWellFormed.isCoherent hL.one_le_d
      hL.isWellFormed.isClosedSubmanifold_N hL.isWellFormed.isCoherent hL.one_le_d
      rfl (LocEquiv.refl _ L) C.N hCN (fun _ hz => hz.1) hRef
  have hB' : B'.N = D := by
    change (geoTransformAlong (barMarked Sec) H).N = D
    rw [N_geoTransformAlong]
    exact congrArg (strictAlong H) (normal_contact_carrier Q).symm
  have hDB : D ⊆ B.N := by
    change D ⊆ (geoTransformAlong (barMarked P) H).N
    rw [N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono H (fun _ hy => hy.1)
  have hOrig : origMembers P H = origMembers Sec H :=
    HironakaG8MemberLoci.origMembers_eq_of_E_eq (A := P) (B := Sec) rfl H
  have hOldB : ∀ E ∈ origMembers P H, E ∈ B.E := fun _ h => List.mem_of_mem_take h
  have hOldB' : ∀ E ∈ origMembers Sec H, E ∈ B'.E := fun _ h => List.mem_of_mem_take h
  have hEqN : C.N = S.N := by
    change L.N ∩ {z : W | u z.val = 0} = S.N
    rw [hTrace]
    change (Subtype.val : W → Y) ⁻¹' (B.N ∩ memberInter B.E
      (membersThrough B.E (origMembers P H) p)) ∩ (Subtype.val : W → Y) ⁻¹' D =
      (Subtype.val : W → Y) ⁻¹' (B'.N ∩ memberInter B'.E (membersThrough B'.E (origMembers Sec H) p))
    rw [memberInter_membersThrough hOldB p, memberInter_membersThrough hOldB' p, hOrig, hB']
    ext z
    exact ⟨fun hz => ⟨hz.2, hz.1.2⟩, fun hz => ⟨⟨hDB hz.1, hz.2⟩, hz.1⟩⟩
  exact ⟨hEqN, rfl, hLS.wEquiv.1, hLC.symm.trans hLS⟩

/-- The prescribed later normal contact gives a whole marked coefficient
restriction in the same local weak class as the literal supported member cut,
with the same actual carrier and ordered boundary. -/
theorem later_selected_normal_contact_section_class {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hp : p ∈ (geoTransformAlong (properNormalMarked Q) H).cosupp)
    (hl : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) H p) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let M := maskA P H p
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    ∃ (W : Opens Y) (hWM : W ≤ M) (u : Y → ℂ),
      let L := positiveMemberOn P H p W
      let S := positiveMemberOn Sec H p W
      let C := withN (coeffMarkedAlong L) (L.N ∩ {z : W | u z.val = 0})
      p ∈ W ∧ p ∈ D ∧ IsInvDomain k L ∧
      L = MarkedIdeal.pullback (Opens.inclusion hWM) (positiveMemberOn P H p M) ∧
      IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) ∧
      C.N = L.N ∩ (Subtype.val : W → Y) ⁻¹' D ∧
      C.N = S.N ∧ C.E = L.E ∧ C.E = S.E ∧
      LocWPEquiv (X := CMfd.of (n := n + 1) W) C S := by
  intro P Sec M D
  obtain ⟨W, hWM, u, hpW, hpD, hL, hPull, _, hu, hTrace⟩ :=
    later_positive_mask_contact Q hQ H hH p hp hl hNS
  obtain ⟨hN, hE, hES, hClass⟩ :=
    selected_normal_contact_section_class_on_window Q hQ H hH p W u hL hu hTrace
  exact ⟨W, hWM, u, hpW, hpD, hL, hPull, hu, hTrace, hN, hE, hES, hClass⟩

end Hironaka.HironakaG1LaterSelectedSectionClass
