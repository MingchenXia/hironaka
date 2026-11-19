import Hironaka.Resolution.HironakaG1LaterContactFieldExistence
import Hironaka.Resolution.HironakaActualOpenTangentDescent
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedChoiceImageTrace

/-! The later tangent on an actual subwindow of the born-aware positive mask. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LaterPositiveMaskContact

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec StepOneValue StepOneLowerDomain
  BoundaryCount MemberInterLocusAlong InvDomainMemberRestriction TangentDirectionAlong ContactEquivalenceAlong
  HironakaG8HomStable HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1RecursiveMemberValueTransport
  HironakaG1LaterContactFieldExistence HironakaActualOpenTangentDescent
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  RelativePrincipalizationSpan HironakaSmoothSubmersionOrderedChoiceImageTrace
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)

/-- The actual positive lower record retains its domain on every smaller
open window of the literal born-aware mask. -/
theorem positive_member_domain_on_subwindow {n k s : ℕ} {X Y : CMfd.{0} n} (hn : 0 < n)
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) (H : BlowupTower X Y)
    (hH : IsGeoTestTower (barMarked P) H) (p : Y) (hl : level P H p = s + 1)
    (W : Opens Y) (hW : W ≤ maskA P H p) :
    IsInvDomain (k - 1) (positiveMemberOn P H p W) := by
  let B := geoTransformAlong (barMarked P) H
  let E₀ := origMembers P H
  have hBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hB : IsInvDomain k B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hBar H hH
  have hE₀ : ∀ D ∈ E₀, D ∈ B.E := fun _ hD => List.mem_of_mem_take hD
  have hpLevel : 1 ≤ boundaryCount E₀ p := by
    have h := hl
    change boundaryCount E₀ p = s + 1 at h
    omega
  refine isInvDomain_pullback_val_of_forall (isWellFormed_memberRestrict hn hB.isWellFormed _)
    (dimLE_memberRestrict hn hB.isWellFormed (membersThrough_nonempty hE₀ hpLevel) hB.dimLE)
    (one_le_memberRestrict_d B _) W ?_
  rintro z ⟨hzN, hzI⟩ hzW
  have hzM := interior_subset (hW hzW)
  have hzI' := memberInter_membersThrough hE₀ p ▸ hzI
  have hiff : ∀ D ∈ E₀, p ∈ D ↔ z ∈ D :=
    fun D hD => ⟨fun hpD => hzI' D hD hpD, fun hzD => hzM.1 D hD hzD⟩
  have hset : memberInter B.E (membersThrough B.E E₀ p) = {w | ∀ D ∈ E₀, z ∈ D → w ∈ D} := by
    rw [memberInter_membersThrough hE₀ p]
    ext w
    exact forall_congr' fun D => forall_congr' fun hD => by rw [hiff D hD]
  refine isNonzeroAlongAt_memberRestrict hB.isWellFormed.isClosedSubmanifold_N
    hB.isWellFormed.isCoherent hB.one_le_d E₀ _ hzN
    (Eventually.of_forall fun w => by rw [hset]; exact Iff.rfl) fun hzL => ?_
  have hlev : level P H z = level P H p := (boundaryCount_eq_of_forall_iff hiff).symm
  exact hzM.2 ⟨hlev, Or.inr ⟨by rw [hlev, hl]; omega, hzL⟩⟩

/-- At a positive nonspecial upper cosupport point, a genuine subwindow of
the literal mask carries the full selected lower record, with its ordered
boundary and prescribed strict normal contact trace. -/
theorem later_positive_mask_contact {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hp : p ∈ (geoTransformAlong (properNormalMarked Q) H).cosupp)
    (hl : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) H p) :
    let P := properNormalMarked Q
    let M := maskA P H p
    let B := geoTransformAlong (barMarked P) H
    let I := membersThrough B.E (origMembers P H) p
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    ∃ (W : Opens Y) (hWM : W ≤ M) (u : Y → ℂ),
      let L := positiveMemberOn P H p W
      p ∈ W ∧ p ∈ D ∧ IsInvDomain k L ∧
      L = MarkedIdeal.pullback (Opens.inclusion hWM) (positiveMemberOn P H p M) ∧
      L.E = (((List.finRange B.E.length).filter fun i => i ∉ I).map B.E.get).map
        ((Subtype.val : W → Y) ⁻¹' ·) ∧
      IsTangentDirectionAlong L.N L.ideal L.d univ (u ∘ (Subtype.val : W → Y)) ∧
      L.N ∩ {z : W | u z.val = 0} = L.N ∩ (Subtype.val : W → Y) ⁻¹' D := by
  classical
  intro P M B I D
  let X := CMfd.of (n := n + 1) (productOpen U)
  let K := memberRestrict B I
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBar := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) P hP
  have hBT := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hBar H hBT
  have hK := isWellFormed_memberRestrict (Nat.succ_pos n) hB.isWellFormed I
  have hpM : p ∈ M := mem_maskA (X := X) P hP.isWellFormed hP.one_le_d
    (Nat.succ_pos n) H hBT (by rw [hl]; omega) hNS
  have hpS := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).2 hH ▸ hp
  have hpD : p ∈ D := by
    have hpSN := (geoTransformAlong (sectionMarked Q) H).cosupp_subset_N hpS
    rw [N_geoTransformAlong] at hpSN
    change p ∈ strictAlong H (liftedCarrier Q.N) at hpSN
    rw [← normal_contact_carrier Q] at hpSN
    exact hpSN
  obtain ⟨V, u, hpV, hu, hTrace⟩ := exists_later_positive_selected_normal_contact Q hQ H hH hpD
  let W := V ⊓ M
  have hWM : W ≤ M := inf_le_right
  have hWV : W ≤ V := inf_le_left
  have hpW : p ∈ W := ⟨hpV, hpM⟩
  have hDom : IsInvDomain k (positiveMemberOn P H p W) := by
    simpa using positive_member_domain_on_subwindow (Nat.succ_pos n) P hP H hBT p hl W hWM
  have hDown := isTangentDirectionAlong_of_open_pullback K.N hK.isClosedSubmanifold_N
    K.ideal hK.isCoherent K.d V univ u hu
  have hVeq : (Subtype.val : V → Y) '' (univ : Set V) = (V : Set Y) := by
    ext x
    exact ⟨fun ⟨z, _, hz⟩ => hz ▸ z.property, fun hx => ⟨⟨x, hx⟩, trivial, rfl⟩⟩
  rw [hVeq] at hDown
  have hOnW : IsTangentDirectionAlong K.N K.ideal K.d W u :=
    ⟨W.isOpen, fun y hy => hDown.mem y (hWV hy),
      fun y hy => hDown.multiplicity_one y (hWV hy)⟩
  refine ⟨W, hWM, u, hpW, hpD, hDom, ?_, rfl, ?_, ?_⟩
  · exact whole_markedPullback_comp contMDiff_subtype_val (contMDiff_inclusion hWM) K hK.isCoherent
  · exact isTangentDirectionAlong_pullback_val W
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hK.isCoherent hg) hOnW
  · ext z
    exact Set.ext_iff.mp hTrace (Opens.inclusion hWV z)

end Hironaka.HironakaG1LaterPositiveMaskContact
