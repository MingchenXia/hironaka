import Hironaka.Resolution.HironakaG1ActualLaterCommonReference
import Hironaka.Resolution.HironakaG8LocalTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ActualLaterCommonTangent
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain GeneralValue GeneralCompare
  NonmonomialOrderTail InvDomainMemberRestriction InvDomainTowerAlong BoundaryCount
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalContact HironakaActualSectionBoundaryGeometry
  HironakaG1PositiveNormalPhase HironakaG1LaterPositiveMaskContact HironakaG1LaterSelectedActualOrder
  HironakaG1RecursiveMemberValueTransport HironakaG1ActualLaterCompanionTangent
  HironakaG1LaterOrderMaskSupportedLocal HironakaG1LaterOrderMaskNonfactor
  HironakaG8LocalHistory HironakaG8LocalRestrictEquiv HironakaG8LocalContactStage
  ContactRepresentative MarkedIdealOperationsAlong.MarkedIdeal GermIdealPullbackCalculus
  RelativePrincipalizationSpan HironakaActualOpenZeroSectionDifferentials

open HironakaG1ActualLaterCommonReference HironakaG1ActualLaterBornCut
  HironakaG8LocalTransport TangentDirectionAlong ContactEquivalenceAlong
  HironakaActualRelativeNormalGeometry CompanionReductionAlong CompanionRebase
open HomogenizedGlueingTower (strictAlong)

private theorem domain_on_smaller_open {n k : ℕ} {X : CMfd.{0} n}
    {R : MarkedIdeal n X} (hR : R.ideal.IsCoherent) {V W : Opens X} (hWV : W ≤ V)
    (hV : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : V → X) R)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X) R) := by
  have h := isInvDomain_pullback_val (MaxLocusLocal.nestedOpens V W) hV
  have h' := isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hWV).symm h
  rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo hR hWV] at h'

set_option maxHeartbeats 1800000 in
/-- The actual incoming normal direction survives on the same exact order-mask
window as both recursive domains and their supported local weak class. -/
theorem exists_actual_later_common_supported_tangent {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let B := CMfd.of (n := n + 1) C
    let J := compAt L L.d (.refl : BlowupTower A A)
    let R := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A) (positiveMemberOn Sec H p O)
    (¬ IsSpecial Sec H p) →
    ∃ (a : C) (W : Opens B) (u : W → ℂ) (haW : a ∈ W), a.val.val = p ∧
      let D := CMfd.of (n := n + 1) W
      let Jw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) J
      let Rw := MarkedIdeal.pullback (M' := D) (Subtype.val : W → B) R
      IsInvDomain (k + 1) Jw ∧ IsInvDomain k Rw ∧ LocWPEquiv (X := D) Jw Rw ∧
      IsTangentDirectionAlong Jw.N Jw.ideal Jw.d univ u ∧
      Jw.N ∩ {z : W | u z = 0} = Rw.N ∧
      (⟨a, haW⟩ : W) ∈ Rw.N ∧ u ⟨a, haW⟩ = 0 ∧
      Jw.d = J.d ∧ Jw.E = J.E.map ((Subtype.val : W → B) ⁻¹' ·) := by
  intro X P Sec r H S p O A L C B J R hNSS
  obtain ⟨a, V, ha, haV, _, _, hRv, hClass, _, _⟩ :=
    exists_actual_later_common_supported_reference Q hQ T hCan y hy hLevel hNS hNSS
  obtain ⟨hp, hq, Ω, v, hpΩ, hp0, hJ, ht, hTrace⟩ :=
    exists_actual_later_initial_order_companion_tangent Q hQ T hCan y hy hLevel hNS
  let f : C → _ := fun z => z.val.val
  let a' : C := ⟨⟨p, hp⟩, hq⟩
  have ha' : a = a' := Subtype.ext (Subtype.ext ha)
  have haΩ : a ∈ Ω := ha'.symm ▸ hpΩ
  let W : Opens B := V ⊓ ⟨Ω, ht.isOpen⟩
  have haW : a ∈ W := ⟨haV, haΩ⟩
  have hWV : W ≤ V := inf_le_left
  let u : W → ℂ := (v ∘ f) ∘ Subtype.val
  have hRcoh : R.ideal.IsCoherent := by
    let F := invFamily (Nat.succ_pos n) (k + 1)
    have hP := properNormalMarked_isInvDomain Q hQ
    have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
    have hTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical F P hP hMax
      (Nat.succ_pos n) T hCan).2.1
    have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
    let BS := geoTransformAlong (barMarked Sec) H
    have hSec : IsInvDomain (k + 1) Sec := section_projected_domain (k + 1) Q.N Q.E Q.ideal Q.d hQ
    have hST := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hHeadTest
    have hBST := ((HironakaG8HomStable.bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hST
    have hBS : BS.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (StepOneLowerDomain.isWellFormed_barMarked Sec hSec.isWellFormed) H hBST
    have hKS := isWellFormed_memberRestrict (Nat.succ_pos n) hBS
      (membersThrough BS.E (origMembers Sec H) p)
    exact (MarkedIdealRestrictOpen.IsWellFormed.pullback_val
      (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hKS O) C).isCoherent
  have hAlong : IsTangentDirectionAlong J.N J.ideal J.d W (v ∘ f) :=
    ⟨W.isOpen, fun z hz => ht.mem z hz.2, fun z hz => ht.multiplicity_one z hz.2⟩
  have hTan := isTangentDirectionAlong_pullback_val W
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ.isWellFormed.isCoherent hg) hAlong
  let Jw := MarkedIdeal.pullback (M' := CMfd.of (n := n + 1) W) (Subtype.val : W → B) J
  let Rw := MarkedIdeal.pullback (M' := CMfd.of (n := n + 1) W) (Subtype.val : W → B) R
  have hRN := supported_member_carrier_on_initial_order_mask Q (s := s) H p
  have hZero : Jw.N ∩ {z : W | u z = 0} = Rw.N := by
    ext z
    change (z.val ∈ J.N ∧ u z = 0) ↔ z.val ∈ R.N
    rw [hRN]
    have he := Set.ext_iff.mp hTrace z.val
    exact ⟨fun hz => (he.mp ⟨hz, z.property.2⟩).1,
      fun hz => (he.mpr ⟨hz, z.property.2⟩).1⟩
  have ha0 : u ⟨a, haW⟩ = 0 := by
    change v (f a) = 0
    rw [show f a = p from ha]
    exact hp0
  have haN : a ∈ J.N := by
    obtain ⟨_, _, _, _, hpL, hLp, _, _, _⟩ :=
      original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
    rw [ha']
    change a' ∈ (companionOf (n + 1) (M := B) _ L.d).N
    simp only [companionOf, companionAlong_N, geoTransformAlong_refl]
    exact L.cosupp_subset_N hLp
  have haR : (⟨a, haW⟩ : W) ∈ Rw.N := hZero ▸ ⟨haN, ha0⟩
  exact ⟨a, W, u, haW, ha, isInvDomain_pullback_val W hJ, domain_on_smaller_open hRcoh hWV hRv,
    locWPEquiv_restrict_of_le hJ.isWellFormed.isCoherent hRcoh hWV hClass,
    hTan, hZero, haR, ha0, rfl, rfl⟩

end
end Hironaka.HironakaG1ActualLaterCommonTangent
