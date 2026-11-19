import Hironaka.Resolution.HironakaG1ActualLaterCompanionTangent
import Hironaka.Resolution.HironakaG1BornSelectedCompanionPhase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ActualLaterBornCut
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain GeneralValue
  CompanionRebase CompanionReductionAlong NonmonomialOrderTail
  HironakaG1ActualLaterOrderRun HironakaG1LaterSelectedActualOrder
  HironakaG1LaterPositiveMaskContact HironakaG1PositiveNormalPhase
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualOpenZeroSectionDifferentials HironakaActualOpenTangentDescent
  InvDomainMemberRestriction InvDomainTowerAlong BoundaryCount RelativePrincipalizationSpan
  TangentDirectionAlong ContactEquivalenceAlong DerivativeIdealAlong DerivativeIdealAlongEtale
  HironakaActualRawCompanionNaturality HironakaG8E4cCompanion MarkedIdealOperationsAlong RestrictedIdealExtension RestrictLeCalculus MarkedIdealOperationsAlong.MarkedIdeal
open HomogenizedGlueingTower (strictAlong)
open HomogenizedGlueingLiftAlong HironakaActualRelativeNormalGeometry HironakaG1ProperCarrierNormalLocalClass

open HironakaG1ActualLaterCompanionTangent HironakaG1BornSelectedCompanionPhase
  HironakaG1RecursiveMemberValueTransport MarkedIdealEquivalence
  MarkedIdealEquivalence.MarkedIdeal HironakaG1LaterSelectedSectionClass
  CompanionReductionAlong HomogenizedIdealAlong CoefficientIdealRestriction HironakaG8LocalHistory

set_option maxHeartbeats 1800000 in
/-- A supported reference for the actual same-mark companion gives a born-aware
cut using the genuine normal tangent from the upper strict section. -/
theorem exists_actual_later_born_cut {n k l s b : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
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
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    let f : C → _ := fun z => z.val.val
    let I : BlowupTower B B := .refl
    ∀ (R : MarkedIdeal (n + 1) B), IsInvDomain l R → LocWPEquiv J R →
    R.N = J.N ∩ f ⁻¹' D →
    (∀ a : C, f a = p → level J I a = b + 1 ∧ ¬ IsSpecial J I a) →
    ∃ (a : C) (W : Opens B) (u : B → ℂ),
      f a = p ∧ a ∈ W ∧ W ≤ maskA J I a ∧ u a = 0 ∧
      let K := positiveMemberOn J I a W
      let R' := positiveMemberOn R I a W
      let Cut := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
      IsInvDomain k K ∧
      IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : W → B)) ∧
      Cut.N = R'.N ∧ Cut.E = R'.E ∧
      Cut.E = ((barMarked J).E.filter (fun F => decide ¬ (F ∈ origMembers J I ∧ a ∈ F))).map
        ((Subtype.val : W → B) ⁻¹' ·) ∧
      LocWPEquiv (X := CMfd.of (n := n + 1) W) Cut R' := by
  intro X P r H S p O A L C B J D f I R hR hClass hRN hBorn
  obtain ⟨hp, hq, Ω, u, hpΩ, hpU, hJ, hTangent, hTrace⟩ :=
    exists_actual_later_initial_order_companion_tangent Q hQ T hCan y hy hLevel hNS
  let V : Opens B := ⟨Ω, hTangent.isOpen⟩
  let a : C := ⟨⟨p, hp⟩, hq⟩
  have ha : f a = p := rfl
  have haV : a ∈ V := hpΩ
  have haU : (u ∘ f) a = 0 := hpU
  have hTraceR : J.N ∩ {z | (u ∘ f) z = 0} ∩ V = R.N ∩ V := by
    rw [hRN]
    exact hTrace
  have haR : a ∈ R.N := by
    obtain ⟨_, _, _, _, hpO, hpL, _, _, _⟩ :=
      original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
    have haJ : a ∈ J.N := by
      change a ∈ (companionOf (n + 1) (M := B) _ L.d).N
      simp only [companionOf, companionAlong_N, geoTransformAlong_refl]
      exact L.cosupp_subset_N hpL
    exact ((Set.ext_iff.mp hTraceR a).mp ⟨⟨haJ, haU⟩, haV⟩).1
  obtain ⟨hl, hNS'⟩ := hBorn a ha
  obtain ⟨W, haW, _, hWM, hK, hKu, hN, _, hE, hSlots, hEq⟩ :=
    exists_born_selected_companion_contact (Nat.succ_pos n) J R hJ hR hClass
      (fun z hz => (hRN ▸ hz).1) a haR hl hNS' V haV (u ∘ f) hTangent hTraceR
  exact ⟨a, W, u ∘ f, ha, haW, hWM, haU, hK, hKu, hN, hE, hSlots, hEq⟩

set_option maxHeartbeats 1200000 in
/-- The pullback of the literal supported member record to the order mask has
exactly the carrier traced out by the upper strict section on the companion. -/
theorem supported_member_carrier_on_initial_order_mask {n s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (p : Y) :
    let P := properNormalMarked Q
    let Sec := sectionMarked Q
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) P (s + 1) H p
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let J := compAt L L.d (.refl : BlowupTower A A)
    let R := MarkedIdeal.pullback (M' := CMfd.of (n := n + 1) C)
      (Subtype.val : C → A) (positiveMemberOn Sec H p O)
    let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
    let f : C → Y := fun z => z.val.val
    R.N = J.N ∩ f ⁻¹' D := by
  intro P Sec O A L C J R D f
  let B := geoTransformAlong (barMarked P) H
  let B' := geoTransformAlong (barMarked Sec) H
  have hB' : B'.N = D := by
    change (geoTransformAlong (barMarked Sec) H).N = D
    rw [HomogenizedGlueingTower.N_geoTransformAlong]
    exact congrArg (strictAlong H) (normal_contact_carrier Q).symm
  have hDB : D ⊆ B.N := by
    change D ⊆ (geoTransformAlong (barMarked P) H).N
    rw [HomogenizedGlueingTower.N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono H (fun _ hy => hy.1)
  have hOrig : origMembers P H = origMembers Sec H :=
    HironakaG8MemberLoci.origMembers_eq_of_E_eq (A := P) (B := Sec) rfl H
  have hOldB : ∀ E ∈ origMembers P H, E ∈ B.E := fun _ h => List.mem_of_mem_take h
  have hOldB' : ∀ E ∈ origMembers Sec H, E ∈ B'.E := fun _ h => List.mem_of_mem_take h
  change f ⁻¹' (B'.N ∩ memberInter B'.E (membersThrough B'.E (origMembers Sec H) p)) =
    (companionOf (n + 1) (M := CMfd.of (n := n + 1) C) _ L.d).N ∩ f ⁻¹' D
  simp only [companionOf, companionAlong_N, geoTransformAlong_refl]
  change f ⁻¹' (B'.N ∩ memberInter B'.E (membersThrough B'.E (origMembers Sec H) p)) =
    f ⁻¹' (B.N ∩ memberInter B.E (membersThrough B.E (origMembers P H) p)) ∩ f ⁻¹' D
  rw [memberInter_membersThrough hOldB p, memberInter_membersThrough hOldB' p, hOrig, hB']
  ext z
  exact ⟨fun hz => ⟨⟨hDB hz.1, hz.2⟩, hz.1⟩, fun hz => ⟨hz.2, hz.1.2⟩⟩

end
end Hironaka.HironakaG1ActualLaterBornCut
