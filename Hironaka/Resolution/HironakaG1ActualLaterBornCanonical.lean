import Hironaka.Resolution.HironakaG1ActualLaterBornCut
import Hironaka.Resolution.HironakaG1BornSelectedCompanionCanonical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ActualLaterBornCanonical
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain GeneralValue NonmonomialOrderTail
  CompanionRebase CompanionReductionAlong HomogenizedIdealAlong CoefficientIdealRestriction
  TangentDirectionAlong DivisorExponentAlong HironakaG8LocalHistory
  HironakaG1ActualLaterBornCut HironakaG1ActualLaterCompanionTangent
  HironakaG1BornSelectedCompanionCanonical HironakaG1RecursiveMemberValueTransport
  HironakaG1PositiveNormalPhase HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaActualOpenZeroSectionDifferentials
  HironakaActualRelativeNormalGeometry
open HomogenizedGlueingTower (strictAlong)

private theorem initial_positive_special_of_larger_carrier {n k l : ℕ} {X : CMfd.{0} n}
    (J R : MarkedIdeal n X) (hJ : IsInvDomain k J) (hR : IsInvDomain l R)
    (hClass : LocWPEquiv J R) (hRJ : R.N ⊆ J.N) (a : X)
    (hPos : 0 < level J (.refl : BlowupTower X X) a)
    (hS : IsSpecial J (.refl : BlowupTower X X) a) :
    IsSpecial R (.refl : BlowupTower X X) a := by
  let I : BlowupTower X X := .refl
  have hOrig := HironakaG8MemberLoci.origMembers_eq_of_E_eq hClass.wEquiv.1 I
  have hLev := HironakaG8MemberLoci.level_eq_of_E_eq hClass.wEquiv.1 I a
  have hCos : (barMarked J).cosupp = (barMarked R).cosupp :=
    (cosupp_barMarked J hJ.isWellFormed hJ.one_le_d).trans
      (hClass.cosupp_eq_base.trans (cosupp_barMarked R hR.isWellFormed hR.one_le_d).symm)
  rcases hS with ⟨h0, _⟩ | ⟨hP, hMem⟩
  · exact (Nat.ne_of_gt hPos h0).elim
  · refine Or.inr ⟨hLev ▸ hP, ?_⟩
    change a ∈ MemberInterLocusAlong.memberInterLocus R.N (origMembers R I) (barMarked R).cosupp
    rw [← hOrig, ← hCos]
    exact ⟨hMem.1, hMem.2.mono fun _ hz hzR hzE => hz (hRJ hzR) hzE⟩

set_option maxHeartbeats 1500000 in
/-- The actual later order companion supplies the contact function and its
strict trace internally. On support-aligned positive anchors the supported
reference supplies the recursive domain and the coefficient gaps give the
original canonicality equivalence on the resulting common window. -/
theorem exists_actual_later_born_canonical {n k l s b : ℕ}
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
    let R := MarkedIdeal.pullback (M' := B) (Subtype.val : C → A)
      (positiveMemberOn (sectionMarked Q) H p O)
    let f : C → _ := fun z => z.val.val
    let I : BlowupTower B B := .refl
    IsInvDomain l R → LocWPEquiv J R →
    (∀ a : C, f a = p → level J I a = b + 1 ∧ ¬ IsSpecial R I a) →
    ∃ (a : C) (W : Opens B) (u : B → ℂ),
      f a = p ∧ a ∈ W ∧ W ≤ maskA J I a ∧ W ≤ maskA R I a ∧ u a = 0 ∧
      let A' := CMfd.of (n := n + 1) W
      let K := positiveMemberOn J I a W
      let R' := positiveMemberOn R I a W
      let Cut := withN (coeffMarkedAlong K) (K.N ∩ {z : W | u z.val = 0})
      IsInvDomain k K ∧
      IsTangentDirectionAlong K.N K.ideal K.d univ (u ∘ (Subtype.val : W → B)) ∧
      Cut.N = R'.N ∧ Cut.E = R'.E ∧ LocWPEquiv (X := A') Cut R' ∧
      IsInvDomain (l - 1) Cut ∧ IsInvDomain (l - 1) R' ∧
      (∀ F ∈ Cut.E, ∀ z ∈ Cut.cosupp, z ∈ F →
        R'.d * divExpAlong (n + 1) Cut.N Cut.ideal F z =
          Cut.d * divExpAlong (n + 1) R'.N R'.ideal F z) ∧
      (∀ {Z : CMfd.{0} (n + 1)} (V : BlowupTower A' Z),
        IsCanonical Cut ((invFamily (Nat.succ_pos n) (l - 1)).inv Cut) V ↔
          IsCanonical R' ((invFamily (Nat.succ_pos n) (l - 1)).inv R') V) := by
  intro X P r H S p O A L C B J R f I hR hClass hBorn
  let D := strictAlong H (P.N ∩ {z | relativeNormalCoordinate U z = 0})
  have hRN : R.N = J.N ∩ f ⁻¹' D :=
    supported_member_carrier_on_initial_order_mask (s := s) Q H p
  have hRJ : R.N ⊆ J.N := fun z hz => (hRN ▸ hz).1
  obtain ⟨hp, hq, Ω, u, haV, haU, hJ, hTangent, hTrace⟩ :=
    exists_actual_later_initial_order_companion_tangent Q hQ T hCan y hy hLevel hNS
  let V : Opens B := ⟨Ω, hTangent.isOpen⟩
  let a : C := ⟨⟨p, hp⟩, hq⟩
  have ha : f a = p := rfl
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
  obtain ⟨hl, hNSR⟩ := hBorn a ha
  have hNSJ : ¬ IsSpecial J I a := fun hS => hNSR
    (initial_positive_special_of_larger_carrier J R hJ hR hClass hRJ a (by rw [hl]; omega) hS)
  obtain ⟨W, haW, _, hWJ, hWR, hK, hKu, hN, hE, hCR, hCut, hR', hExp, hCan'⟩ :=
    exists_born_selected_contact_canonical_of_supported_nonspecial (Nat.succ_pos n)
      J R hJ hR hClass hRJ a haR hl hNSJ hNSR V haV (u ∘ f) hTangent hTraceR
  exact ⟨a, W, u ∘ f, ha, haW, hWJ, hWR, haU, hK,
    hKu, hN, hE, hCR, hCut, hR', hExp, hCan'⟩

end
end Hironaka.HironakaG1ActualLaterBornCanonical
