import Hironaka.Resolution.HironakaG1InitialPositiveSpecialRecoding
import Hironaka.Resolution.HironakaG1InitialSelectedOrderPhase
import Hironaka.Resolution.HironakaG1OriginalStepSkeleton

/-! The actual initial companion reads the section's special branch. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialCompanionSpecial

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealEquivalence.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong.MarkedIdeal
  ResolutionInvariantSpec HomogenizedIdealAlong InvDomainMemberRestriction InvDomainRebase
  StepOneValue StepOneValueMasked StepOneRestrictOpen
  GeneralValue NonmonomialOrderTail CompanionRebase RestrictedIdealExtension
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaG1ProperCarrierNormalContact HironakaG1PositiveNormalRepairCentres
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaG1InitialPositiveSpecialRecoding HironakaG1InitialSelectedOrderPhase
  HironakaG1OriginalStepSkeleton CanonicalCentres

set_option maxHeartbeats 1400000 in
/-- The literal initial order companion of the positive selected padded
record has level zero. Its special branch occurs exactly at the original
section-special anchor. -/
theorem initial_positive_companion_special_iff {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : p ∈ (properNormalMarked Q).cosupp)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) p = s + 1) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let H := BlowupTower.refl (X := X)
    let O := maskA P H p
    let Y := CMfd.of (n := n + 1) O
    let L := lowerMarkedM (X := X) P (s + 1) H p
    let F := ordMask (M := Y) L L.d
    let J := compAt (X := Y) L L.d (.refl : BlowupTower Y Y)
    let K := BlowupTower.refl (X := CMfd.of (n := n + 1) F)
    ∀ z : F, (z.val : O).val = p → level J K z = 0 ∧
      (IsSpecial J K z ↔ IsSpecial (sectionMarked Q) H p) := by
  intro X P H O Y L F J K z hz
  let T := BlowupTower.refl (X := Y)
  let C : MarkedIdeal (n + 1) Y := companionOf (n + 1) L L.d
  have hL : IsInvDomain k L := padded_lower_isInvDomain Q hQ H trivial p hLevel
  obtain ⟨hC, _, _⟩ := original_initial_positive_lower_companion_recursion Q hQ p hLevel
  obtain ⟨_, hComp⟩ := original_initial_positive_lower_companion_eq Q hQ p hLevel
  have hCEq : C = (⟨L.N, L.E, restrictOn (n + 1) L.N L.ideal, L.d⟩ :
      MarkedIdeal (n + 1) Y) := hComp
  have hEq : RestrictEquiv L C := by
    rw [hCEq]
    exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hL.isWellFormed.isCoherent, restrictLe_restrictOn⟩
  have hW := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hEq
    hL.isWellFormed.isClosedSubmanifold_N.1
    hL.isWellFormed.isCoherent hC.isWellFormed.isCoherent
  obtain ⟨hLevelC, hSpecialC, _⟩ := original_step_skeleton_of_wEquiv (Nat.succ_pos n)
    L C hL hC hEq.N_eq hW T trivial z.val
  have hJ : MarkedIdeal.pullback (Subtype.val : F → Y) C = J :=
    pullback_val_companionOf (Nat.succ_pos n) hL.isWellFormed hL.isNonzeroAlongAt F L.d
  have hOpen := (restrict_facts C F hC.isWellFormed hC.one_le_d T trivial).2.2 z
  have hLevelOpen : level J K z = level C T z.val := hJ ▸ hOpen.1
  have hSpecialOpen : IsSpecial J K z ↔ IsSpecial C T z.val := hJ ▸ hOpen.2.1
  obtain ⟨hZero, hSpecial⟩ := original_initial_masked_positive_special_iff Q hQ p hp hLevel z.val hz
  exact ⟨hLevelOpen.trans (hLevelC.symm.trans hZero),
    hSpecialOpen.trans (hSpecialC.symm.trans hSpecial)⟩

set_option maxHeartbeats 1400000 in
/-- At a section-special anchor, the actual initial companion reads the
zero-level top pair for every lower recursive depth. -/
theorem initial_positive_companion_special_value {n k q s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : p ∈ (properNormalMarked Q).cosupp)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) p = s + 1)
    (hSpecial : IsSpecial (sectionMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) p) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let H := BlowupTower.refl (X := X)
    let O := maskA P H p
    let Y := CMfd.of (n := n + 1) O
    let L := lowerMarkedM (X := X) P (s + 1) H p
    let F := ordMask (M := Y) L L.d
    let J := compAt (X := Y) L L.d (.refl : BlowupTower Y Y)
    let K := BlowupTower.refl (X := CMfd.of (n := n + 1) F)
    ∀ z : F, (z.val : O).val = p →
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J K z =
        toLex (0, (⊤ : WithTop (ValTy q))) := by
  intro X P H O Y L F J K z hz
  obtain ⟨hZero, hSpecialJ⟩ :=
    initial_positive_companion_special_iff Q hQ p hp hLevel z hz
  have hAt := Seq.StepOneValueMasked.stepOneInvL_of_isSpecial
    (invFamily (Nat.succ_pos n) q) J (lowerMarkedM J) K (hSpecialJ.mpr hSpecial)
  exact hAt.trans (congrArg (fun level => toLex (level, (⊤ : WithTop (ValTy q)))) hZero)

end Hironaka.HironakaG1InitialCompanionSpecial
