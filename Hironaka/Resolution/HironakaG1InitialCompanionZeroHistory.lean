import Hironaka.Resolution.HironakaG1InitialCompanionNormalTangent
import Hironaka.Resolution.HironakaG1NormalContactChoiceTransfer

/-! Zero-level histories of the literal initial positive order companion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1InitialCompanionZeroHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  CanonicalCentres HomogenizedIdealAlong InvDomainTowerAlong RelativePrincipalizationSpan
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal RestrictedIdealExtension
  HironakaG1PositiveNormalRepairCentres StepOneValue StepOneValueMasked BoundaryCount
  GeneralValue NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaG1InitialSelectedOrderPhase HironakaG1InitialCompanionNormalTangent
  HironakaG1NormalContactChoiceTransfer
open HomogenizedGlueingTower (strictAlong)

private theorem level_eq_zero_of_empty_original {n : ℕ} {X Y : CMfd.{0} n}
    (J : MarkedIdeal n X) (hE : ∀ D ∈ J.E, D = ∅)
    (T : BlowupTower X Y) (y : Y) : level J T y = 0 := by
  classical
  rw [level, origMembers_eq, boundaryCount, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro i _
  have hD : (J.E.map (strictAlong T)).get i = ∅ := by
    obtain ⟨D, hD, hEq⟩ := List.mem_map.mp (List.get_mem (J.E.map (strictAlong T)) i)
    rw [← hEq, hE D hD, StepOneEmptyPrefix.strictAlong_empty]
  rw [hD]
  exact notMem_empty y

/-- The initial selected order companion keeps its ordered empty slots.
Their strict transforms are empty at every stage, so Step One always
reads level zero, even with new exceptional members. -/
theorem initial_positive_companion_zero_history {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (p : productOpen U)
    (hLevel : level (properNormalMarked Q) (BlowupTower.refl
      (X := CMfd.of (n := n + 1) (productOpen U))) p = s + 1) :
    let P := properNormalMarked Q
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := lowerMask P (s + 1) H p
    let X := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) X :=
      lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) P (s + 1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let J : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) C) :=
      compAt (X := X) L L.d (BlowupTower.refl (X := X))
    (∀ D ∈ J.E, D = ∅) ∧
      ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) C) Y) (y : Y),
        level J T y = 0 := by
  intro P H O X L C J
  obtain ⟨hLE, _⟩ := original_initial_positive_lower_companion_eq Q hQ p hLevel
  have hJ : J.E = L.E.map ((Subtype.val : C → X) ⁻¹' ·) := by
    change (companionOf (n + 1) (M := CMfd.of (n := n + 1) C)
      (MarkedIdeal.pullback (Subtype.val : C → X) L) L.d).E = _
    unfold companionOf companionAlong
    split <;> rfl
  have hJE : ∀ D ∈ J.E, D = ∅ := by
    intro D hD
    rw [hJ] at hD
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hD
    rw [show F = ∅ from hLE F hF, preimage_empty]
  exact ⟨hJE, fun T y => level_eq_zero_of_empty_original J hJE T y⟩

set_option maxHeartbeats 700000 in
/-- A surviving nonspecial endpoint of the actual canonical companion
restriction reads its finite recursive value on the prescribed normal-contact
tail. Initial domain, maximal order, tangent and level zero are constructed. -/
theorem initial_positive_companion_zero_contact_value {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    (p : productOpen U)
    (hLevel : level (properNormalMarked Q) (BlowupTower.refl
      (X := CMfd.of (n := n + 1) (productOpen U))) p = s + 1) :
    let P := properNormalMarked Q
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := lowerMask P (s + 1) H p
    let X := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) X :=
      lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) P (s + 1) H p
    let C : Opens X := ordMask (M := X) (geoTransformAlong L (.refl (X := X))) L.d
    let J : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) C) :=
      compAt (X := X) L L.d (BlowupTower.refl (X := X))
    let u : C → ℂ := fun x => relativeNormalCoordinate U (x.val : O).val
    ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower X Y) (y : Y),
      y ∈ (geoTransformAlong L T).cosupp → IsGeoTestTower L T →
      ∃ hp : T.proj y ∈ C,
        let S := restrict C T
        let z : openPreimage T C := ⟨y, hp⟩
        IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) J) S →
        ¬ IsSpecial J S z →
        nmOrd (geoTransformAlong L T) y = L.d ∧
          ZeroContactTransfer (k := k) (Nat.succ_pos n) J u S z := by
  intro P H O X L C J u Y T y hy hTest
  obtain ⟨hTop, hJ, hMax, hTang⟩ := initial_positive_companion_normal_tangent Q hQ p hLevel
  refine ⟨?_, ?_⟩
  · rw [show C = ⊤ from hTop]
    trivial
  · intro S z hCan hNS
    let F : MarkedIdeal (n + 1) X := companionOf (n + 1) L L.d
    have hL : IsInvDomain (k + 1) L := padded_lower_isInvDomain Q hQ H trivial p hLevel
    have hFEq : F = (⟨L.N, L.E, restrictOn (n + 1) L.N L.ideal, L.d⟩ :
        MarkedIdeal (n + 1) X) := (original_initial_positive_lower_companion_eq Q hQ p hLevel).2
    have hLEq : RestrictEquiv L F := by
      rw [hFEq]
      exact ⟨rfl, rfl, rfl, restrictLe_self_restrictOn hL.isWellFormed.isCoherent,
        restrictLe_restrictOn⟩
    have hF : IsInvDomain (k + 1) F :=
      (original_initial_positive_lower_companion_recursion Q hQ p hLevel).1
    have hW := RestrictEquiv.wEquiv hLEq hL.isWellFormed.isClosedSubmanifold_N.1
      hL.isWellFormed.isCoherent hF.isWellFormed.isCoherent
    have hEq : MarkedIdeal.pullback (Subtype.val : C → X) F = J :=
      pullback_val_companionOf (Nat.succ_pos n) hL.isWellFormed hL.isNonzeroAlongAt C L.d
    have hFTest := (hW.2 T).1.mp hTest
    have hCos := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict (X := X) (𝔪 := F)
      hF.isWellFormed.isClosedSubmanifold_N hF.isWellFormed.isCoherent C T hFTest
    have hz : z ∈ (geoTransformAlong J S).cosupp := by
      rw [← hEq]
      change z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : C → X) F) (restrict C T)).cosupp
      rw [hCos, ← (hW.2 T).2 hTest]
      exact hy
    have hZero : level J S z = 0 :=
      (initial_positive_companion_zero_history Q hQ p hLevel).2 S z
    exact initial_positive_companion_normal_contact (l := k) Q hQ p hLevel hJ hMax hTang
      T y hy hTest _ hCan hz hZero hNS

end Hironaka.HironakaG1InitialCompanionZeroHistory
