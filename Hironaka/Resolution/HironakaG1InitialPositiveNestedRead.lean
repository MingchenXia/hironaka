import Hironaka.Resolution.HironakaG1InitialCompanionSpecial
import Hironaka.Resolution.HironakaG1InitialPositiveGeneralRead
import Hironaka.Resolution.HironakaG1NormalNestedOrderMap

/-!
# The nested read at a positive special point of the initial lift

The original padded finite branch reads the actual selected lower
companion. Its zero-level top is exactly the inner value prescribed by the
nested order map for the actual native top branch.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialPositiveNestedRead

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres StepOneValue StepOneValueMasked
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionStepOneHistory
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionInitialBar
  HironakaActualOpenZeroSectionDifferentials
  HironakaG1InitialCompanionSpecial HironakaG1InitialPositiveGeneralRead
  HironakaG1NormalNestedOrderMap HomogenizedIdealAlong

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
/-- At a padded-nonspecial, section-special positive point on the initial
stage, the original padded and literal native Step One reads obey the
nested formula, at the adjacent depths `q+1` and `q`. The lift and native
point are the supplied ones. -/
theorem original_initial_positive_special_nested_read {n q s : ℕ}
    {U : Opens (ComplexModel n)} (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain (q + 1) Q)
    {V : Set (productOpen U)} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
    {N : BlowupTower (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U))
      (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U)) (Nat.le_succ n) V hV)}
    {hWc : IsClosed (zeroPlane U)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (sectionMarked Q).E (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) V hVc hV N)
    (z : nativeManifold (Y := CMfd.of (n := n + 1) (productOpen U)) (Nat.le_succ n) V hV)
    (hz : z.val ∈ (properNormalMarked Q).cosupp)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) z.val = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) z.val)
    (hSpecial : IsSpecial (sectionMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) z.val)
    (δ : ValTy q → ValTy q) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let T := BlowupTower.refl (X := X)
    let B := nativePullback (Y := X) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (sectionMarked Q)
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (q + 1)) (properNormalMarked Q) T
    let g := Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) B N
    g z = toLex (s + 1, (⊤ : WithTop (ValTy q))) ∧
      f z.val = nestedStep (fun _ => (coeffMarkedAlong (barMarked (X := X) (properNormalMarked Q))).d) δ (g z) := by
  intro X T B f g
  let L := lowerMarkedM (properNormalMarked Q) (s + 1) T z.val
  let Sec := sectionMarked Q
  have hSec : IsInvDomain (q + 1) Sec := section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hChron := actual_section_step_one_chronology U Q.N hQ.isWellFormed.isClosedSubmanifold_N
    Q.E hQ.isWellFormed.isSNCDivisor Sec.ideal hSec.isWellFormed.isCoherent Q.d hLift
  have hLevelSec : level Sec T z.val = s + 1 :=
    (HironakaG8MemberLoci.level_eq_of_E_eq (show (properNormalMarked Q).E = Sec.E from rfl) T z.val).symm.trans hLevel
  have hLevelNative : level B N z = s + 1 := (hChron.2.2.1 z).1.symm.trans hLevelSec
  have hzSpecial : IsSpecial B N z := (hChron.2.2.1 z).2.mp hSpecial
  have hNative : g z = toLex (s + 1, (⊤ : WithTop (ValTy q))) :=
    (Seq.StepOneValueMasked.stepOneInvL_of_isSpecial (invFamily hn q) B (lowerMarkedM B) N hzSpecial).trans
      (congrArg (fun j => toLex (j, (⊤ : WithTop (ValTy q)))) hLevelNative)
  have hRead := original_upper_initial_positive_successor_read Q hQ T trivial z.val hz hLevel hNS rfl
  obtain ⟨_, hp, hq, _, _, _, _, _, hPadded⟩ := hRead
  let O := maskA (properNormalMarked Q) T z.val
  let A := CMfd.of (n := n + 1) O
  let F := NonmonomialOrderTail.ordMask (M := A) L L.d
  let v : F := ⟨⟨z.val, hp⟩, hq⟩
  let J := GeneralValue.compAt (X := A) L L.d (.refl : BlowupTower A A)
  let K := BlowupTower.refl (X := CMfd.of (n := n + 1) F)
  let c := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) J K v
  have hComp : c = toLex (0, (⊤ : WithTop (ValTy q))) :=
    initial_positive_companion_special_value (q := q) Q hQ z.val hz hLevel hSpecial v rfl
  change f z.val = toLex (s + 1,
    (positiveSuccessorRead L.d c : WithTop (ValTy (q + 1)))) at hPadded
  have hOrder : L.d = (coeffMarkedAlong (barMarked (X := X) (properNormalMarked Q))).d := rfl
  rw [hComp, hOrder] at hPadded
  refine ⟨hNative, ?_⟩
  simp only [hNative, nestedStep, ofLex_toLex, nestedLower_top]
  exact hPadded

end

end Hironaka.HironakaG1InitialPositiveNestedRead
