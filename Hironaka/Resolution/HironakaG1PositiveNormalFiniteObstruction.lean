import Hironaka.Resolution.HironakaG1PositiveNormalJointExample
import Hironaka.Resolution.HironakaOriginalFamilyDepthStability

/-!
# A finite Step One obstruction on the actual normal section

The comparison uses the same anchor and the same empty history. Both
Step One values are finite, but their lower nonmonomial first entries differ.
-/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalFiniteObstruction

noncomputable section

open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq CanonicalCentres StepOneValue StepOneValueMasked
  NonmonomialOrderLocal HironakaG8MixedOrderInvariance
  HironakaActualOpenZeroSectionDifferentials
  HironakaActualNativeSectionInitialBar HironakaActualNativeSectionFiniteHistory
  HironakaG1PositiveNormalJointExample HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaSmoothSubmersionCanonicalValueDimensionShift
  HironakaActualSectionBoundaryDimension HironakaOriginalFamilyDepthStability

private theorem stepOne_refl_lower {n k : ℕ} {X : CMfd.{0} n} {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariant n k Λ) (M : MarkedIdeal n X) (p : X)
    (hLevel : level M (BlowupTower.refl (X := X)) p = 1)
    (hNS : ¬ IsSpecial M (BlowupTower.refl (X := X)) p)
    (pO : lowerMask M 1 (BlowupTower.refl (X := X)) p) (hpO : pO.val = p) :
    Seq.StepOneValueMasked.stepOneInvM R M (BlowupTower.refl (X := X)) p =
      toLex (1, (↑(R.inv (lowerMarkedM M 1 (BlowupTower.refl (X := X)) p)
        (BlowupTower.refl (X := CMfd.of (n := n) (lowerMask M 1 (BlowupTower.refl (X := X)) p)))
        pO) : WithTop Λ)) := by
  classical
  let T : BlowupTower X X := .refl
  change Seq.StepOneValueMasked.stepOneInvL R M (lowerMarkedM M) T p = _
  rw [Seq.StepOneValueMasked.stepOneInvL_of_not_isSpecial R M (lowerMarkedM M) T hNS, hLevel]
  change toLex (1, Seq.StepOneValueMasked.lowerValueL R M (lowerMarkedM M) 1 T T p) = _
  have hm : p ∈ lowerMask M 1 T p := by
    have h : pO.val ∈ lowerMask M 1 T p := pO.property
    simpa only [hpO] using h
  unfold Seq.StepOneValueMasked.lowerValueL
  change toLex (1, if hm' : p ∈ lowerMask M 1 T p then
    (↑(R.inv (lowerMarkedM M 1 T p) (BlowupTower.refl (X := CMfd.of (n := n) (lowerMask M 1 T p)))
      ⟨p, hm'⟩) : WithTop Λ) else ⊤) = _
  rw [dif_pos hm]
  have he : (⟨p, hm⟩ : lowerMask M 1 T p) = pO := Subtype.ext hpO.symm
  rw [he]

private def initialStep {n : ℕ} {X : CMfd.{0} n} (hn : 0 < n) (q : ℕ)
    (M : MarkedIdeal n X) (p : X) : ℕ ×ₗ WithTop (ValTy q) :=
  Seq.StepOneValueMasked.stepOneInvM (X := X) (invFamily hn q) M .refl p

private theorem first_entry_depth {n : ℕ} {X : CMfd.{0} (n + 1)}
    (q : ℕ) (M : MarkedIdeal (n + 1) X) (x : X) :
    fstEntry (k := q) ((invFamily (Nat.succ_pos n) (q + 1)).inv M .refl x) =
      fstEntry (k := n) ((canonicalInvariant (n + 1)).inv M .refl x) := rfl

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩

set_option maxHeartbeats 250000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual finite Step One values at the shared origin disagree under
every lower comparison that preserves the nonmonomial first entry, for
any positive lower recursive depth on either record. -/
theorem joint_finite_stepOne_obstruction (a b : ℕ) :
    let P : MarkedIdeal 3 X := properNormalMarked sourceRecord
    let S : MarkedIdeal 3 X := sectionMarked sourceRecord
    let T : BlowupTower X X := .refl
    let Z := nativeManifold (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U)
    let B : MarkedIdeal 2 Z := nativePullback (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U) S
    let N : BlowupTower Z Z := .refl
    ∃ (z : Z) (hZero : IsClosed (zeroPlane U))
      (v : ValTy (a + 1)) (w : ValTy (b + 1)),
      Lift (Nat.le_succ 2) (zeroPlane U) hZero (zeroPlane_regular U) S.E T
        (zeroPlane U) hZero (zeroPlane_regular U) N ∧ z.val = p ∧
      let vp := initialStep (X := X) (by decide) (a + 1) P p
      let vn := initialStep (X := Z) (by decide) (b + 1) B z
      vp = toLex (1, (↑v : WithTop (ValTy (a + 1)))) ∧
      vn = toLex (1, (↑w : WithTop (ValTy (b + 1)))) ∧
      fstEntry (k := a) v = 1 ∧ fstEntry (k := b) w = 2 ∧
      ∀ f : ValTy (b + 1) → ValTy (a + 1),
        (∀ x, fstEntry (k := a) (f x) = fstEntry (k := b) x) → stepDimensionMap f vn ≠ vp := by
  intro P S T Z B N
  obtain ⟨z, hZero, pO, zO, hLift, hz, hpO, hzO, _, _, hpLevel, hzLevel, hpNS, _, hzNS, hP, hB⟩ :=
    joint_positive_nonspecial_first_entries
  let RP := invFamily (by decide : 0 < 3) (a + 1)
  let RN := invFamily (by decide : 0 < 2) (b + 1)
  let TP : BlowupTower (CMfd.of (n := 3) (lowerMask P 1 T p)) _ := .refl
  let TN : BlowupTower (CMfd.of (n := 2) (lowerMask B 1 N z)) _ := .refl
  let v := RP.inv (lowerMarkedM P 1 T p) TP pO
  let w := RN.inv (lowerMarkedM B 1 N z) TN zO
  have hV : fstEntry (k := a) v = 1 :=
    (first_entry_depth (X := CMfd.of (n := 3) (lowerMask P 1 T p)) a
      (lowerMarkedM P 1 T p) pO).trans hP
  have hW : fstEntry (k := b) w = 2 :=
    (first_entry_depth (X := CMfd.of (n := 2) (lowerMask B 1 N z)) b
      (lowerMarkedM B 1 N z) zO).trans hB
  have hVP := stepOne_refl_lower RP P p hpLevel hpNS pO hpO
  have hVN := stepOne_refl_lower RN B z hzLevel hzNS zO hzO
  refine ⟨z, hZero, v, w, hLift, hz, hVP, hVN, hV, hW, ?_⟩
  intro f hf hEq
  change stepDimensionMap f (Seq.StepOneValueMasked.stepOneInvM RN B N z) =
    Seq.StepOneValueMasked.stepOneInvM RP P T p at hEq
  rw [hVN, hVP] at hEq
  have hCoe : (↑(f w) : WithTop (ValTy (a + 1))) = ↑v :=
    congrArg (fun x : ℕ ×ₗ WithTop (ValTy (a + 1)) => (ofLex x).2) hEq
  exact ((by decide) : (2 : ℕ) ≠ 1) ((hW.symm.trans (hf w).symm).trans
    ((congrArg (fstEntry (k := a)) (WithTop.coe_injective hCoe)).trans hV))

/-- The dimension shift at fixed positive recursive depth preserves the lower
nonmonomial first entry. -/
theorem sameIndexMap_fstEntry (t q : ℕ) (v : ValTy (q + 1)) :
    fstEntry (sameIndexMap t (q + 1) v) = fstEntry v := rfl

/-- Enlarging a positive recursive depth preserves the lower nonmonomial
first entry. -/
theorem depthPadMap_fstEntry (t q : ℕ) (v : ValTy (q + 1)) :
    fstEntry (k := t + q) (depthPadMap t (q + 1) v) = fstEntry v := rfl

/-- The dimension shift with its depth increment preserves the lower
nonmonomial first entry. -/
theorem familyDimensionMap_fstEntry (t q : ℕ) (v : ValTy (q + 1)) :
    fstEntry (k := t + q) (familyDimensionMap t (q + 1) v) = fstEntry v := rfl

set_option maxHeartbeats 250000 in
set_option backward.isDefEq.respectTransparency false in
/-- At the same lifted origin, the ordinary dimension shift and pure depth
padding both fail to identify the actual finite Step One values. -/
theorem joint_finite_stepOne_dimension_depth_obstruction (t b : ℕ) :
    let P : MarkedIdeal 3 X := properNormalMarked sourceRecord
    let S : MarkedIdeal 3 X := sectionMarked sourceRecord
    let T : BlowupTower X X := .refl
    let Z := nativeManifold (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U)
    let B : MarkedIdeal 2 Z := nativePullback (Y := X) (Nat.le_succ 2) (zeroPlane U) (zeroPlane_regular U) S
    let N : BlowupTower Z Z := .refl
    ∃ (z : Z) (hZero : IsClosed (zeroPlane U)),
      Lift (Nat.le_succ 2) (zeroPlane U) hZero (zeroPlane_regular U) S.E T
        (zeroPlane U) hZero (zeroPlane_regular U) N ∧ z.val = p ∧
      let vp := initialStep (X := X) (by decide) (t + (b + 1)) P p
      let vn := initialStep (X := Z) (by decide) (b + 1) B z
      (ofLex vp).2 ≠ ⊤ ∧ (ofLex vn).2 ≠ ⊤ ∧
      stepDimensionMap (familyDimensionMap t (b + 1)) vn ≠ vp ∧
      stepDimensionMap (depthPadMap t (b + 1)) vn ≠ vp ∧
      stepDimensionMap (depthPadMap t (b + 1) ∘ sameIndexMap t (b + 1)) vn ≠ vp := by
  intro P S T Z B N
  obtain ⟨z, hZero, v, w, hLift, hz, hVP, hVN, _, _, hNo⟩ :=
    joint_finite_stepOne_obstruction (t + b) b
  refine ⟨z, hZero, hLift, hz, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => WithTop.coe_ne_top ((congrArg (fun u => (ofLex u).2) hVP).symm.trans h)
  · exact fun h => WithTop.coe_ne_top ((congrArg (fun u => (ofLex u).2) hVN).symm.trans h)
  · exact hNo _ (familyDimensionMap_fstEntry t b)
  · exact hNo _ (depthPadMap_fstEntry t b)
  · exact hNo _ (fun x => (depthPadMap_fstEntry t b _).trans (sameIndexMap_fstEntry t b x))

end
end Hironaka.HironakaG1PositiveNormalFiniteObstruction
