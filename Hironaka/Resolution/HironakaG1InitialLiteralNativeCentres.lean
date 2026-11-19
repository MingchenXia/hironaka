import Hironaka.Resolution.HironakaG1InitialFiniteSectionUpperRead
import Hironaka.Resolution.HironakaG1LaterPositiveCANHistory
import Hironaka.Resolution.HironakaG1SupportedStepOne

/-! # Initial maxima on the padded and literal native sources -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1InitialLiteralNativeCentres

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals
  MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalLocalClass
  HironakaActualOpenZeroSectionDifferentials HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionInitialBar HironakaActualSectionBoundaryGeometry
  HironakaActualNativeSectionOrderHistory HironakaG1InitialFiniteSectionUpperRead
  HironakaG1LaterPositiveCANHistory HironakaG1SupportedStepOne
  HironakaG1NormalCentreComparison NormalCrossings HomogenizedIdealAlong

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (hn : 0 < n) (Q : MarkedIdeal n U)
  (hQ : IsInvDomain (k + 1) Q) (hWc : IsClosed (zeroPlane U))

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "A" => nativeManifold (Y := X₀) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
local notation "P" => properNormalMarked Q
local notation "SEC" => sectionMarked Q
local notation "B" => nativePullback (Y := X₀) (Nat.le_succ n) (zeroPlane U)
  (zeroPlane_regular U) SEC
local notation "T₀" => BlowupTower.refl (X := X₀)
local notation "N₀" => BlowupTower.refl (X := A)
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P
local notation "g" => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) B
local notation "fM" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) SEC

include hQ hWc in
set_option maxHeartbeats 900000 in
/-- At the genuine initial paired cut, the positive same-level comparison
against the section reader gives the exact whole native maximum image.
Section-special points are covered by the initial comparison theorem. -/
theorem initial_literal_native_max_image
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hAnchor : ∀ p ∈ (P).cosupp, level P T₀ p = s + 1 ∧ ¬ IsSpecial P T₀ p) :
    (Subtype.val : A → X₀) '' maxLocus (g N₀)
        (MarkedIdeal.cosupp (n := n) (M := A) (geoTransformAlong (Y := A) B N₀)) =
      maxLocus (f T₀) (geoTransformAlong P T₀).cosupp := by
  have hM : IsInvDomain (k + 1) SEC :=
    section_projected_domain _ Q.N Q.E Q.ideal Q.d hQ
  have hSupport : (SEC).N ⊆ zeroPlane U := fun _ hx => ⟨mem_univ _, hx.2⟩
  have hTrans : IsTransverse (n + 1) (zeroPlane U) (SEC).E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) (SEC).E
      T₀ (zeroPlane U) hWc (zeroPlane_regular U) N₀ := .refl
  have hCan : IsCanonical SEC fM T₀ := by trivial
  have hNative := (Lift.original_same_bound_step_one_max_loci (q := k) (X := X₀) (hk := Nat.le_succ n)
    (W := zeroPlane U) (hW := zeroPlane_regular U) (T := T₀)
    (V := zeroPlane U) (hV := zeroPlane_regular U) (Q := N₀)
    (Nat.succ_pos n) hn SEC hM hSupport hTrans hMax hLift hCan).2
  have hc : (P).cosupp = (SEC).cosupp :=
    (properNormalMarked_locWPEquiv_section Q hQ).cosupp_eq_base
  let i : (P).cosupp → X₀ := Subtype.val
  have hi : range i = (P).cosupp := Subtype.range_coe
  have hRead := (initial_positive_literal_section_stratum Q hQ (s := s) i
    (fun a => ⟨a.property, hAnchor a.val a.property⟩)).2
  rw [hi] at hRead
  change _ = maxLocus (f T₀) (P).cosupp
  rw [hNative]
  change maxLocus (fM T₀) (SEC).cosupp = _
  rw [← hc]
  exact hRead.symm

include hQ hWc in
/-- This actual initial paired prefix requires no supplied order comparison
or maximum image to provide a history readback. -/
theorem initial_literal_native_prefix_read
    (hMax : IsMaximalOrderAlong (SEC).N (SEC).ideal (SEC).d)
    (hAnchor : ∀ p ∈ (P).cosupp, level P T₀ p = s + 1 ∧ ¬ IsSpecial P T₀ p) :
    PrefixRead (k := k) hn Q T₀ N₀ :=
  PrefixRead.exactMax (initial_literal_native_max_image hn Q hQ hWc hMax hAnchor)

end
end Hironaka.HironakaG1InitialLiteralNativeCentres
