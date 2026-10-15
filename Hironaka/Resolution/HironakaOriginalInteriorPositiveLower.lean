/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalInteriorEmptyHistory
/-! Actual positive lower records of the original interior empty history.
The complete mathematics was written before proof in
`hironaka-original-interior-positive-lower-extension.tex`.
Zero contact carriers and full higher recursive history comparison remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalInteriorPositiveLower
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms MonomialInvariantEmptyMember
  MarkedIdealBiholomorphism InvDomainMemberRestriction InvDomainRebase StepOneValue
  StepOneValueMasked StepOneLowerDomain HironakaOriginalPositiveMemberEmptyInsertion
  HironakaOriginalInteriorEmptyHistory
variable {n : ℕ} {X A Y : CMfd.{u} n}

/-- A future empty member is kept by the actual member filter; the original
member list is literally UNCHANGED, with no bound inside that original prefix. -/
theorem future_memberRestrict_insertEmpty (J : MarkedIdeal n Y)
    (E₀ : List (Set Y)) (p : Y) {j : ℕ} (hj : j ≤ J.E.length) :
    memberRestrict (insertEmpty j J) (membersThrough (insertEmpty j J).E E₀ p) =
      insertEmpty (memberInsertionIndex J E₀ p j) (memberRestrict J (membersThrough J.E E₀ p)) := by
  classical
  let P : Set Y → Bool := fun W => decide ¬(W ∈ E₀ ∧ p ∈ W)
  have hE : (memberRestrict (insertEmpty j J) (membersThrough (insertEmpty j J).E E₀ p)).E =
      ((memberRestrict J (membersThrough J.E E₀ p)).E).insertIdx
        (memberInsertionIndex J E₀ p j) ∅ := by
    rw [memberRestrict_membersThrough_E,memberRestrict_membersThrough_E]
    exact filter_insertIdx_of_kept P ∅ (by simp [P]) J.E j hj
  have hthrough : ∀ w : Y,
      (∀ W ∈ J.E.insertIdx j ∅, W ∈ E₀ → p ∈ W → w ∈ W) ↔
      (∀ W ∈ J.E, W ∈ E₀ → p ∈ W → w ∈ W) := by
    intro w
    constructor
    · intro h W hW hW₀ hp
      exact h W ((List.mem_insertIdx hj).mpr (Or.inr hW)) hW₀ hp
    · intro h W hW hW₀ hp
      rcases (List.mem_insertIdx hj).mp hW with rfl | hW
      · exact False.elim (Set.notMem_empty p hp)
      · exact h W hW hW₀ hp
  have hN : (memberRestrict (insertEmpty j J) (membersThrough (insertEmpty j J).E E₀ p)).N =
      (memberRestrict J (membersThrough J.E E₀ p)).N := by
    rw [memberRestrict_membersThrough_N,memberRestrict_membersThrough_N]
    ext w
    exact and_congr Iff.rfl (hthrough w)
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE rfl rfl

/-- The insertion position after the true member restriction, computed from
the actual whole boundary prefix of the SAME original history. -/
def interiorPositiveLowerIndex (M : MarkedIdeal n X)
    (H : BlowupTower X A) (S : BlowupTower A Y) (p : Y) : ℕ :=
  memberInsertionIndex (geoTransformAlong (barMarked M) (H.append S))
    (origMembers M (H.append S)) p (M.E.length + H.length)

theorem interiorPositiveLowerIndex_le_boundary (M : MarkedIdeal n X)
    (H : BlowupTower X A) (S : BlowupTower A Y) (p : Y) (s : ℕ) :
    interiorPositiveLowerIndex M H S p ≤ (lowerMarkedM M (s+1) (H.append S) p).E.length := by
  classical
  let J := geoTransformAlong (barMarked M) (H.append S)
  let E₀ := origMembers M (H.append S)
  let P : Set Y → Bool := fun W => decide ¬(W ∈ E₀ ∧ p ∈ W)
  change ((J.E.take (M.E.length + H.length)).filter P).length ≤
    ((memberRestrict J (membersThrough J.E E₀ p)).E.map
      ((Subtype.val : maskA M (H.append S) p → Y) ⁻¹' ·)).length
  rw [List.length_map,memberRestrict_membersThrough_E]
  exact ((List.take_sublist (M.E.length + H.length) J.E).filter P).length_le

private theorem pullback_future_insertEmpty_heq (J : MarkedIdeal n Y)
    (j : ℕ) (U V : Opens Y) (hUV : U=V) :
    HEq (MarkedIdeal.pullback (Subtype.val : U → Y) (insertEmpty j J))
      (insertEmpty j (MarkedIdeal.pullback (Subtype.val : V → Y) J)) := by
  subst V
  apply heq_of_eq
  change MarkedIdeal.mk _ ((J.E.insertIdx j ∅).map ((Subtype.val : U → Y) ⁻¹' ·)) _ _ =
    MarkedIdeal.mk _ ((J.E.map ((Subtype.val : U → Y) ⁻¹' ·)).insertIdx j ∅) _ _
  rw [List.map_insertIdx,Set.preimage_empty]
  rfl

/-- Actual original masked lower record after an interior empty step, at every
positive level. No lower-value equality or lower-history comparison is assumed. -/
theorem original_positive_lower_record (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (H : BlowupTower X A) (hH : IsGeoTestTower (barMarked M) H)
    (S : BlowupTower A Y) (hS : 0 < S.length) (p : Y) (s : ℕ) :
    HEq (lowerMarkedM M (s+1) (interiorEmptyHistory H S) p)
      (insertEmpty (interiorPositiveLowerIndex M H S p) (lowerMarkedM M (s+1) (H.append S) p)) := by
  let J := geoTransformAlong (barMarked M) (H.append S)
  let E₀ := origMembers M (H.append S)
  let c := interiorPositiveLowerIndex M H S p
  have hj : M.E.length + H.length ≤ J.E.length := by
    rw [length_E_geoTransformAlong,BlowupTower.length_append]
    change M.E.length + H.length ≤ M.E.length + (H.length + S.length)
    omega
  have hraw : memberRestrict (geoTransformAlong (barMarked M) (interiorEmptyHistory H S))
      (membersThrough (geoTransformAlong (barMarked M) (interiorEmptyHistory H S)).E
        (origMembers M (interiorEmptyHistory H S)) p) =
      insertEmpty c (memberRestrict J (membersThrough J.E E₀ p)) := by
    rw [whole_record_of_nonempty_tail (barMarked M) (isWellFormed_barMarked M hM) H hH S hS,
      original_members_dictionary M hM H hH S]
    exact future_memberRestrict_insertEmpty J E₀ p hj
  change HEq (lowerMarked M (s+1) (interiorEmptyHistory H S) p)
    (insertEmpty c (lowerMarked M (s+1) (H.append S) p))
  unfold lowerMarked
  rw [hraw]
  exact pullback_future_insertEmpty_heq _ c _ _ (maskA_dictionary M hM H hH S p)

end
end Hironaka.HironakaOriginalInteriorPositiveLower
