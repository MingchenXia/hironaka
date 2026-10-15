/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalMemberFutureShift
import Hironaka.Resolution.HironakaOriginalStepOneEmptyInsertion
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalPositiveMemberEmptyInsertion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms StepOneValue InvDomainMemberRestriction InvDomainRebase
  MonomialInvariantEmptyMember HironakaOriginalMemberFutureShift HironakaOriginalStepOneEmptyInsertion
variable {n : ℕ} {X Y : CMfd.{u} n}


theorem filter_insertIdx_of_kept {α : Type*} (P : α → Bool) (a : α) (ha : P a = true) :
    ∀ (l : List α) (j : ℕ), j ≤ l.length →
      (l.insertIdx j a).filter P = (l.filter P).insertIdx ((l.take j).filter P).length a
  | [],j,hj => by
      have he : j = 0 := by simpa using hj
      subst j
      simp [ha]
  | b::l,0,_ => by simp [ha]
  | b::l,j+1,hj => by
      have h : j ≤ l.length := by simp only [List.length_cons] at hj;omega
      cases hb : P b <;>
        simp [List.insertIdx_succ_cons,hb,filter_insertIdx_of_kept P a ha l j h]

open Classical in
def memberInsertionIndex (J : MarkedIdeal n Y) (E₀ : List (Set Y)) (p : Y) (j : ℕ) : ℕ :=
  ((J.E.take j).filter fun W => decide ¬(W ∈ E₀ ∧ p ∈ W)).length

private theorem marked_eq_of_fields (A B : MarkedIdeal n Y)
    (hN : A.N = B.N) (hE : A.E = B.E) (hI : A.ideal = B.ideal) (hd : A.d = B.d) : A = B := by
  cases A
  cases B
  simp_all

theorem memberRestrict_insertEmpty (J : MarkedIdeal n Y) (E₀ : List (Set Y)) (p : Y)
    {j : ℕ} (hj : j ≤ J.E.length) (hj₀ : j ≤ E₀.length) :
    memberRestrict (insertEmpty j J)
      (membersThrough (insertEmpty j J).E (E₀.insertIdx j ∅) p) =
    insertEmpty (memberInsertionIndex J E₀ p j)
      (memberRestrict J (membersThrough J.E E₀ p)) := by
  classical
  let P : Set Y → Bool := fun W => decide ¬(W ∈ E₀ ∧ p ∈ W)
  have hP : (fun W : Set Y => decide ¬(W ∈ E₀.insertIdx j ∅ ∧ p ∈ W)) = P := by
    funext W
    by_cases he : W = ∅ <;> simp [P,he,List.mem_insertIdx hj₀]
  have hE : (memberRestrict (insertEmpty j J)
      (membersThrough (insertEmpty j J).E (E₀.insertIdx j ∅) p)).E =
      ((memberRestrict J (membersThrough J.E E₀ p)).E).insertIdx
        (memberInsertionIndex J E₀ p j) ∅ := by
    rw [memberRestrict_membersThrough_E,memberRestrict_membersThrough_E]
    change (J.E.insertIdx j ∅).filter _ = (J.E.filter P).insertIdx _ ∅
    rw [hP]
    exact filter_insertIdx_of_kept P ∅ (by simp [P]) J.E j hj
  have hthrough : ∀ w : Y,
      (∀ W ∈ J.E.insertIdx j ∅, W ∈ E₀.insertIdx j ∅ → p ∈ W → w ∈ W) ↔
      (∀ W ∈ J.E, W ∈ E₀ → p ∈ W → w ∈ W) := by
    intro w
    constructor
    · intro h W hW hW₀ hp
      exact h W ((List.mem_insertIdx hj).mpr (Or.inr hW))
        ((List.mem_insertIdx hj₀).mpr (Or.inr hW₀)) hp
    · intro h W hW hW₀ hp
      rcases (List.mem_insertIdx hj).mp hW with rfl | hW
      · exact False.elim (Set.notMem_empty p hp)
      rcases (List.mem_insertIdx hj₀).mp hW₀ with rfl | hW₀
      · exact False.elim (Set.notMem_empty p hp)
      exact h W hW hW₀ hp
  have hN : (memberRestrict (insertEmpty j J)
      (membersThrough (insertEmpty j J).E (E₀.insertIdx j ∅) p)).N =
      (memberRestrict J (membersThrough J.E E₀ p)).N := by
    rw [memberRestrict_membersThrough_N,memberRestrict_membersThrough_N]
    ext w
    exact and_congr Iff.rfl (hthrough w)
  exact marked_eq_of_fields _ _ hN hE rfl rfl


def actualLowerInsertionIndex (m : MarkedIdeal n X) (H : BlowupTower X Y) (p : Y) (j : ℕ) : ℕ :=
  memberInsertionIndex (geoTransformAlong (barMarked m) H) (origMembers m H) p j

theorem actualLowerInsertionIndex_le_retainedOriginalCount (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) {j : ℕ} (hj : j ≤ m.E.length) :
    actualLowerInsertionIndex m H p j ≤ retainedOriginalCount m H p := by
  classical
  let E := (geoTransformAlong (barMarked m) H).E
  let E₀ := origMembers m H
  have htake : E.take j = E₀.take j := by
    dsimp only [E₀,origMembers]
    rw [List.take_take]
    congr 1
    omega
  have hfilter : (E₀.take j).filter (fun W => decide ¬(W ∈ E₀ ∧ p ∈ W)) =
      (E₀.take j).filter (fun W => decide (p ∉ W)) := by
    apply List.filter_congr
    intro W hW
    have hw₀ : W ∈ E₀ := List.mem_of_mem_take hW
    simp only [hw₀,true_and]
  change ((E.take j).filter (fun W => decide ¬(W ∈ E₀ ∧ p ∈ W))).length ≤
    (E₀.filter (fun W => decide (p ∉ W))).length
  rw [htake,hfilter]
  exact ((List.take_sublist j E₀).filter (fun W => decide (p ∉ W))).length_le

private theorem pullback_insertEmpty_heq_of_equal_masks (J : MarkedIdeal n Y)
    (j : ℕ) (U V : Opens Y) (hUV : U = V) :
    HEq (MarkedIdeal.pullback (Subtype.val : U → Y) (insertEmpty j J))
      (insertEmpty j (MarkedIdeal.pullback (Subtype.val : V → Y) J)) := by
  subst V
  apply heq_of_eq
  change MarkedIdeal.mk _ ((J.E.insertIdx j ∅).map ((Subtype.val : U → Y) ⁻¹' ·)) _ _ =
    MarkedIdeal.mk _ ((J.E.map ((Subtype.val : U → Y) ⁻¹' ·)).insertIdx j ∅) _ _
  rw [List.map_insertIdx,Set.preimage_empty]
  rfl

theorem lowerMarked_succ_insertEmpty_heq (m : MarkedIdeal n X) {j : ℕ}
    (hj : j ≤ m.E.length) (H : BlowupTower X Y) (p : Y) (s : ℕ) :
    HEq (lowerMarked (insertEmpty j m) (s+1) H p)
      (insertEmpty (actualLowerInsertionIndex m H p j) (lowerMarked m (s+1) H p)) := by
  let J := geoTransformAlong (barMarked m) H
  let E₀ := origMembers m H
  let c := actualLowerInsertionIndex m H p j
  have hjJ : j ≤ J.E.length := le_length_E_geoTransformAlong (barMarked m) hj H
  have hj₀ : j ≤ E₀.length := by
    change j ≤ (origMembers m H).length
    rw [origMembers_eq,List.length_map]
    exact hj
  have hraw : memberRestrict (geoTransformAlong (barMarked (insertEmpty j m)) H)
      (membersThrough (geoTransformAlong (barMarked (insertEmpty j m)) H).E
        (origMembers (insertEmpty j m) H) p) =
      insertEmpty c (memberRestrict J (membersThrough J.E E₀ p)) := by
    rw [bar_geoTransformAlong_insertEmpty m hj H,origMembers_insertEmpty m j H]
    exact memberRestrict_insertEmpty J E₀ p hjJ hj₀
  unfold lowerMarked
  rw [hraw]
  exact pullback_insertEmpty_heq_of_equal_masks _ c _ _ (maskA_insertEmpty m hj H p)

theorem actualLowerInsertionIndex_le_lowerBoundary (m : MarkedIdeal n X)
    (H : BlowupTower X Y) (p : Y) (s : ℕ) {j : ℕ} (hj : j ≤ m.E.length) :
    actualLowerInsertionIndex m H p j ≤ (lowerMarked m (s+1) H p).E.length := by
  have hc := actualLowerInsertionIndex_le_retainedOriginalCount m H p hj
  have hl := (original_lower_tail_empty_prefix m H p s (BlowupTower.refl)).1
  exact hc.trans hl

end
end Hironaka.HironakaOriginalPositiveMemberEmptyInsertion
