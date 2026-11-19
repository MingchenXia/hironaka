import Hironaka.Resolution.HironakaG8OccupiedSlotComparison

/-! Exact raw occupied lifts on a scheduled three-step sheet. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ThreeSheetLiftReadback

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison

variable {n : ℕ} {X Y Z : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- An actual three-slot local restriction reads the assigned raw schedule
on the containing tower under any genuine empty-aware comparison. -/
theorem occupiedLift_three_sheet_slots
    (U : Opens X) (R : BlowupTower X Z)
    {T : BlowupTower (CMfd.of (n := n) U) Y}
    {e : Y ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (openPreimage R U)}
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) U) ∞)
      T (restrict U R) e)
    (p q r : {k // Occupied T k}) (hpq : p.val < q.val) (hqr : q.val < r.val)
    (s m : ℕ) (hs : s ≤ m)
    (hOnly : ∀ k, (slotFootprint (restrict U R) k).Nonempty → k = s ∨ k = s+1 ∨ k = m+2) :
    (occupiedLiftOnOpen U R h p).val = s ∧
      (occupiedLiftOnOpen U R h q).val = s+1 ∧
      (occupiedLiftOnOpen U R h r).val = m+2 := by
  let f := occupiedLiftOnOpen U R h
  have hA := f.strictMono hpq
  have hB := f.strictMono hqr
  have hSlot (x : {k // Occupied T k}) :
      (f x).val = s ∨ (f x).val = s+1 ∨ (f x).val = m+2 :=
    hOnly _ ((slotFootprint_nonempty_iff (restrict U R) _).mpr (occupiedComparison h x).property)
  change (f p).val < (f q).val at hA
  change (f q).val < (f r).val at hB
  change (f p).val = s ∧ (f q).val = s+1 ∧ (f r).val = m+2
  rcases hSlot p with hp | hp | hp <;>
    rcases hSlot q with hq | hq | hq <;>
    rcases hSlot r with hr | hr | hr <;> omega

end Hironaka.HironakaG8ThreeSheetLiftReadback
