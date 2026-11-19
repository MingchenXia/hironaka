import Hironaka.Resolution.HironakaG8CaseTCommonRemainder
import Hironaka.Resolution.HironakaActualBoundarySlotReindex

/-!
# Moving the selected boundary slot to the front

The SNC condition is transported through explicit slot bijections, preserving
duplicate empty slots and the full ordered remainder.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CaseTBoundaryReorder
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualBoundarySlotReindex

/-- Moving one specified member across a prefix preserves the literal SNC
condition, including all repeated empty slots. -/
theorem isSNCDivisor_move_front
    {n : ℕ} {X : CMfd.{u} n} (L R : List (Set X)) (H : Set X)
    (h : IsSNCDivisor n (L ++ [H] ++ R)) :
    IsSNCDivisor n ([H] ++ (L ++ R)) := by
  have h0 : IsSNCDivisor n (L ++ R ++ [H]) :=
    (snc_reindex_iff (boundarySlotEquiv L R H) (boundarySlotEquiv_get L R H)).mpr h
  have h1 : IsSNCDivisor n ([] ++ [H] ++ (L ++ R)) :=
    (snc_reindex_iff (boundarySlotEquiv [] (L ++ R) H)
      (boundarySlotEquiv_get [] (L ++ R) H)).mp (by simpa using h0)
  simpa using h1

/-- The chosen indexed member can be put first and all remaining slots retain
their original order. -/
theorem isSNCDivisor_get_cons_eraseIdx
    {n : ℕ} {X : CMfd.{u} n} (E : List (Set X)) (i : Fin E.length)
    (h : IsSNCDivisor n E) : IsSNCDivisor n (E.get i :: E.eraseIdx i.val) := by
  have hSplit : E.take i.val ++ [E.get i] ++ E.drop (i.val+1) = E := by
    rw [List.get_eq_getElem, List.take_append_getElem i.isLt, List.take_append_drop]
  have h1 : IsSNCDivisor n (E.take i.val ++ [E.get i] ++ E.drop (i.val+1)) := hSplit.symm ▸ h
  have h2 := isSNCDivisor_move_front (E.take i.val) (E.drop (i.val+1)) (E.get i) h1
  simpa only [List.eraseIdx_eq_take_drop_succ, List.singleton_append] using h2

end
end Hironaka.HironakaG8CaseTBoundaryReorder
