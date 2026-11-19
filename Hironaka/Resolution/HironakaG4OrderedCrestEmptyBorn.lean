import Hironaka.Resolution.HironakaG4OrderedDefectStamp
import Hironaka.Resolution.HironakaG4JointProfileEmptyBorn

/-! The ordered retained defect data ignores genuinely empty born slots. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4OrderedCrestEmptyBorn

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.HolomorphicIdealSheaves BlowupTowers MonomialPartAlong MonomialInvariantEmptyMember
  HironakaG4PreparedCentreCoordinates HironakaActualRetainedBoundaryJointStep
  HironakaSharpActualChronologicalDistinctDefect HironakaG4OrderedDefectStamp
  HironakaG4JointProfileEmptyBorn HironakaOriginalBoundaryEmptyFilterComparison
  HironakaOriginalCrossingValueTransport

variable {n : ℕ} {X : CMfd.{u} n}

/-- Filtering the genuinely empty born slots does not alter any original
old residual row. The old list and its index remain literal. -/
theorem oldResidualPart_filter_empty_born (N : Set X) (old born : List (Set X)) :
    oldResidualPart N old (born.filter fun H => decide H.Nonempty) =
      oldResidualPart N old born := by
  apply filter_value_of_empty_insertion (fun B => oldResidualPart N old B) _ born
  intro B j hj
  funext i
  unfold oldResidualPart nonmonomialPartAlong
  rw [monomialPartAlong_insertIdx_empty _ _ _ hj]

/-- The corresponding tuple of actual monomial factors is unchanged. -/
theorem oldMonomialPart_filter_empty_born (N : Set X) (old born : List (Set X)) :
    oldMonomialPart N old (born.filter fun H => decide H.Nonempty) =
      oldMonomialPart N old born := by
  apply filter_value_of_empty_insertion (fun B => oldMonomialPart N old B) _ born
  intro B j hj
  funext i
  exact monomialPartAlong_insertIdx_empty N _ B hj

/-- The exact row-order tuple and inactive nonunit mask survive this
normalization of the born boundary. -/
theorem retainedDefectStamp_filter_empty_born (N : Set X) (old born : List (Set X)) (x : X) :
    retainedDefectStamp N old (born.filter fun H => decide H.Nonempty) x =
      retainedDefectStamp N old born x := by
  unfold retainedDefectStamp
  rw [oldResidualPart_filter_empty_born]
  dsimp only
  unfold inactiveCanonicalRows
  rw [oldMonomialPart_filter_empty_born]

/-- Both the true defect and the refined rank are unchanged by removing
empty born slots. -/
theorem retainedDefect_and_rank_filter_empty_born (N : Set X) (old born : List (Set X)) :
    let B := born.filter fun H => decide H.Nonempty
    actualFamilyDistinctDefect N (oldResidualPart N old B) =
      actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
    retainedDefectOrderedRank N old B = retainedDefectOrderedRank N old born := by
  dsimp only
  refine ⟨?_,?_⟩
  · rw [oldResidualPart_filter_empty_born]
  · funext x
    unfold retainedDefectOrderedRank
    rw [retainedDefectStamp_filter_empty_born]

/-- Once the nonempty born lists agree, equal refined ranks give exactly
the same normalized canonical marked record. -/
theorem normalized_jointProfileMarked_eq_of_orderedRank_eq (N : Set X)
    (old born₁ born₂ : List (Set X)) (x y : X)
    (hB : (born₁.filter fun H => decide H.Nonempty) = born₂.filter (fun H => decide H.Nonempty))
    (hRank : retainedDefectOrderedRank N old born₁ x = retainedDefectOrderedRank N old born₂ y) :
    let S := retainedDefectStamp N old born₁ x
    let R := retainedDefectStamp N old born₂ y
    nonemptyBoundary (jointProfileMarked N old born₁ (∑ i, S.1 i) S.2) =
      nonemptyBoundary (jointProfileMarked N old born₂ (∑ i, R.1 i) R.2) := by
  dsimp only
  rw [← jointProfileMarked_filter_empty_born N old born₁,
    ← jointProfileMarked_filter_empty_born N old born₂, hB]
  have hRank₁ := congrFun (retainedDefect_and_rank_filter_empty_born N old born₁).2 x
  have hRank₂ := congrFun (retainedDefect_and_rank_filter_empty_born N old born₂).2 y
  rw [hB] at hRank₁
  have hRank' := hRank₁.trans (hRank.trans hRank₂.symm)
  have hStamp := retainedDefectStamp_eq_of_orderedRank_eq N old
    (born₂.filter fun H => decide H.Nonempty) hRank'
  have hStamp₁ := retainedDefectStamp_filter_empty_born N old born₁ x
  rw [hB] at hStamp₁
  rw [hStamp₁.symm, hStamp, retainedDefectStamp_filter_empty_born]

end
end Hironaka.HironakaG4OrderedCrestEmptyBorn
