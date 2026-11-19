import Hironaka.Resolution.HironakaG8StageRankCoherence
import Hironaka.Resolution.HironakaG8RankedTestCompression

/-! Gluing rank-padded original TEST charts from strict common-open comparisons. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8RankedGlobalTest
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG8RankedTestCompression
  HironakaG8RankedEmptyPadding HironakaG8StageRankCoherence
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOriginalGrowingHistory
  HironakaSharpActualCurveOverlapMaps HironakaLocallyFiniteResolutionSequence
  BlowupTowerIsomorphism HironakaSharpActualCurveChosenOverlapCocycle
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal

variable {n : ℕ} {X : CMfd.{0} n} {ι : Type}

/-- Strict comparisons of the two genuine histories on the common open,
through the larger of their two final ranks. -/
def StrictPairwiseComparisons (U : ι → Opens X) {Y : ι → CMfd.{0} n}
    (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i)) : Prop :=
  ∀ i j, ∃ e : localEndpoint (U i) (U i ⊓ U j) .refl (T i)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        localEndpoint (U j) (U i ⊓ U j) .refl (T j),
    IsTowerIso (commonOpenBase (U i) (U j) (U i ⊓ U j) inf_le_left inf_le_right)
      (localPaddedHistory (U i) (U i ⊓ U j) .refl (T i) (max (T i).length (T j).length))
      (localPaddedHistory (U j) (U i ⊓ U j) .refl (T j) (max (T i).length (T j).length)) e

/-- The physical histories are the given tails over the identity prefixes. -/
def actualEndpointHistories (U : ι → Opens X) {Y : ι → CMfd.{0} n}
    (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (hPair : StrictPairwiseComparisons U T) : ActualEndpointHistories X ι where
  openSet := U
  prefixSpace i := CMfd.of (n := n) (U i)
  finalSpace := Y
  prefixTower _ := .refl
  tail := T
  cut i j := max (T i).length (T j).length
  left_bound _i _j := le_max_left _ _
  right_bound _i _j := le_max_right _ _
  comparison i j := (hPair i j).choose
  stagewise i j := (hPair i j).choose_spec

/-- The actual rank-padded charts produce one locally finite growing sequence
whose finite prefixes test the original whole record. -/
theorem ranked_test_compressions_globalize
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (U : ι → Opens X) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    {Y : ι → CMfd.{0} n}
    {T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i)}
    {rank : ∀ i, {k // HironakaG8CofinalOccupiedAncestry.Occupied (T i) k} → ℕ}
    (d : ∀ i, RankedTestCompression (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      (T i) (rank i))
    (hPair : StrictPairwiseComparisons U (fun i => (d i).decoration.pad)) :
    let A := actualEndpointHistories U (fun i => (d i).decoration.pad) hPair
    LocallyFinite (centreImage (uniformGrowingSeq A hCover)) ∧
      ∀ k, IsGeoTestTower M ((uniformGrowingSeq A hCover).stage k).2 := by
  dsimp only
  constructor
  · exact uniform_growing_seq_locally_finite _ hCover
  · apply uniform_growing_seq_original_test _ hCover M hM.isClosedSubmanifold_N hM.isCoherent
    intro i
    change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      ((BlowupTower.refl : BlowupTower (CMfd.of (n := n) (U i)) (CMfd.of (n := n) (U i))).append
        (d i).decoration.pad)
    rw [BlowupTower.refl_append]
    simpa [actualEndpointHistories, BlowupTower.refl_append, RankedTower.through, HironakaSharpActualCurveEmptyPadding.identityEmptyTail] using
      test_ranked_through _ (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (U i)) (d i).test (d i).decoration (d i).clock

end
end Hironaka.HironakaG8RankedGlobalTest

#print axioms Hironaka.HironakaG8RankedGlobalTest.ranked_test_compressions_globalize
