/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom check

`lake test` (or `lake env lean scripts/CheckAxioms.lean`) prints the axioms of selected public endpoints and fails if
any declaration owned by a `Hironaka` module, including
private and generated declarations, depends on axioms other than `propext`,
`Classical.choice` and `Quot.sound`.
-/

open Lean Elab Command

#print axioms Hironaka.forall_isNonzeroAlongAt_univ_iff
#print axioms Hironaka.exists_principalization
#print axioms Hironaka.exists_principalization_of_isCompact
#print axioms Hironaka.exists_principalization_of_subset_isCompact
#print axioms Hironaka.exists_principalization_local
#print axioms Hironaka.exists_principalization_boundary
#print axioms Hironaka.exists_embeddedResolution
#print axioms Hironaka.exists_embeddedResolution_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_pure
#print axioms Hironaka.exists_embeddedResolution_pure_of_isCompact
#print axioms Hironaka.not_le_vanishingIdeal_univ
#print axioms Hironaka.exists_principalization_of_connected
#print axioms Hironaka.exists_principalization_boundary_of_compactSpace
#print axioms Hironaka.exists_principalization_boundary_of_subset_isCompact
#print axioms Hironaka.exists_principalization_boundary_local
#print axioms Hironaka.exists_embeddedResolution_local
#print axioms Hironaka.exists_embeddedResolution_pure_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_boundary_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_boundary
#print axioms Hironaka.exists_embeddedResolution_boundary_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_boundary_local
#print axioms Hironaka.eq_iUnion_dimensionPart
#print axioms Hironaka.isComplexAnalyticSubset_dimensionPart
#print axioms Hironaka.exists_embeddedResolution_dimensionPart_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_dimensionPart
#print axioms Hironaka.exists_embeddedResolution_dimensionPart_boundary_of_isCompact
#print axioms Hironaka.canonicalResolution
#print axioms Hironaka.exists_embeddedResolution_analytic_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_analytic
#print axioms Hironaka.exists_embeddedResolution_analytic_boundary_of_isCompact
#print axioms Hironaka.exists_embeddedResolution_analytic_boundary
#print axioms Hironaka.exists_separation
#print axioms Hironaka.isAdmissibleBlowupSequence_comp
#print axioms Hironaka.isIsomorphismOver_compl_of_isAdmissibleBlowupSequence
#print axioms Hironaka.exceptionalLocus_subset_of_isAdmissibleBlowupSequence
#print axioms Hironaka.exists_embeddedResolution_analytic_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_analytic_local
#print axioms Hironaka.exists_embeddedResolution_analytic_boundary_of_subset_isCompact
#print axioms Hironaka.exists_embeddedResolution_analytic_boundary_local
#print axioms Hironaka.exists_separation_of_subset_isCompact
#print axioms Hironaka.exists_restrict_opens
#print axioms Hironaka.Resolution.Algebraic.HironakaG1OriginalCombinedResolution.original_contract
#print axioms Hironaka.HironakaG1FiniteClosedGraphOriginalComparison.exists_closed_graph_actual_native_realization
#print axioms Hironaka.HironakaG8FinalOrderedEndpoint.exists_locally_finite_ordered_boundary_epoch_canonical
#print axioms Hironaka.HironakaG8MixedCompactLabelledAlternative.mixed_compact_task_singular_survivor_of_original_canonical
#print axioms Hironaka.HironakaG8CountableArrangementNoClock.exists_certified_countableArrangement_no_clock
#print axioms Hironaka.HironakaG8RankedNestedGlobalTest.global_test_of_finite_chart_ancestry
#print axioms Hironaka.HironakaG8FiniteSpatialRealization.realize_target_intersection_order
#print axioms Hironaka.HironakaG8ParallelStepReadback.parallel_step_readback_on_saturated_open
#print axioms Hironaka.HironakaG8IndexedDisjointSwap.swap_adjacent_at_index_with_readback
#print axioms Hironaka.HironakaG8IndexedDisjointSwap.realize_disjoint_swap_word_with_readback
#print axioms Hironaka.HironakaG8FiniteSpatialRealization.realize_target_visible_order
#print axioms Hironaka.HironakaG8RankSortedSpatialChart.exists_rank_sorted_singular_test_chart
#print axioms Hironaka.HironakaG8SelectedParallelTapeProducer.SelectedParallelPlan.exists_local_tape
#print axioms Hironaka.HironakaG8RankSortedRawChart.exists_rank_sorted_cofinal_singular_charts
#print axioms Hironaka.HironakaG8NestedVisibleReordering.nested_visible_reordering
#print axioms Hironaka.HironakaG8DiscreteOriginalSingular.discrete_original_singular_finite_or_proper_limit
#print axioms Hironaka.HironakaG8CompactConnectedSingular.compact_connected_original_singular_finite_or_proper_limit
#print axioms Hironaka.HironakaG8VisibleSwapRestriction.restrict_visible_swapped_pair
#print axioms Hironaka.HironakaG8OrderedFootprintTraces.ranked_cofinal_footprint_traces_agree
#print axioms Hironaka.HironakaG8MatchedVisibleSwap.nested_pairs_after_disjoint_swap
#print axioms Hironaka.HironakaG8CompactBaseSubmersionTest.two_line_cylinder_finite_test
#print axioms Hironaka.HironakaG8MatchedSwapFullHistory.matched_nested_swap_with_carried_suffix
#print axioms Hironaka.HironakaG8CartesianSingularPrefix.actualSourceGrowing_centreImage_eq
#print axioms Hironaka.HironakaG8SubmersionCompactConnectedTest.submersion_test_of_compact_connected_base_singular
#print axioms Hironaka.HironakaG8VisibleSwapWord.swapWord_filter
#print axioms Hironaka.HironakaG8CompressedNestedSwapWitness.exists_compressed_nested_adjacent_swap
#print axioms Hironaka.HironakaG8ReorderedComparisonRank.rank_preserved_by_reordered_comparison
#print axioms Hironaka.HironakaG8MatchedSortedGlobalTest.global_test_of_nested_rank_reorderings
#print axioms Hironaka.HironakaG8ActualCompressionAtCuts.exists_actual_compression_at_cuts
#print axioms Hironaka.HironakaG8CompressedSwapComparison.compressed_swap_of_matched_cut
#print axioms Hironaka.HironakaG8LiteralCompressedSwapComparison.literal_restricted_compressed_swap
#print axioms Hironaka.HironakaG8ReorderedSingularEndpoint.intrinsic_endpoint_of_nested_rank_reorderings
#print axioms Hironaka.HironakaG8NestedMoveReadback.visible_nested_move_readback
#print axioms Hironaka.HironakaG8IndexedSwapTraceLift.lift_indexed_occupied_word
#print axioms Hironaka.HironakaG8GeometricNestedWordLift.lift_geometric_word_to_smaller_test
#print axioms Hironaka.HironakaG8JointSpatialReordering.jointly_realize_nested_spatial_target
#print axioms Hironaka.HironakaG8PenultimateCoverDescent.isTowerIso_of_local_strict_comparisons
#print axioms Hironaka.HironakaG8SortedNestedPairDescent.sorted_nested_pair_of_occupiedFootprints_eq
#print axioms Hironaka.HironakaG8CofinalSpatialRankEndpoint.intrinsic_endpoint_of_cofinal_spatial_rank
#print axioms Hironaka.HironakaG8SpatialRankByFootprintConfinement.exists_injective_spatial_rank_iff_compact_ancestral_transversals
#print axioms Hironaka.HironakaG8CofinalWeakRankEndpoint.intrinsic_endpoint_of_cofinal_weak_spatial_rank
#print axioms Hironaka.HironakaG8CofinalWeakRankEndpoint.intrinsic_endpoint_of_cofinal_bounded_spatial_height
#print axioms Hironaka.HironakaG8CombCofinalAtlas.exists_comb_atlas_without_injective_spatial_rank
#print axioms Hironaka.HironakaG8AnalyticFootprintHeightExample.no_weak_rank_analyticSpatialBefore
#print axioms Hironaka.HironakaG8CuspSheetsNoWeakRank.exists_cusp_sheets_original_test_atlas_without_weak_rank
#print axioms Hironaka.HironakaG8SameClockCuspSheets.exists_whole_cusp_sheets_three_step_test
#print axioms Hironaka.HironakaG8RegularOverlapTestLimit.intrinsic_endpoint_of_regular_overlap_tests
#print axioms Hironaka.HironakaG8SingularCoverTestLimit.intrinsic_endpoint_of_singular_cover_tests
#print axioms Hironaka.HironakaG8ScheduledCuspNativeObstruction.scheduled_cusp_cutoff_not_native
#print axioms Hironaka.HironakaG8BoundedOpenTestEndpoint.bounded_endpoint_of_compatible_open_tests
#print axioms Hironaka.HironakaG8GrowingSingularCoverTestLimit.intrinsic_endpoint_of_singular_cover_growing_tests
#print axioms Hironaka.HironakaG8NativeHomogeneousEndpoint.intrinsic_endpoint_of_homogeneous_native_windows
#print axioms Hironaka.HironakaG8CompactOrbitReference.finite_serial_rank_of_native_compact_orbits
#print axioms Hironaka.HironakaG8NativeSlotwiseSpatialRank.exists_injective_spatial_rank_of_native_slotwise_transitivity
#print axioms Hironaka.HironakaG8FiniteEventTestEndpoint.finite_endpoint_of_finite_cofinal_events
#print axioms Hironaka.HironakaG8CofinalLocalPointRank.cofinal_rank_of_local_point_comparisons
#print axioms Hironaka.HironakaG8BoundedWeakRankEndpoint.finite_endpoint_of_uniformly_bounded_weak_spatial_rank
#print axioms Hironaka.HironakaG8ClosedSupportedGrowingExtension.exists_supported_growing_test_extension
#print axioms Hironaka.HironakaG8SupportedCompactClearance.exists_compact_clearance_in_supported_growing_test
#print axioms Hironaka.HironakaG8NativeGermComparison.localPointComparison_of_native_germ_first_footprint
#print axioms Hironaka.HironakaG8SingularStratumTestLift.growing_test_of_singular_stratum_test
#check @Hironaka.deJongAlterationTheorem
#print axioms Hironaka.deJongAlterationTheorem
#print axioms Hironaka.exists_alterationWithBoundary
#check @Hironaka.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem
#print axioms Hironaka.StableModificationBridge.AlterationUnconditional.deJongAlterationTheorem

-- Namespace OR exact module ownership also covers adopted native-namespace APIs.
run_cmd do
  let env ← getEnv
  let moduleIndices := env.const2ModIdx
  let moduleNames := env.header.moduleNames
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut hironakaCount : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (c, _) in env.constants.toList do
    let hironakaOwned := match moduleIndices[c]? with
      | some idx => (`Hironaka).isPrefixOf moduleNames[idx]!
      | none => false
    if hironakaOwned || (`Hironaka).isPrefixOf c then
      n := n + 1
      if hironakaOwned then hironakaCount := hironakaCount + 1
      for a in (← liftCoreM <| collectAxioms c) do
        unless allowed.contains a do bad := bad.push (c, a)
  if hironakaCount == 0 then
    throwError "axioms check: refusing an empty Hironaka audit"
  if bad.isEmpty then
    logInfo m!"axioms check: {n} declarations ({hironakaCount} Hironaka-owned), including private/generated, all within [propext, Classical.choice, Quot.sound]"
  else
    throwError m!"axioms check: non-standard axioms: {bad.toList.take 20}"
