import Hironaka.Resolution.HironakaG8AnalyticEventFootprints
import Hironaka.Resolution.HironakaG8CombAnalyticFootprintObstruction
import Hironaka.Resolution.HironakaG8SingularSpineOpen

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8PhysicalCombNoSpatialRank

open Hironaka.BlowupSequences BlowupTowers
  HironakaG8CofinalOccupiedAncestry HironakaG8PhysicalChartOccupiedLifts
  G3UniversePhysicalClassComparisons HironakaG8SpatialCofinalPrecedence
  HironakaG8AnalyticEventFootprints HironakaG8CombAnalyticFootprintObstruction
  HironakaG8SingularSpineOpen HironakaG8CombNativeFirstHits HironakaG8VariableCombArrangement
  HironakaG8NoncompactInitialBoundaryAtlas HironakaG8CorrectedOrderedEndpoint
  HironakaG8LabelledNativeHistory HironakaG8LabelledEmbeddedAtlas HironakaEmbeddedAnalytic

/-- A compact-covering physical comb chain with the native epochs and
smooth terminal strict transforms admits no injective spatial rank. -/
theorem no_injective_spatial_rank_of_physical_comb_chain
    {Z : CMfd.{0} 3} {P : Z → combManifold}
    {c : ℕ → CombChart (P := P)} {ι : Type*} (E : CofinalEvents c ι)
    (cmp : HasPhysicalComparisons (orderedInitialBoundaryClass (X := combManifold) comb []))
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p, E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ K : Set combManifold, IsCompact K → ∃ i, K ⊆ ((c i).U : Set combManifold))
    (hEpochs : ∀ i, InitialBoundaryChartEpochs (c i))
    (hOccurs : ∀ b, ∃ i p, E.event i p = b)
    (hSmooth : ∀ i, IsClosedSubmanifold 3 (strictTransform 3 (c i).T.proj
      ((Subtype.val : (c i).U → combManifold) ⁻¹' comb))) :
    ¬ ∃ rank : ι → ℕ, Injective rank ∧
      ∀ ⦃u v⦄, SpatialBefore E u v → rank u < rank v := by
  have hPoint : ∀ x : combManifold, ∃ i, x ∈ (c i).U := by
    intro x
    obtain ⟨i,hi⟩ := hCover {x} isCompact_singleton
    exact ⟨i,hi (mem_singleton x)⟩
  have hAnalytic := cofinalEventFootprint_analytic E cmp hMono hLift hPoint
  have hCoverage := singularSet_subset_iUnion_cofinalEventFootprint E hPoint
    analytic_comb.isClosed hSmooth
  obtain ⟨O,hO,hne,hSing⟩ := exists_singular_open_on_spine
  exact no_spatial_rank_of_analytic_spine_cover E cmp hMono hLift hCover hEpochs hOccurs
    hAnalytic O hO hne (fun z hz => hCoverage (hSing z hz))

end Hironaka.HironakaG8PhysicalCombNoSpatialRank

#print axioms Hironaka.HironakaG8PhysicalCombNoSpatialRank.no_injective_spatial_rank_of_physical_comb_chain
