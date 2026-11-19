import Hironaka.Resolution.HironakaG8ComparablePackedRounds

/-! Global intrinsic resolution from a finishing cofinal TEST atlas of bounded spatial height. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CofinalWeakRankEndpoint

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG3RTowerClass MaxLocusLocal G3UniversePhysicalClassComparisons
  HironakaG8PhysicalChartOccupiedLifts HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8SpatialCofinalPrecedence HironakaG8WeakRankCofinalWords
  HironakaG8KeyedPackedRoundFamily HironakaG8PackedRoundRanks HironakaG8PackedNestedPair
  HironakaG8ConsecutiveNestedReorderings HironakaG8NestedRankFootprintAlignment
  HironakaG8RankedSingularGeometry HironakaG8ReorderedComparisonRank HironakaG8SpatialWeakRankHeight
  HironakaG8StageRankCoherence
  HironakaStageCenters HironakaEmbeddedAnalytic MarkedIdealTowerTransport
  HironakaNormalCrossingsSeparationChoiceComparison
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLimitCarrierGeometry HironakaG4CompactComponentLimit HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}

/-- Pack tied disjoint events and glue the exactly compared charts along a
common weak spatial rank. Every finite global prefix is original TEST and
uses only intrinsically singular centres. -/
theorem intrinsic_endpoint_of_cofinal_weak_spatial_rank
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (rank : ι → ℕ)
    (hSpatial : ∀ ⦃a b⦄, SpatialBefore E a b → rank a < rank b)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M (s.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj W)) (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
      limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  classical
  obtain ⟨tag,D,F,hNested⟩ :=
    HironakaG8ComparablePackedRounds.exists_comparable_packed_round_family
      E cmp hMono hLift hOccurs rank hSpatial M hM hN hTest W hW.isClosed hSing hSmooth
  let event i := listedOccupiedEvent (F.tower i) (F.labels i) (F.occupied i)
  exact intrinsic_endpoint_of_matched_sorted_charts F.tower event id
    (fun i => strictMono_listedRank (F.tower i) (F.labels i) (F.occupied i) id (F.sorted i))
    hMono hCover hNested M hM F.test W hW F.singular F.smooth

/-- A chart family with bounded incoming spatial path length at each
event admits one proper intrinsic resolution sequence. -/
theorem intrinsic_endpoint_of_cofinal_bounded_spatial_height
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p = a)
    (hHeight : ∀ b, ∃ bound, ∀ l, DependencyPath (SpatialBefore E) l b → l ≤ bound)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M (s.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj W)) (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
      limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  obtain ⟨rank,hRank⟩ := (exists_weak_spatial_rank_iff_bounded_height E).mpr hHeight
  exact intrinsic_endpoint_of_cofinal_weak_spatial_rank hCover E cmp hMono hLift hOccurs
    rank hRank M hM hN hTest W hW hSing hSmooth

end Hironaka.HironakaG8CofinalWeakRankEndpoint
