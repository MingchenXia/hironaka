import Hironaka.Resolution.HironakaG8WeakRankCofinalWords
import Hironaka.Resolution.HironakaG8KeyedPackedRoundFamily
import Hironaka.Resolution.HironakaG8PackedRoundRanks
import Hironaka.Resolution.HironakaG8PackedNestedPair
import Hironaka.Resolution.HironakaG8NestedRankFootprintAlignment
import Hironaka.Resolution.HironakaG8SpatialWeakRankHeight
import Hironaka.Resolution.HironakaG8RankedSingularGeometry
import Hironaka.Resolution.HironakaG8BoundedOpenTestEndpoint

/-! Comparable packed native rounds from a common weak spatial rank. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ComparablePackedRounds
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8RankOccupiedAnnotation HironakaG8RankedEmptyPadding
  HironakaG8RankedTestCompression HironakaG8RankedNestedGlobalTest
  HironakaG8RankedGlobalTest HironakaG8RankedSingularGeometry
  HironakaG8PhysicalChartOccupiedLifts HironakaG3RTowerClass
  G3UniversePhysicalClassComparisons HironakaG3EmptyAwareHistory
  HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8BoundedOpenTestEndpoint HironakaSharpActualCurveEmptyPadding
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOriginalGrowingHistory
  HironakaG8IntrinsicSingularBlockSchedule HironakaUniformHistoricalSuccessorOriginalRegular
  HironakaG8SurfaceLimitEndpoint HironakaNormalCrossingsSeparationChoiceComparison

open HironakaG8WeakRankCofinalWords HironakaG8KeyedPackedRoundFamily
  HironakaG8PackedRoundRanks HironakaG8PackedNestedPair
  HironakaG8ConsecutiveNestedReorderings HironakaG8NestedRankFootprintAlignment
  HironakaG8ReorderedComparisonRank HironakaG8SpatialCofinalPrecedence
  HironakaG8CofinalSpatialRankEndpoint HironakaG8PackedRoundFamily
  HironakaG8CofinalRoundFootprints MaxLocusLocal

variable {n : ℕ} {X Y : CMfd.{0} n}

variable {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}

/-- Exact readback of the existing sorted-and-packed weak-rank construction.
The whole old D/F structures and the actual nested comparison are retained. -/
theorem exists_comparable_packed_round_family
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i≤j) p,
      E.lift h p=chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p=a)
    (rank : ι → ℕ)
    (hSpatial : ∀ ⦃a b⦄, SpatialBefore E a b → rank a<rank b)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N=univ)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T)
    (W : Set X) (hW : IsClosed W)
    (hSing : ∀ i, StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) :

    ∃ (tag : ι → ℕ)
      (D : CofinalKeyedSingularWords E
        (fun a => (toLex (rank a,tag a) : ℕ ×ₗ ℕ)) M W)
      (F : PackedRoundFamily D.R (fun i r => chartRoundFootprint E rank r i)
        (fun i => MarkedIdeal.pullback (Subtype.val : (c i).U → X) M)
        (fun i => (Subtype.val : (c i).U → X) ⁻¹' W)),
      ∀ i j, i≤j → NestedRankComparison (O := (c i).U ⊓ (c j).U)
        (F.tower i) (F.tower j)
        (listedOccupiedEvent (F.tower i) (F.labels i) (F.occupied i))
        (listedOccupiedEvent (F.tower j) (F.labels j) (F.occupied j)) := by
  classical
  obtain ⟨tag,D,_,hNested,hSorted,hDisjoint⟩ := exists_cofinal_weak_rank_word_geometry
    E cmp hMono hLift hOccurs rank hSpatial M hM hN hTest W hW hSing hSmooth
  obtain ⟨F⟩ := exists_keyed_packed_round_family E D rank hM hSorted hDisjoint
  have hPacked (i j : ℕ) (hij : i≤j) : NestedGeometry (F.tower i) (F.tower j) := by
    obtain ⟨e,he,f,hOld⟩ := hNested i j hij
    have hTrace := packed_round_occupiedFootprint_traces_agree E cmp hMono hLift
      rank F.labels F.sorted F.labels_iff F.tower F.readback F.occupied hij
    have hFoot := nested_occupied_footprints_eq_of_ambient_traces (F.tower i) (F.tower j)
      e he hTrace
    obtain ⟨g,_,hNew⟩ := packed_nested_pair_of_occupiedFootprints_eq
      (D.R i) (F.tower i) (D.R j) (F.tower j) (F.packing i) (F.packing j) e he f hOld
      (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M)
      (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U) hFoot
    exact ⟨e,he,g,hNew⟩
  refine ⟨tag,D,F,?_⟩
  intro i j hij
  exact nestedRankComparison_of_packed_rounds E cmp hMono hLift rank F.labels F.sorted
    F.labels_iff F.tower F.readback F.occupied hij (hPacked i j hij)

/-- An actual packed label is witnessed by an original event at that rank. -/
theorem packed_label_lt_of_rank_bound
    (E : CofinalEvents c ι) (rank : ι → ℕ)
    {κ : Type*} [LinearOrder κ] {key : ι → κ}
    {M : MarkedIdeal n X} {W : Set X}
    (D : CofinalKeyedSingularWords E key M W)
    (F : PackedRoundFamily D.R (fun i r => chartRoundFootprint E rank r i)
      (fun i => MarkedIdeal.pullback (Subtype.val : (c i).U → X) M)
      (fun i => (Subtype.val : (c i).U → X) ⁻¹' W))
    {N : ℕ} (hCap : ∀ a, rank a<N) (i : ℕ)
    (p : {k // Occupied (F.tower i) k}) :
    listedOccupiedEvent (F.tower i) (F.labels i) (F.occupied i) p<N := by
  have hMem : listedOccupiedEvent (F.tower i) (F.labels i) (F.occupied i) p ∈ F.labels i :=
    List.get_mem _ _
  obtain ⟨x,hx⟩ := (F.labels_iff i _).mp hMem
  obtain ⟨q,_⟩ := mem_iUnion.mp hx
  exact q.property ▸ hCap (E.event i q.val)

end
end Hironaka.HironakaG8ComparablePackedRounds
