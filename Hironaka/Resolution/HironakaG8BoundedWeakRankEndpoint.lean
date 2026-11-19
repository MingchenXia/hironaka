import Hironaka.Resolution.HironakaG8ComparablePackedRounds
import Hironaka.Resolution.HironakaG8FiniteEventTestEndpoint

/-! A finite global TEST from a uniformly bounded common weak rank. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8BoundedWeakRankEndpoint
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

open HironakaG8ComparablePackedRounds HironakaG8FiniteEventTestEndpoint

variable {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}

/-- Uniformly bounded weak spatial ranks give an actual finite original TEST.
Ties and infinitely many distinct original events are permitted. -/
theorem finite_endpoint_of_uniformly_bounded_weak_spatial_rank
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i≤j) p,
      E.lift h p=chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p=a)
    (hCover : ∀ x : X, ∃ i, x∈(c i).U)
    (rank : ι → ℕ)
    (hSpatial : ∀ ⦃a b⦄, SpatialBefore E a b → rank a<rank b)
    (N : ℕ) (hCap : ∀ a, rank a<N)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hN : M.N=univ)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (c i).T)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (c i).T)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      T.length=N ∧ IsGeoTestTower M T ∧
      StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj W) ∧
      IsProperMap T.proj ∧ Function.Surjective T.proj ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsIsomorphismOver n T.proj (singularSet (n := n) W)ᶜ := by
  classical
  obtain ⟨tag,D,F,hNested⟩ := exists_comparable_packed_round_family
    E cmp hMono hLift hOccurs rank hSpatial M hM hN hTest W hW.isClosed hSing hSmooth
  let label (i : ℕ) := listedOccupiedEvent (F.tower i) (F.labels i) (F.occupied i)
  have hs (i : ℕ) : StrictMono (label i) :=
    strictMono_listedRank (F.tower i) (F.labels i) (F.occupied i) id (F.sorted i)
  let d (i : ℕ) := Classical.choice (exists_ranked_test_compression _
    (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U)
    (F.tower i) (F.test i) (label i) (hs i))
  have hClock (i : ℕ) : (d i).clock≤N :=
    compression_clock_le_of_rank_bound (d i)
      (packed_label_lt_of_rank_bound E rank D F hCap i)
  have hPair : StrictPairwiseComparisons (fun i => (c i).U)
      (fun i => (d i).decoration.pad) :=
    strict_pairwise_of_nested (fun i => (c i).U) d hMono hNested
  have hLen (i : ℕ) : (d i).decoration.pad.length≤N := by
    rw [(d i).decoration.pad_length]
    exact hClock i
  have hPTest (i : ℕ) :
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M)
        (d i).decoration.pad := by
    simpa [RankedTower.through,identityEmptyTail] using test_ranked_through _
      (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (c i).U)
      (d i).test (d i).decoration (d i).clock
  have hPSing (i : ℕ) : StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (d i).decoration.pad := by
    have h := (singular_stageCentres_ranked_compression_iff _ (d i)
      (hW.isClosed.preimage continuous_subtype_val) (d i).clock).mpr (F.singular i)
    simpa [RankedTower.through,identityEmptyTail] using h
  have hPSmooth (i : ℕ) : IsClosedSubmanifold n
      (strictTransform n (d i).decoration.pad.proj ((Subtype.val : (c i).U → X) ⁻¹' W)) := by
    have h := isClosedSubmanifold_ranked_through _ (d i)
      (hW.isClosed.preimage continuous_subtype_val) (F.smooth i) (d i).clock
    simpa [RankedTower.through,identityEmptyTail] using h
  let A := actualEndpointHistories (fun i => (c i).U) (fun i => (d i).decoration.pad) hPair
  let T := ((uniformGrowingSeq A hCover).stage N).2
  obtain ⟨hLength,hGlobalTest,hGlobalSing,hGlobalSmooth,hProper,hHolo⟩ :=
    bounded_endpoint_of_compatible_open_tests (fun i => (c i).U) hCover
      (fun i => (d i).decoration.pad) hPair N hLen M hM hPTest W hW hPSing hPSmooth
  have hProtect := actual_singular_history_original_regular_protection W hW T
    (intrinsic_stage_native_history W T hGlobalSing)
  have hIso : IsIsomorphismOver n T.proj (singularSet (n := n) W)ᶜ := hProtect.2.1
  exact ⟨_,T,hLength,hGlobalTest,hGlobalSing,hGlobalSmooth,hProper,
    proper_regular_open_iso_surjective W T.proj hProper hIso,hHolo,hIso⟩

end
end Hironaka.HironakaG8BoundedWeakRankEndpoint
