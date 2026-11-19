import Hironaka.Resolution.HironakaG8RankedNestedGlobalTest
import Hironaka.Resolution.HironakaG8ReorderedComparisonRank

/-! Global original TEST from sorted towers with literal nested comparisons. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8MatchedSortedGlobalTest

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG8RankedNestedGlobalTest
  HironakaG8RankedTestCompression HironakaG8RankedEmptyPadding
  HironakaG8OccupiedSlotComparison HironakaG3EmptyAwareHistory
  HironakaG8CofinalOccupiedAncestry MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG8RankedGlobalTest HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOriginalGrowingHistory
  HironakaLocallyFiniteResolutionSequence MaxLocusLocal

variable {n : ℕ} {X : CMfd.{0} n} {U : ℕ → Opens X} {Y : ℕ → CMfd.{0} n}
  (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))

/-- A comparison across a nested window matches actual reordered towers
and preserves the global event of each surviving occupied occurrence. -/
def NestedEventComparison {ι : Type*}
    (event : ∀ i, {k // Occupied (T i) k} → ι) (i j : ℕ) : Prop :=
  ∃ φ : CMfd.of (n := n) (U i) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens (U j) (U i ⊓ U j)),
    (∀ x : U i, (φ x).val.val = x.val) ∧
    ∃ ψ : Y i ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage (T j) (nestedOpens (U j) (U i ⊓ U j))),
      ∃ h : EmptyAwareTowerIso φ (T i) (restrict (nestedOpens (U j) (U i ⊓ U j)) (T j)) ψ,
        ∀ p, event i p = event j (occupiedLiftOnOpen _ (T j) h p)

theorem nestedEventComparison_iff_rank {ι : Type*}
    (event : ∀ i, {k // Occupied (T i) k} → ι) (rank : ι → ℕ)
    (hInjective : Function.Injective rank) (i j : ℕ) :
    NestedEventComparison T event i j ↔
    NestedRankComparison (O := U i ⊓ U j) (T i) (T j) (rank ∘ event i) (rank ∘ event j) := by
  constructor
  · rintro ⟨φ,hφ,ψ,h,hEvent⟩
    exact ⟨φ,hφ,ψ,h,fun p => congrArg rank (hEvent p)⟩
  · rintro ⟨φ,hφ,ψ,h,hRank⟩
    exact ⟨φ,hφ,ψ,h,fun p => hInjective (hRank p)⟩

/-- Sorted local TEST towers with genuinely matched nested restrictions
give a single locally finite growing original TEST sequence. -/
theorem global_test_of_matched_sorted_charts
    {ι : Type*} (event : ∀ i, {k // Occupied (T i) k} → ι)
    (rank : ι → ℕ) (hSorted : ∀ i, StrictMono (rank ∘ event i))
    (hMono : Monotone U) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    (hMatched : ∀ i j, i ≤ j →
      NestedRankComparison (O := U i ⊓ U j) (T i) (T j) (rank ∘ event i) (rank ∘ event j))
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (T i)) :
    ∃ A : ActualEndpointHistories X ℕ,
      ∃ hCoverA : ∀ x : X, ∃ i, x ∈ A.openSet i,
        LocallyFinite (centreImage (uniformGrowingSeq A hCoverA)) ∧
          ∀ k, IsGeoTestTower M ((uniformGrowingSeq A hCoverA).stage k).2 := by
  classical
  let d (i : ℕ) := Classical.choice (exists_ranked_test_compression _
    (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM (U i))
    (T i) (hTest i) (rank ∘ event i) (hSorted i))
  have hComparisons := strict_pairwise_of_nested U d hMono hMatched
  refine ⟨actualEndpointHistories _ _ hComparisons,hCover,?_⟩
  exact ranked_test_compressions_globalize M hM _ hCover d hComparisons

open HironakaG3RTowerClass HironakaG8PhysicalChartOccupiedLifts
  G3UniversePhysicalClassComparisons HironakaG8ReorderedComparisonRank

/-- Actual nested comparisons of physically reordered cofinal TEST charts
already have the rank agreement needed for a single global original TEST. -/
theorem global_test_of_nested_rank_reorderings
    {Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
    {c : ℕ → TowerChart K Z P} {ι : Type*}
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ)
    (order : ∀ i, List {k // Occupied (c i).T k}) (hComplete : ∀ i p, p ∈ order i)
    (hSorted : ∀ i, (order i).Pairwise (fun p q => rank (E.event i p) < rank (E.event i q)))
    (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (Y i))
    (hRead : ∀ i k p, (order i)[k]? = some p → slotFootprint (R i) k = slotFootprint (c i).T p.val)
    (hOcc : ∀ i k, (slotFootprint (R i) k).Nonempty ↔ k < (order i).length)
    (hNested : ∀ i j, i ≤ j →
      ∃ φ : CMfd.of (n := n) (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (nestedOpens (c j).U ((c i).U ⊓ (c j).U)),
        (∀ x : (c i).U, (φ x).val.val = x.val) ∧
        ∃ ψ : Y i ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
            CMfd.of (n := n) (openPreimage (R j) (nestedOpens (c j).U ((c i).U ⊓ (c j).U))),
          EmptyAwareTowerIso φ (R i) (restrict (nestedOpens (c j).U ((c i).U ⊓ (c j).U)) (R j)) ψ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (R i)) :
    ∃ A : ActualEndpointHistories X ℕ,
      ∃ hCoverA : ∀ x : X, ∃ i, x ∈ A.openSet i,
        LocallyFinite (centreImage (uniformGrowingSeq A hCoverA)) ∧
          ∀ k, IsGeoTestTower M ((uniformGrowingSeq A hCoverA).stage k).2 := by
  let event (i : ℕ) (p : {k // Occupied (R i) k}) :=
    E.event i (listedOccupiedEvent (R i) (order i) (hOcc i) p)
  apply global_test_of_matched_sorted_charts R event rank
    (fun i => strictMono_listedRank (R i) (order i) (hOcc i) _ (hSorted i))
    hMono hCover _ M hM hTest
  intro i j hij
  obtain ⟨φ,hφ,ψ,hCmp⟩ := hNested i j hij
  exact ⟨φ,hφ,ψ,hCmp,rank_preserved_by_reordered_comparison E cmp hMono hLift
    rank order hComplete hSorted R hRead hOcc hij hCmp⟩

end Hironaka.HironakaG8MatchedSortedGlobalTest
