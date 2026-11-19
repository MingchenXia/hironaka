import Hironaka.Resolution.HironakaG8CompressedNestedGeometry
import Hironaka.Resolution.HironakaG8SortedNestedPairDescent
import Hironaka.Resolution.HironakaG8NestedRankFootprintAlignment
import Hironaka.Resolution.HironakaG8ReorderedSingularEndpoint

/-! Retained physical words and common-rank cofinal footprint readback give exact nested geometry. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CofinalSortedWordGeometry

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG3RTowerClass MaxLocusLocal
  G3UniversePhysicalClassComparisons HironakaG8PhysicalChartOccupiedLifts
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8ConsecutiveNestedReorderings HironakaG8CompressedNestedGeometry
  HironakaG8NestedVisibleWordLift HironakaG8GeometricIndexedWord HironakaG8SortedNestedPairDescent
  HironakaG8NestedRankFootprintAlignment HironakaG8OrderedFootprintTraces

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z → X}
  {c : ℕ → TowerChart K Z P} {ι : Type*}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- The exact fixed geometric sorting words compare over every pair of
literal cofinal restrictions when their footprint lists use a common rank. -/
theorem nested_geometry_of_cofinal_keyed_words {κ : Type*} [LinearOrder κ]
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → κ) (hRank : Function.Injective rank)
    (order : ∀ i, List {k // Occupied (c i).T k}) (hComplete : ∀ i p, p ∈ order i)
    (hSorted : ∀ i, (order i).Pairwise (fun p q => rank (E.event i p) < rank (E.event i q)))
    {A B : ℕ → CMfd.{0} n}
    (Q : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i))
    (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (B i))
    (a : ∀ i, A i ≃ₘ⟮𝓘c,𝓘c⟯ (c i).Y)
    (hCmp : ∀ i, EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (c i).U) ∞)
      (Q i) (c i).T (a i))
    (W : ∀ i, Set (c i).U)
    (M : ∀ i, MarkedIdeal n (CMfd.of (n := n) (c i).U)) (hM : ∀ i, (M i).IsWellFormed)
    (word : ℕ → List ℕ)
    (hWord : ∀ i, RealizedWord (GeometricIndexedMove (W i) (M i)) (word i)
      ⟨A i,Q i⟩ ⟨B i,R i⟩)
    (hRead : ∀ i k p, (order i)[k]? = some p → slotFootprint (R i) k = slotFootprint (c i).T p.val)
    (hOcc : ∀ i k, (slotFootprint (R i) k).Nonempty ↔ k < (order i).length) :
    ∀ i j, i ≤ j → NestedGeometry (R i) (R j) := by
  classical
  intro i j hij
  have hOriginal := physical_comparison_nested_chart cmp (c i) (c j) (hMono hij)
  dsimp only at hOriginal
  rw [inf_eq_left.mpr (hMono hij)] at hOriginal
  have hCompressed := nestedGeometry_of_compressions hOriginal (hCmp i) (hCmp j)
  obtain ⟨f,hf,e,hGeo⟩ := hCompressed
  have hTraces := keyed_cofinal_footprint_traces_agree E cmp hMono hLift rank hRank order
    hComplete hSorted R hRead hOcc hij
  have hFoot := nested_occupied_footprints_eq_of_ambient_traces (R i) (R j) f hf hTraces
  obtain ⟨_,_,_,_,hResult⟩ := sorted_nested_pair_of_occupiedFootprints_eq
    (W i) (W j) (M i) (M j) (hM i) (hWord i) (hWord j) f hf e hGeo hFoot
  exact ⟨f,hf,_,hResult⟩

/-- Literal nested comparisons for geometric words sorted by natural keys. -/
theorem nested_geometry_of_cofinal_sorted_words
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (hRank : Function.Injective rank)
    (order : ∀ i, List {k // Occupied (c i).T k}) (hComplete : ∀ i p, p ∈ order i)
    (hSorted : ∀ i, (order i).Pairwise (fun p q => rank (E.event i p) < rank (E.event i q)))
    {A B : ℕ → CMfd.{0} n}
    (Q : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i))
    (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (B i))
    (a : ∀ i, A i ≃ₘ⟮𝓘c,𝓘c⟯ (c i).Y)
    (hCmp : ∀ i, EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (c i).U) ∞)
      (Q i) (c i).T (a i))
    (W : ∀ i, Set (c i).U)
    (M : ∀ i, MarkedIdeal n (CMfd.of (n := n) (c i).U)) (hM : ∀ i, (M i).IsWellFormed)
    (word : ℕ → List ℕ)
    (hWord : ∀ i, RealizedWord (GeometricIndexedMove (W i) (M i)) (word i)
      ⟨A i,Q i⟩ ⟨B i,R i⟩)
    (hRead : ∀ i k p, (order i)[k]? = some p → slotFootprint (R i) k = slotFootprint (c i).T p.val)
    (hOcc : ∀ i k, (slotFootprint (R i) k).Nonempty ↔ k < (order i).length) :
    ∀ i j, i ≤ j → NestedGeometry (R i) (R j) :=
  nested_geometry_of_cofinal_keyed_words E cmp hMono hLift rank hRank order hComplete
    hSorted Q R a hCmp W M hM word hWord hRead hOcc

open MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG8ReorderedSingularEndpoint HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLimitCarrierGeometry HironakaG4CompactComponentLimit HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- Retained physical sorting words with common-rank footprints and
finished local singular TESTs give a single proper physical growing limit. -/
theorem intrinsic_endpoint_of_cofinal_sorted_words
    (hCover : ∀ x : X, ∃ i, x ∈ (c i).U)
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i ≤ j) p,
      E.lift h p = chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (rank : ι → ℕ) (hRank : Function.Injective rank)
    (order : ∀ i, List {k // Occupied (c i).T k}) (hComplete : ∀ i p, p ∈ order i)
    (hSorted : ∀ i, (order i).Pairwise (fun p q => rank (E.event i p) < rank (E.event i q)))
    {A B : ℕ → CMfd.{0} n}
    (Q : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (A i))
    (R : ∀ i, BlowupTower (CMfd.of (n := n) (c i).U) (B i))
    (a : ∀ i, A i ≃ₘ⟮𝓘c,𝓘c⟯ (c i).Y)
    (hCmp : ∀ i, EmptyAwareTowerIso (Diffeomorph.refl 𝓘c (CMfd.of (n := n) (c i).U) ∞)
      (Q i) (c i).T (a i))
    (W : ∀ i, Set (c i).U)
    (M : ∀ i, MarkedIdeal n (CMfd.of (n := n) (c i).U)) (hM : ∀ i, (M i).IsWellFormed)
    (word : ℕ → List ℕ)
    (hWord : ∀ i, RealizedWord (GeometricIndexedMove (W i) (M i)) (word i)
      ⟨A i,Q i⟩ ⟨B i,R i⟩)
    (hRead : ∀ i k p, (order i)[k]? = some p → slotFootprint (R i) k = slotFootprint (c i).T p.val)
    (hOcc : ∀ i k, (slotFootprint (R i) k).Nonempty ↔ k < (order i).length)
    (M₀ : MarkedIdeal n X) (hM₀ : M₀.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M₀) (R i))
    (W₀ : Set X) (hW : IsComplexAnalyticSubset (n := n) W₀)
    (hLocalSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : (c i).U → X) ⁻¹' W₀))) (R i))
    (hLocalSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (R i).proj ((Subtype.val : (c i).U → X) ⁻¹' W₀))) :
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M₀ (s.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj W₀)) (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W₀) ∧
      limitStrictTransform s hLF W₀ = strictTransform n (gluedProjection s hLF) W₀ ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W₀)ᶜ := by
  apply intrinsic_endpoint_of_nested_rank_reorderings E cmp hMono hCover hLift rank
    order hComplete hSorted R hRead hOcc _ M₀ hM₀ hTest W₀ hW hLocalSing hLocalSmooth
  intro i j hij
  rw [inf_eq_left.mpr (hMono hij)]
  exact nested_geometry_of_cofinal_sorted_words E cmp hMono hLift rank hRank order
    hComplete hSorted Q R a hCmp W M hM word hWord hRead hOcc i j hij

end Hironaka.HironakaG8CofinalSortedWordGeometry
