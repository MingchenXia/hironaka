import Hironaka.Resolution.HironakaG8RankedSingularGeometry
import Hironaka.Resolution.HironakaG8ReorderedComparisonRank

/-! Intrinsic physical endpoints of nested rank reorderings. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ReorderedSingularEndpoint

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaG8OccupiedSlotComparison HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry
  HironakaG3RTowerClass HironakaG8PhysicalChartOccupiedLifts G3UniversePhysicalClassComparisons
  HironakaG8ReorderedComparisonRank HironakaStageCenters HironakaEmbeddedAnalytic MaxLocusLocal
  HironakaG8RankedSingularGeometry HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitCarrierGeometry
  HironakaG4CompactComponentLimit HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- The actual nested comparison of reordered charts already preserves the
ranks determined by their exact occupied footprint lists. -/
theorem intrinsic_endpoint_of_nested_rank_reorderings {n : ℕ} {X : CMfd.{0} n} {Y : ℕ → CMfd.{0} n}
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
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U → X) M) (R i))
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hLocalSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : (c i).U → X) ⁻¹' W))) (R i))
    (hLocalSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (R i).proj ((Subtype.val : (c i).U → X) ⁻¹' W))) :
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M (s.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj W)) (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
      limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  let event (i : ℕ) (p : {k // Occupied (R i) k}) :=
    E.event i (listedOccupiedEvent (R i) (order i) (hOcc i) p)
  apply intrinsic_endpoint_of_matched_sorted_charts R event rank
    (fun i => strictMono_listedRank (R i) (order i) (hOcc i) _ (hSorted i))
    hMono hCover _ M hM hTest W hW hLocalSing hLocalSmooth
  intro i j hij
  obtain ⟨φ,hφ,ψ,hCmp⟩ := hNested i j hij
  exact ⟨φ,hφ,ψ,hCmp,rank_preserved_by_reordered_comparison E cmp hMono hLift
    rank order hComplete hSorted R hRead hOcc hij hCmp⟩

end Hironaka.HironakaG8ReorderedSingularEndpoint
