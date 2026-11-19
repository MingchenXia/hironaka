import Hironaka.Resolution.HironakaG8DisjointClockAtlas
import Hironaka.Resolution.HironakaG8RankedSingularGeometry

/-! A single intrinsic original TEST chronology from compatible open tests. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8OpenCoverTestLimit

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaG8RankedGlobalTest HironakaG8DisjointClockAtlas HironakaG8StageRankCoherence
  HironakaSharpActualCurveChosenOverlapCocycle HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOverlapMaps
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveOriginalGrowingHistory
  MaxLocusLocal MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealBiholomorphism.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8RankedSingularGeometry HironakaG8SurfaceLimitEndpoint
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLimitCarrierGeometry HironakaG4CompactComponentLimit HironakaAdmissibleSequence

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- Finished, compatibly compared finite TEST towers over an open cover
produce one locally finite proper smooth resolution history. -/
theorem intrinsic_endpoint_of_compatible_open_tests
    {I : Type} (U : I → Opens X) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    {Y : I → CMfd.{0} n} (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (hPair : StrictPairwiseComparisons U T)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (T i))
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) (T i))
    (hSmooth : ∀ i, IsClosedSubmanifold n (strictTransform n (T i).proj ((Subtype.val : U i → X) ⁻¹' W))) :
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M (s.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
      limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧ Function.Surjective (gluedProjection s hLF) ∧
      ContMDiff 𝓘c 𝓘c ∞ (gluedProjection s hLF : limitManifold s hLF → X) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  let A := actualEndpointHistories U T hPair
  let s := uniformGrowingSeq A hCover
  have hLF : LocallyFinite (centreImage s) := uniform_growing_seq_locally_finite A hCover
  have hGTest : ∀ k, IsGeoTestTower M (s.stage k).2 := by
    apply uniform_growing_seq_original_test A hCover M hM.isClosedSubmanifold_N hM.isCoherent
    intro i
    change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (BlowupTower.refl.append (T i))
    rw [BlowupTower.refl_append]
    exact hTest i
  have hLocalSing (i : I) : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : A.openSet i → X) ⁻¹' W)))
      ((A.prefixTower i).append (A.tail i)) := by
    simpa only [A,actualEndpointHistories,BlowupTower.refl_append] using hSing i
  have hLocalSmooth (i : I) :
      IsClosedSubmanifold n (strictTransform n ((A.prefixTower i).append (A.tail i)).proj
        ((Subtype.val : A.openSet i → X) ⁻¹' W)) := by
    change IsClosedSubmanifold n (strictTransform n (BlowupTower.refl.append (T i)).proj
      ((Subtype.val : U i → X) ⁻¹' W))
    rw [BlowupTower.refl_append]
    exact hSmooth i
  obtain ⟨hGSing,hStrict,hEq,hProper,hIso⟩ :=
    intrinsic_uniformGrowingSeq_endpoint_indexed A hCover W hW hLF hLocalSing hLocalSmooth
  exact ⟨s,hLF,hGTest,hGSing,hStrict,hEq,hProper,proper_regular_open_iso_surjective (Y := CMfd.of (n := n) (limitManifold s hLF))
      W (gluedProjection s hLF) hProper hIso,
    gluedProjection_contMDiff s hLF,hIso⟩

end Hironaka.HironakaG8OpenCoverTestLimit
