import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule
import Hironaka.Resolution.HironakaG8EmptyStageOverlapComparisons
import Hironaka.Resolution.HironakaG8OpenCoverTestLimit

/-! A single intrinsic resolution from finished local TESTs with regular overlaps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8RegularOverlapTestLimit

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG8IntrinsicSingularBlockSchedule HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaResolutionSpaceLocal AnalyticSubsetOpens RestrictEmptyTower MaxLocusLocal
  HironakaG8FirstFootprintOrder HironakaG8EmptyStageOverlapComparisons
  HironakaG8OpenCoverTestLimit MarkedIdeals MarkedIdealBiholomorphism MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitCarrierGeometry
  HironakaActualLocallyFiniteHistoryOverlap HironakaAdmissibleSequence HironakaG4CompactComponentLimit
  HironakaG8OccupiedSlotComparison

variable {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}

/-- The restriction to a chart overlap avoiding the original singular set
has no occupied stages in an intrinsically singular history. -/
theorem centresAvoid_regular_overlap
    (U V : Opens X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hRegular : Disjoint (singularSet (n := n) W) ((U : Set X) ∩ (V : Set X)))
    (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) T) :
    CentresAvoid (nestedOpens U V) T := by
  have hU := isComplexAnalyticSubset_preimage_val hW U
  apply intrinsic_singular_history_avoids_regular_open hU _ ?_ T hStage
  rw [singularSet_preimage_val]
  exact Set.disjoint_left.mpr (fun x hx hV => Set.disjoint_left.mp hRegular hx ⟨x.property,hV⟩)

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- Complete local TESTs on an open cover whose distinct overlaps avoid the
original singular locus combine into one intrinsic resolution. The local
tower lengths may be unbounded. -/
theorem intrinsic_endpoint_of_regular_overlap_tests
    {I : Type} (U : I → Opens X) (hCover : ∀ x : X, ∃ i, x ∈ U i)
    {Y : I → CMfd.{0} n} (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (T i))
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) (T i))
    (hSmooth : ∀ i, IsClosedSubmanifold n (strictTransform n (T i).proj ((Subtype.val : U i → X) ⁻¹' W)))
    (hRegular : ∀ ⦃i j⦄, i ≠ j →
      Disjoint (singularSet (n := n) W) ((U i : Set X) ∩ (U j : Set X))) :
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M (s.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
      limitStrictTransform s hLF W = strictTransform n (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧ Function.Surjective (gluedProjection s hLF) ∧
      ContMDiff 𝓘c 𝓘c ∞ (gluedProjection s hLF : limitManifold s hLF → X) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  have hAvoid (i j : I) (hij : i ≠ j) (k : ℕ) :
      Disjoint (slotFootprint (T i) k) ((Subtype.val : U i → X) ⁻¹' (U j : Set X)) := by
    let O := nestedOpens (U i) (U j)
    have hOver := centresOver_compl_of_centresAvoid O (T i)
      (centresAvoid_regular_overlap (U i) (U j) hW (hRegular hij) (T i) (hSing i))
    have hFoot := slotFootprint_subset_of_centresOver (T i) hOver k
    exact Set.disjoint_left.mpr fun _ hx hy => hFoot hx hy
  exact intrinsic_endpoint_of_compatible_open_tests U hCover T
    (strictPairwiseComparisons_of_empty_stage_overlaps U T (fun {i j} hij => hAvoid i j hij))
    M hM hTest W hW hSing hSmooth

end Hironaka.HironakaG8RegularOverlapTestLimit
