import Hironaka.Resolution.HironakaG8RegularOverlapTestLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SingularCoverTestLimit

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaG8IntrinsicSingularBlockSchedule HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaResolutionSpaceLocal AnalyticSubsetOpens RestrictEmptyTower MaxLocusLocal
  HironakaG8FirstFootprintOrder HironakaG8EmptyStageOverlapComparisons
  HironakaG8OpenCoverTestLimit MarkedIdeals MarkedIdealBiholomorphism MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitCarrierGeometry
  HironakaActualLocallyFiniteHistoryOverlap HironakaAdmissibleSequence HironakaG4CompactComponentLimit
  HironakaG8RegularOverlapTestLimit

variable {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- The local finite TESTs need cover only the singular locus; the regular
complement is served by its literal reflexive tower. -/
theorem intrinsic_endpoint_of_singular_cover_tests
    {I : Type} (U : I → Opens X)
    {Y : I → CMfd.{0} n} (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M) (T i))
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) (T i))
    (hSmooth : ∀ i, IsClosedSubmanifold n (strictTransform n (T i).proj ((Subtype.val : U i → X) ⁻¹' W)))
    (hCover : ∀ x ∈ singularSet (n := n) W, ∃ i, x ∈ U i)
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
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ, (isClosed_singularSet hW.isClosed).isOpen_compl⟩
  let U' : Option I → Opens X
    | none => O
    | some i => U i
  let Y' : Option I → CMfd.{0} n
    | none => CMfd.of (n := n) O
    | some i => Y i
  let T' : ∀ i, BlowupTower (CMfd.of (n := n) (U' i)) (Y' i)
    | none => .refl
    | some i => T i
  have hCover' (x : X) : ∃ i, x ∈ U' i := by
    by_cases hx : x ∈ singularSet (n := n) W
    · obtain ⟨i,hi⟩ := hCover x hx
      exact ⟨some i,hi⟩
    · exact ⟨none,hx⟩
  have hTest' (i : Option I) :
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U' i → X) M) (T' i) := by
    cases i with
    | none => trivial
    | some i => exact hTest i
  have hSing' (i : Option I) : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U' i → X) ⁻¹' W))) (T' i) := by
    cases i with
    | none => trivial
    | some i => exact hSing i
  have hSmooth' (i : Option I) : IsClosedSubmanifold n
      (strictTransform n (T' i).proj ((Subtype.val : U' i → X) ⁻¹' W)) := by
    cases i with
    | some i => exact hSmooth i
    | none =>
      change IsClosedSubmanifold n (strictTransform n id ((Subtype.val : O → X) ⁻¹' W))
      have hClosed := hW.isClosed.preimage (continuous_subtype_val (p := fun x : X => x ∈ O))
      rw [HironakaG11PresTowerState.strictTransform_id (n := n) (X := CMfd.of (n := n) O) hClosed]
      refine ⟨hClosed, fun x hx => ?_⟩
      obtain ⟨d,hd⟩ : ∃ d, RegularAtDim (n := n) W x.val d := by
        by_contra h
        exact x.property (mem_singularSet_iff.mpr ⟨hx,fun d hd => h ⟨d,hd⟩⟩)
      exact ⟨d,regularAtDim_preimage_val_iff.mpr hd⟩
  have hRegular' : ∀ ⦃i j : Option I⦄, i ≠ j →
      Disjoint (singularSet (n := n) W) ((U' i : Set X) ∩ (U' j : Set X)) := by
    intro i j hij
    cases i with
    | none =>
      exact Set.disjoint_left.mpr fun _ hx hy => hy.1 hx
    | some i =>
      cases j with
      | none => exact Set.disjoint_left.mpr fun _ hx hy => hy.2 hx
      | some j => exact hRegular (fun h => hij (congrArg Option.some h))
  exact intrinsic_endpoint_of_regular_overlap_tests U' hCover' T' M hM hTest' W hW hSing' hSmooth' hRegular'

#print axioms intrinsic_endpoint_of_singular_cover_tests

end Hironaka.HironakaG8SingularCoverTestLimit
