import Hironaka.Resolution.HironakaG8GrowingOpenTestLimit

/-! Growing original TESTs over a cover of the singular locus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Filter
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8GrowingSingularCoverTestLimit

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq ResolutionInvariantExt HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitCarrierGeometry
  HironakaAdmissibleSequence HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaG8AmbientGrowingClip HironakaG8AmbientStableTest HironakaG8AmbientStablePair
  HironakaG8RankedGlobalTest HironakaG8RegularOverlapTestLimit HironakaG8OpenCoverTestLimit
  HironakaG8OccupiedSlotComparison HironakaG8FirstFootprintOrder
  HironakaG8EmptyStageOverlapComparisons MaxLocusLocal
  HironakaG8GrowingOpenTestLimit HironakaG8SurfaceLimitEndpoint HironakaActualLimitProtectedOpen
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveStrictSetOverlaps AnalyticSubsetOpens HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- Identity blowups are the actual stages of the growing regular-chart sequence. -/
def identityGrowingSeq (A : CMfd.{0} n) : GrowingSeq A where
  stage k := ⟨A,identityEmptyTail A k⟩
  zero := rfl
  succ _ := ⟨∅,id,BlowupExistenceCodimOne.isBlowupAlong_id_empty,rfl⟩

theorem identityGrowingSeq_centreImage (A : CMfd.{0} n) (i : ℕ) :
    centreImage (identityGrowingSeq A) i = ∅ := by
  obtain ⟨π,hπ,hEq⟩ := exists_step_map (identityGrowingSeq A) i
  change (identityEmptyTail A i).step ∅ id BlowupExistenceCodimOne.isBlowupAlong_id_empty =
    (identityEmptyTail A i).step (stepCentre (identityGrowingSeq A) i) π hπ at hEq
  injection hEq with _ _ _ hC _
  simp [centreImage,hC.symm]

theorem identityGrowingSeq_locallyFinite (A : CMfd.{0} n) :
    LocallyFinite (centreImage (identityGrowingSeq A)) := by
  intro x
  refine ⟨univ,univ_mem,?_⟩
  simp [identityGrowingSeq_centreImage]

private theorem identityGrowingSeq_stageCentres (A : CMfd.{0} n) (B : Set A) (i : ℕ) :
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj B))
      ((identityGrowingSeq A).stage i).2 := by
  induction i with
  | zero => trivial
  | succ i ih => exact ⟨ih,empty_subset _⟩

private theorem identityGrowingSeq_strict_smooth (A : CMfd.{0} n) (B : Set A)
    (hB : IsComplexAnalyticSubset (n := n) B) (hSmooth : IsClosedSubmanifold n B) :
    IsClosedSubmanifold n (strictTransform n
      (gluedProjection (identityGrowingSeq A) (identityGrowingSeq_locallyFinite A)) B) := by
  let g := identityGrowingSeq A
  let hG := identityGrowingSeq_locallyFinite A
  have hIso := gluedProjection_isIsomorphismOver_compl_of_centreImages_subset g hG
    (singularSet (n := n) B) (fun i => by rw [show centreImage g i = ∅ from identityGrowingSeq_centreImage A i]; exact empty_subset _)
  have hEq := intrinsic_limit_strictTransform_eq_projection B hB g hG (identityGrowingSeq_stageCentres A B) hIso
  change IsClosedSubmanifold n (strictTransform n (gluedProjection g hG) B)
  rw [← hEq]
  refine ⟨isClosed_limitStrictTransform g hG hB.isClosed,?_⟩
  intro z hz
  obtain ⟨x,q,rfl⟩ := actualHistoryLocalInclusion_jointly_surjective g hG z
  have hRead := localInclusion_preimage_limitStrictTransform g hG hB.isClosed x
  have hq : q.val ∈ B := by
    have h := (Set.ext_iff.mp hRead q).mp hz
    change q.val ∈ strictAlong (identityEmptyTail A (stableIndex g hG x)) B at h
    rwa [strictAlong_identityEmptyTail hB.isClosed] at h
  obtain ⟨d,hd⟩ := hSmooth.2 q.val hq
  refine ⟨d,(regularAtDim_limitStrictTransform_local_iff g hG hB.isClosed x q d).mpr ?_⟩
  change RegularAtDim (n := n) (strictAlong (identityEmptyTail A (stableIndex g hG x)) B) q.val d
  rwa [strictAlong_identityEmptyTail hB.isClosed]

/-- A cover of the original singular locus by regular-overlap growing TESTs
extends by the identity growing sequence on the regular complement. -/
theorem intrinsic_endpoint_of_singular_cover_growing_tests
    {I : Type} (U : I → Opens X)
    (s : ∀ i, GrowingSeq (CMfd.of (n := n) (U i)))
    (hLF : ∀ i, LocallyFinite (centreImage (s i)))
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ i k, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U i → X) M)
      ((s i).stage k).2)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hSing : ∀ i k, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U i → X) ⁻¹' W))) ((s i).stage k).2)
    (hSmooth : ∀ i, IsClosedSubmanifold n
      (strictTransform n (gluedProjection (s i) (hLF i)) ((Subtype.val : U i → X) ⁻¹' W)))
    (hCover : ∀ x ∈ singularSet (n := n) W, ∃ i, x ∈ U i)
    (hRegular : ∀ ⦃i j⦄, i ≠ j →
      Disjoint (singularSet (n := n) W) ((U i : Set X) ∩ (U j : Set X))) :
    ∃ g : GrowingSeq X, ∃ hG : LocallyFinite (centreImage g),
      (∀ k, IsGeoTestTower M (g.stage k).2) ∧
      (∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W))
        (g.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection g hG) W) ∧
      limitStrictTransform g hG W = strictTransform n (gluedProjection g hG) W ∧
      IsProperMap (gluedProjection g hG) ∧ Function.Surjective (gluedProjection g hG) ∧
      ContMDiff 𝓘c 𝓘c ∞ (gluedProjection g hG : limitManifold g hG → X) ∧
      IsIsomorphismOver n (gluedProjection g hG) (singularSet (n := n) W)ᶜ := by
  let O : Opens X := ⟨(singularSet (n := n) W)ᶜ, (isClosed_singularSet hW.isClosed).isOpen_compl⟩
  let U' : Option I → Opens X
    | none => O
    | some i => U i
  let s' : ∀ i, GrowingSeq (CMfd.of (n := n) (U' i))
    | none => identityGrowingSeq (CMfd.of (n := n) O)
    | some i => s i
  let hLF' : ∀ i, LocallyFinite (centreImage (s' i))
    | none => identityGrowingSeq_locallyFinite _
    | some i => hLF i
  have hCover' (x : X) : ∃ i, x ∈ U' i := by
    by_cases hx : x ∈ singularSet (n := n) W
    · obtain ⟨i,hi⟩ := hCover x hx
      exact ⟨some i,hi⟩
    · exact ⟨none,hx⟩
  have hTest' (i : Option I) (k : ℕ) :
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U' i → X) M) ((s' i).stage k).2 := by
    cases i with
    | none => exact isGeoTestTower_of_isEmptyTower _ _ (identityEmptyTail_isEmptyTower _ k)
    | some i => exact hTest i k
  have hSing' (i : Option I) (k : ℕ) : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U' i → X) ⁻¹' W))) ((s' i).stage k).2 := by
    cases i with
    | none => exact identityGrowingSeq_stageCentres _ _ k
    | some i => exact hSing i k
  have hSmooth' (i : Option I) : IsClosedSubmanifold n
      (strictTransform n (gluedProjection (s' i) (hLF' i)) ((Subtype.val : U' i → X) ⁻¹' W)) := by
    cases i with
    | some i => exact hSmooth i
    | none =>
      apply identityGrowingSeq_strict_smooth (CMfd.of (n := n) O)
      · exact isComplexAnalyticSubset_preimage_val hW O
      · have hClosed := hW.isClosed.preimage (continuous_subtype_val (p := fun x : X => x ∈ O))
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
  exact intrinsic_endpoint_of_regular_overlap_growing_tests U' hCover' s' hLF' M hM
    hTest' W hW hSing' hSmooth' hRegular'

end Hironaka.HironakaG8GrowingSingularCoverTestLimit
