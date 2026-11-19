import Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction
import Hironaka.Analytic.Unibranch.HironakaG11HSPhaseInduction
import Hironaka.Analytic.Unibranch.OriginalIntrinsicHSSuperlevels
import Mathlib.Topology.Compactness.LocallyCompact

/-! Genuine precompact original native neighbourhoods of actual compact
shadows, without global compactness/countability/open-para inheritance.
Blueprint FIRST: original-native-precompact-neighbourhood.tex.
No dynamic centre, canonical phase or analytic structure on L is assumed. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativePrecompactNeighbourhood
noncomputable section
open Hironaka Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels HironakaG11HSPhaseInduction
  HironakaIntrinsicComplexAnalyticRegularLocus

/-- Actual closed analytic models and their genuine OPEN embeddings give compact neighbourhoods. -/
theorem weaklyLocallyCompactSpace (X : SourceReducedComplexSpace) :
    WeaklyLocallyCompactSpace X.obj.left := by
  refine ⟨fun x => ?_⟩
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint X x
  let : LocallyCompactSpace e.ambient := e.ambient.isOpen.locallyCompactSpace
  let : LocallyCompactSpace e.carrier := e.analytic.isClosed.locallyCompactSpace
  obtain ⟨L, hL, hcL⟩ := exists_compact_mem_nhds c
  refine ⟨e.toPoint '' L, hL.image e.isOpenEmbedding_toPoint.continuous, ?_⟩
  rw [← hc]
  exact e.isOpenEmbedding_toPoint.image_mem_nhds.mpr hcL

theorem locallyCompactSpace (X : SourceReducedComplexSpace) : LocallyCompactSpace X.obj.left := by
  let : T2Space X.obj.left := X.property.1
  let : WeaklyLocallyCompactSpace X.obj.left := weaklyLocallyCompactSpace X
  infer_instance

/-- The actual open V and derived compact closure, inside the actual given O. -/
structure Neighbourhood (X : SourceReducedComplexSpace) (K : Set X.obj.left) (O : Opens X.obj.left) where
  openSet : Opens X.obj.left
  compactClosure : IsCompact (closure (openSet : Set X.obj.left))
  contains : K ⊆ openSet
  closure_subset : closure (openSet : Set X.obj.left) ⊆ O

theorem exists_neighbourhood (X : SourceReducedComplexSpace) (K : Set X.obj.left)
    (hK : IsCompact K) (O : Opens X.obj.left) (hKO : K ⊆ O) : Nonempty (Neighbourhood X K O) := by
  let : T2Space X.obj.left := X.property.1
  let : LocallyCompactSpace X.obj.left := locallyCompactSpace X
  obtain ⟨L, hL, hKL, hLO⟩ := exists_compact_between hK O.isOpen hKO
  let V : Opens X.obj.left := ⟨interior L, isOpen_interior⟩
  have hcl : closure (V : Set X.obj.left) ⊆ L :=
    closure_minimal interior_subset hL.isClosed
  exact ⟨⟨V, hL.of_isClosed_subset isClosed_closure hcl, hKL, hcl.trans hLO⟩⟩

def neighbourhood (X : SourceReducedComplexSpace) (K : Set X.obj.left)
    (hK : IsCompact K) (O : Opens X.obj.left) (hKO : K ⊆ O) : Neighbourhood X K O :=
  (exists_neighbourhood X K hK O hKO).some

namespace Neighbourhood
variable {X : SourceReducedComplexSpace} {K : Set X.obj.left} {O : Opens X.obj.left}
  (N : Neighbourhood X K O)

/-- SAME literal raw native restriction; topology is derived from actual compact closure. -/
def source : SourceReducedComplexSpace :=
  OriginalRelativelyCompactRestriction.restriction X N.openSet N.compactClosure

def inclusion : N.source ⟶ X :=
  OriginalRelativelyCompactRestriction.inclusion X N.openSet N.compactClosure

instance inclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion N.inclusion.hom.left :=
  OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X N.openSet N.compactClosure

theorem inclusion_scalar : N.inclusion.hom.left ≫ X.obj.hom = N.source.obj.hom :=
  Over.w N.inclusion.hom

theorem inclusion_point (y : N.source.obj.left) : N.inclusion.hom.left.base y = y.val := rfl

theorem inclusion_range : range N.inclusion.hom.left.base = (N.openSet : Set X.obj.left) :=
  OriginalRelativelyCompactRestriction.inclusion_range X N.openSet N.compactClosure

theorem preimage_regular : N.inclusion.hom.left.base ⁻¹' intrinsicRegularLocus X.obj =
    intrinsicRegularLocus N.source.obj :=
  OriginalRelativelyCompactRestriction.inclusion_preimage_intrinsicRegularLocus X N.openSet N.compactClosure

theorem preimage_singular : N.inclusion.hom.left.base ⁻¹' intrinsicSingularLocus X.obj =
    intrinsicSingularLocus N.source.obj :=
  OriginalRelativelyCompactRestriction.inclusion_preimage_intrinsicSingularLocus X N.openSet N.compactClosure

/-- The SAME actual inverse K, not an independently chosen compact model. -/
def shadow : Set N.source.obj.left := N.inclusion.hom.left.base ⁻¹' K

theorem shadow_compact (hK : IsCompact K) : IsCompact N.shadow := by
  change IsCompact ((Subtype.val : N.openSet → X.obj.left) ⁻¹' K)
  exact Topology.IsInducing.subtypeVal.isCompact_preimage' hK
    (fun x hx => ⟨⟨x, N.contains hx⟩, rfl⟩)

theorem shadow_image : N.inclusion.hom.left.base '' N.shadow = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, N.contains hx⟩, hx, rfl⟩

theorem hs (y : N.source.obj.left) :
    originalStalkHS X (N.inclusion.hom.left.base y) = originalStalkHS N.source y :=
  originalStalkHS_openImmersion N.inclusion N.inclusion_isOpenImmersion y

theorem preimage_threshold (H : ℕ → ℕ) :
    N.inclusion.hom.left.base ⁻¹' originalSingularHSThreshold X H =
      originalSingularHSThreshold N.source H := by
  ext y
  have hs : N.inclusion.hom.left.base y ∈ intrinsicSingularLocus X.obj ↔
      y ∈ intrinsicSingularLocus N.source.obj := Set.ext_iff.mp N.preimage_singular y
  change (N.inclusion.hom.left.base y ∈ intrinsicSingularLocus X.obj ∧
      ∀ ℓ, H ℓ ≤ originalStalkHS X (N.inclusion.hom.left.base y) ℓ) ↔
    (y ∈ intrinsicSingularLocus N.source.obj ∧ ∀ ℓ, H ℓ ≤ originalStalkHS N.source y ℓ)
  rw [hs, N.hs y]

end Neighbourhood
end
end Hironaka.Analytic.Unibranch.OriginalNativePrecompactNeighbourhood
