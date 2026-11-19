import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Mathlib.Topology.Separation.Regular

/-!
# Finite original local embeddings and compact shrinking footprints

An ordinary compact original reduced complex space admits a finite cover by
the SAME `LocalEmbedding.ofPoint` model maps. Internally chosen open shrinkings
have compact closures inside those model images, compact actual inverse-model
footprints and compact literal ambient footprints. Ambient dimensions may vary.

Blueprint: `compact-original-embedding-cover.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.Analytic.Unibranch.CompactOriginalEmbeddingCover

noncomputable section

/-- Compactness selects a finite cover from the SAME original local embeddings. -/
theorem exists_finite_localEmbedding_cover (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] :
    ∃ s : Finset X.obj.left,
      (⋃ x ∈ s, range (LocalEmbedding.ofPoint X x).toPoint) = univ := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X.obj.left => range (LocalEmbedding.ofPoint X x).toPoint)
    (fun x => (LocalEmbedding.ofPoint X x).isOpen_range_toPoint)
    (by
      intro x _hx
      exact mem_iUnion.mpr ⟨x, LocalEmbedding.mem_range_ofPoint X x⟩)
  exact ⟨s, eq_univ_of_univ_subset hs⟩

private theorem exists_original_localEmbedding_shrinking
    (X : SourceReducedComplexSpace) [CompactSpace X.obj.left] (x : X.obj.left) :
    ∃ V : Set X.obj.left, IsOpen V ∧ x ∈ V ∧
      closure V ⊆ range (LocalEmbedding.ofPoint X x).toPoint ∧ IsCompact (closure V) := by
  let : T2Space X.obj.left := X.property.1
  obtain ⟨V, hVo, hxV, hVsub, hVc⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_singleton (x := x))
      (LocalEmbedding.ofPoint X x).isOpen_range_toPoint
      (singleton_subset_iff.mpr (LocalEmbedding.mem_range_ofPoint X x))
  exact ⟨V, hVo, hxV (mem_singleton x), hVsub, hVc⟩

/-- Ordinary compact original X internally produces open shrinking covers and
compact footprints under the SAME model maps, including the literal ambient image. -/
theorem exists_finite_localEmbedding_shrinking (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] :
    ∃ (V : X.obj.left → Opens X.obj.left) (s : Finset X.obj.left),
      (∀ x, x ∈ V x ∧
        closure (V x : Set X.obj.left) ⊆ range (LocalEmbedding.ofPoint X x).toPoint) ∧
      (⋃ x ∈ s, (V x : Set X.obj.left)) = univ ∧
      ∀ x,
        IsCompact (closure (V x : Set X.obj.left)) ∧
        IsCompact ((LocalEmbedding.ofPoint X x).toPoint ⁻¹'
          closure (V x : Set X.obj.left)) ∧
        (LocalEmbedding.ofPoint X x).toPoint ''
          ((LocalEmbedding.ofPoint X x).toPoint ⁻¹' closure (V x : Set X.obj.left)) =
          closure (V x : Set X.obj.left) ∧
        IsCompact ((Subtype.val : (LocalEmbedding.ofPoint X x).carrier →
          (LocalEmbedding.ofPoint X x).ambient) ''
          ((LocalEmbedding.ofPoint X x).toPoint ⁻¹' closure (V x : Set X.obj.left))) := by
  classical
  choose V hVo hxV hVsub hVc using exists_original_localEmbedding_shrinking X
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hVo
    (by
      intro x _hx
      exact mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨fun x => ⟨V x, hVo x⟩, s, ?_, ?_, ?_⟩
  · exact fun x => ⟨hxV x, hVsub x⟩
  · exact eq_univ_of_univ_subset hs
  · intro x
    have hK : IsCompact ((LocalEmbedding.ofPoint X x).toPoint ⁻¹' closure (V x)) :=
      (LocalEmbedding.ofPoint X x).isOpenEmbedding_toPoint.isEmbedding.isInducing.isCompact_preimage'
        (hVc x) (hVsub x)
    exact ⟨hVc x, hK, image_preimage_eq_of_subset (hVsub x),
      hK.image continuous_subtype_val⟩

end

end Hironaka.Analytic.Unibranch.CompactOriginalEmbeddingCover
