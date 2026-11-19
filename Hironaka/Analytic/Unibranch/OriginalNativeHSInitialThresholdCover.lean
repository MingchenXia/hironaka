import Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenWindows
import Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism

/-! ENTIRE actual INITIAL HS threshold coverage of the genuine seed and
its actual native base-open refinements. Blueprint FIRST:
original-native-hs-initial-threshold-cover.tex. No final-empty-cover or
phase/comparison packet is used. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSInitialThresholdCover
noncomputable section
open SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaG11VanishingWindows OriginalNativeHSCompactShadowWindows

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)
local notation "N" => OriginalNativeShadowFirstBlowup.target M hK
local notation "F₀" => OriginalNativeShadowInvariantCentre.centres M hK

theorem seed_threshold_covered :
    originalSingularHSThreshold (N).source (originalStalkHS X M.point) ⊆
      ⋃ i, range (OriginalNativeShadowFlatWindows.window M hK i).toLocalEmbedding.toPoint := by
  intro y hy
  have hThreshold : (N).inclusion.hom.left.base y ∈ M.threshold :=
    (Set.ext_iff.mp ((N).preimage_threshold (originalStalkHS X M.point)) y).mpr hy
  have hNeighbourhood := (N).closure_subset (subset_closure y.property)
  change (N).inclusion.hom.left.base y ∈
    (OriginalNativeCentreLocalClosedness.coveredOpen F₀ : Set X.obj.left) ∪ M.thresholdᶜ at hNeighbourhood
  have hCovered := hNeighbourhood.resolve_right (fun h => h hThreshold)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hCovered
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [OriginalNativeShadowFlatWindows.range_dictionary]
  exact (Set.ext_iff.mp (OriginalNativeCentreOpenPullback.window_range F₀
    (N).inclusion (N).inclusion_isOpenImmersion i) y).mp hi

theorem pullback_threshold_covered {A B : SourceReducedComplexSpace} {n : ℕ} {ι : Type*}
    (w : ι → DimEmbedding A n) (H : ℕ → ℕ)
    (hCover : originalSingularHSThreshold A H ⊆ ⋃ i, range (w i).toLocalEmbedding.toPoint)
    (j : B ⟶ A) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    originalSingularHSThreshold B H ⊆
      ⋃ i, range (OriginalNativeHSBaseOpenWindows.window w j hj i).toLocalEmbedding.toPoint := by
  intro y hy
  have hOld : j.hom.left.base y ∈ originalSingularHSThreshold A H :=
    (Set.ext_iff.mp (OriginalNativeHSThresholdIsomorphism.threshold_preimage_openImmersion H j hj) y).mpr hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCover hOld)
  exact Set.mem_iUnion.mpr ⟨i,
    (Set.ext_iff.mp (OriginalNativeHSBaseOpenWindows.range_dictionary w j hj i) y).mp hi⟩

theorem seed_threshold_covered_on_native_open {B : SourceReducedComplexSpace}
    (j : B ⟶ (N).source) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    originalSingularHSThreshold B (originalStalkHS X M.point) ⊆
      ⋃ i, range (OriginalNativeHSBaseOpenWindows.window
        (OriginalNativeShadowFlatWindows.window M hK) j hj i).toLocalEmbedding.toPoint :=
  pullback_threshold_covered (OriginalNativeShadowFlatWindows.window M hK)
    (originalStalkHS X M.point) (seed_threshold_covered M hK) j hj

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSInitialThresholdCover
