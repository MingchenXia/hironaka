import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule
import Hironaka.Resolution.HironakaActualProcessedAllMasksDrop
import Hironaka.Resolution.HironakaSharpOriginalDynamicGoodPrefixes
import Hironaka.Analytic.ProperMappingTheorem
import Hironaka.Analytic.CompactAnalyticFinite

/-! An affine compact-footprint obstruction. No resolution producer is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8CompactFootprintObstruction
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  RestrictEmptyTower HironakaEmbeddedAnalytic HironakaStageCenters

/-- A finite actual tower over a compact subset of affine complex space has
one finite original centre footprint inside that same compact set. -/
theorem exists_finite_original_footprint_of_compact {n : ℕ}
    (K : Set (ComplexModel n)) (hK : IsCompact K) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) (ComplexModel n)) Y),
      CentresOver K T → ∃ F : Set (ComplexModel n), F.Finite ∧ F ⊆ K ∧ CentresOver F T
  | _, .refl, _ => ⟨∅, Set.finite_empty, empty_subset K, trivial⟩
  | _, .step T C π hπ, hOver => by
    obtain ⟨F,hF,hFK,hFT⟩ := exists_finite_original_footprint_of_compact K hK T hOver.1
    have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
    have hImage := ProperMappingTheorem.isComplexAnalyticSubset_image T.contMDiff_proj hC
      (fun A hA => ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hA).inter_left hC.isClosed)
    have hImageK : T.proj '' C ⊆ K := image_subset_iff.mpr hOver.2
    have hImageCompact : IsCompact (T.proj '' C) := hK.of_isClosed_subset hImage.isClosed hImageK
    have hImageFinite : (T.proj '' C).Finite := CompactAnalyticFinite.finite_of_isCompact hImage hImageCompact
    refine ⟨F ∪ T.proj '' C,hF.union hImageFinite,union_subset hFK hImageK,?_⟩
    exact ⟨HironakaActualProcessedAllMasksDrop.centresOver_mono_local subset_union_left T hFT,
      fun y hy => Or.inr ⟨y,hy,rfl⟩⟩

/-- A tower with compact original centre footprint can clear only finitely
many original singular points of an affine analytic carrier over any set. -/
theorem finite_original_singular_points_of_compact_footprint_service {n : ℕ}
    (W S K : Set (ComplexModel n)) (hW : IsClosed W) (hK : IsCompact K)
    {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) (ComplexModel n)) Y)
    (hOver : CentresOver K T)
    (hClear : Disjoint (singularSet (n := n) (strictTransform n T.proj W)) (T.proj ⁻¹' S)) :
    (singularSet (n := n) W ∩ S).Finite := by
  obtain ⟨F,hF,hFK,hFT⟩ := exists_finite_original_footprint_of_compact K hK T hOver
  have hIso := HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver F T hFT
  apply hF.subset
  intro x hx
  by_contra hxF
  have hxFc : x ∈ Fᶜ := hxF
  obtain ⟨y,hyF,hyx⟩ := hIso.1.2.2 hxFc
  have hyNE : y ∉ exceptionalLocus n T.proj := fun hyE => disjoint_left.mp hIso.2 hyF hyE
  have hyW : y ∈ strictTransform n T.proj W := by
    apply (HironakaAdmissibleCalculus.mem_strictTransform_iff_of_notMem T.contMDiff_proj.continuous hW hyNE).mpr
    simpa only [hyx] using (mem_singularSet_iff.mp hx.1).1
  have hySing : y ∈ singularSet (n := n) (strictTransform n T.proj W) := by
    apply mem_singularSet_iff.mpr
    refine ⟨hyW,?_⟩
    intro d hd
    have hreg := (regularAtDim_strictTransform_iff_of_notMem_exceptionalLocus T.contMDiff_proj hW hyNE d).mp hd
    exact (mem_singularSet_iff.mp hx.1).2 d (by simpa only [hyx] using hreg)
  have hyS : y ∈ T.proj ⁻¹' S := by simpa only [mem_preimage,hyx] using hx.2
  exact disjoint_left.mp hClear hySing hyS
end
end Hironaka.HironakaG8CompactFootprintObstruction
