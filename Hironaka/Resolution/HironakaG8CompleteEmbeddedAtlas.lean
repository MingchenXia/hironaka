import Hironaka.Resolution.HironakaG8IsolatedCompactSingularAtlas
import Hironaka.Resolution.HironakaG3GenericBornChartOverlap
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
import Hironaka.Resolution.HironakaResolutionSpaceLocal

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8CompleteEmbeddedAtlas

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings MarkedIdealTowerTransport HironakaEmbeddedAnalytic HironakaStageCenters
  HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaG8IsolatedCompactSingularAtlas HironakaG8SurfaceLimitEndpoint
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3DisjointAtlasCommonGood
  HironakaG3GenericBornChartOverlap HironakaG3EmptyAwareBornSlots HironakaG3EmptyAwareFullBoundary
  HironakaResolutionSpaceLocal

private abbrev emptyInitialRecord {n : ℕ} {X : CMfd.{0} n} (W : Set X) : MarkedIdeal n X :=
  ⟨univ, [], vanishingIdeal (n := n) W, 1⟩

/-- A complete actual embedded history with empty initial boundary. -/
structure CompleteEmbeddedHistory {n : ℕ} {X Y : CMfd.{0} n} (W : Set X) (T : BlowupTower X Y) : Prop where
  positions : EmbeddedPositions W T
  smooth : IsClosedSubmanifold n (strictTransform n T.proj W)
  snc : IsSNCDivisor n (bornAlong T)
  nc : HasNormalCrossings n (strictTransform n T.proj W) (bornAlong T)

/-- Read completeness from the literal geometric list of an empty-boundary history. -/
theorem completeEmbeddedHistory_of_empty_initial {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}
    {T : BlowupTower X Y} (hPos : EmbeddedPositions W T) (hSmooth : IsClosedSubmanifold n (strictTransform n T.proj W))
    (hSNC : IsSNCDivisor n (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E)
    (hNC : HasNormalCrossings n (strictTransform n T.proj W)
      (geoTransformAlong (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).E) :
    CompleteEmbeddedHistory W T := by
  have hE : (geoTransformAlong (emptyInitialRecord W) T).E = bornAlong T := by
    rw [boundary_decomp]
    rfl
  exact ⟨hPos,hSmooth,hE ▸ hSNC,hE ▸ hNC⟩

/-- Every member of the given class is complete on its actual open carrier. -/
def ClassHasCompleteEmbeddedHistories {n : ℕ} {X : CMfd.{0} n} (W : Set X) (K : LocalTowerClass X) : Prop :=
  ∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
    K U Y T → CompleteEmbeddedHistory ((Subtype.val : U → X) ⁻¹' W) T

/-- Terminal geometry is carried by the given glued projection and its actual charts. -/
structure CompleteEmbeddedAtlas {n : ℕ} {X Z : CMfd.{0} n} (W : Set X) (K : LocalTowerClass X)
    (P : Z → X) : Prop where
  glued : IsGluedFrom K Z P
  regularIso : IsIsomorphismOver n P (singularSet (n := n) W)ᶜ
  smooth : IsClosedSubmanifold n (strictTransform n P W)
  image_eq : P '' strictTransform n P W = W
  exceptional_eq : exceptionalLocus n P = P ⁻¹' singularSet (n := n) W
  actualHistory : ∀ c : TowerChart K Z P, CompleteEmbeddedHistory ((Subtype.val : c.U → X) ⁻¹' W) c.T
  chartGeometry : ∀ c : TowerChart K Z P,
    IsSNCDivisor n ((bornChartBoundary c).map ((Subtype.val : c.V → Z) ⁻¹' ·)) ∧
    HasNormalCrossings n ((Subtype.val : c.V → Z) ⁻¹' strictTransform n P W)
      ((bornChartBoundary c).map ((Subtype.val : c.V → Z) ⁻¹' ·)) ∧
    (⋃ H ∈ bornChartBoundary c, H) = (c.V : Set Z) ∩ exceptionalLocus n P

private theorem born_boundary_support {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}
    (hW : IsClosed W) {T : BlowupTower X Y} (h : CompleteEmbeddedHistory W T) :
    (⋃ H ∈ bornAlong T, H) = exceptionalLocus n T.proj := by
  let M := emptyInitialRecord W
  have hB : (geoTransformAlong M T).E = bornAlong T := by
    rw [boundary_decomp]
    rfl
  have hAdm := (embedded_positions_centres_over hW T h.positions).2
  have hIso := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm
  have hExc := exceptionalLocus_eq_singular_preimage W hW T.proj T.contMDiff_proj hIso h.smooth
  apply Subset.antisymm
  · rw [← hB,hExc]
    simpa using HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.biUnion_subset hAdm
      (isSNCDivisor_nil : IsSNCDivisor n ([] : List (Set X))).1
  · rw [← hB]
    exact exceptionalLocus_subset_boundary M T

private theorem chart_born_geometry {n : ℕ} {X Z : CMfd.{0} n} {W : Set X} {K : LocalTowerClass X}
    {P : Z → X} (hW : IsClosed W) (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart K Z P) (h : CompleteEmbeddedHistory ((Subtype.val : c.U → X) ⁻¹' W) c.T) :
    IsSNCDivisor n ((bornChartBoundary c).map ((Subtype.val : c.V → Z) ⁻¹' ·)) ∧
    HasNormalCrossings n ((Subtype.val : c.V → Z) ⁻¹' strictTransform n P W)
      ((bornChartBoundary c).map ((Subtype.val : c.V → Z) ⁻¹' ·)) ∧
    (⋃ H ∈ bornChartBoundary c, H) = (c.V : Set Z) ∩ exceptionalLocus n P := by
  let M := emptyInitialRecord W
  have hE : (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X) M) c.T).E =
      bornAlong c.T := by
    rw [boundary_decomp]
    rfl
  have hB : chartBoundary c M = bornChartBoundary c := by
    unfold chartBoundary bornChartBoundary
    rw [hE]
  have hList := chartBoundary_map_val c M
  rw [hB,hE] at hList
  have hCarrier : (Subtype.val : c.V → Z) ⁻¹' strictTransform n P W =
      c.φ.symm ⁻¹' strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' W) := by
    rw [strictTransform_chart c hP W]
    ext z
    change z.val ∈ strictTransform n P W ↔ chartIncl c (c.φ.symm z) ∈ strictTransform n P W
    rw [chartIncl_symm]
  refine ⟨?_,?_,?_⟩
  · rw [hList]
    exact (isSNCDivisor_map_preimage_iff c.φ.symm).mpr h.snc
  · rw [hList,hCarrier]
    exact (hasNormalCrossings_preimage_iff c.φ.symm).mpr h.nc
  · rw [bornChartBoundary,iUnion_map_image, born_boundary_support (hW.preimage continuous_subtype_val) h,
      exceptionalLocus_chart c hP,image_preimage_eq_inter_range,range_chartIncl,inter_comm]

/-- Every complete covering chart reads back on the same glued projection. -/
theorem complete_embedded_atlas_readback {n : ℕ} {X Z : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {K : LocalTowerClass X} {P : Z → X}
    (hG : IsGluedFrom K Z P) (hComplete : ClassHasCompleteEmbeddedHistories W K) :
    CompleteEmbeddedAtlas W K P := by
  have hIso : IsIsomorphismOver n P (singularSet (n := n) W)ᶜ := by
    apply glued_isomorphism_over_of_local _ hG
    intro U Y T hT
    have h := hComplete U Y T hT
    have hAdm := (embedded_positions_centres_over (hW.isClosed.preimage continuous_subtype_val) T h.positions).2
    have hLocal := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm
    rwa [singularSet_preimage_val,← preimage_compl] at hLocal
  have hSmooth : IsClosedSubmanifold n (strictTransform n P W) := by
    refine ⟨isClosed_closure,fun z hz => ?_⟩
    obtain ⟨c,hcz⟩ := hG.2.2.2 (P z)
    let v : c.V := ⟨z,c.mem_V hcz⟩
    let y : c.Y := c.φ.symm v
    have hyz : chartIncl c y = z := chartIncl_symm c v
    have hTrace := strictTransform_chart c hG.1 W
    have hy : y ∈ strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' W) := by
      rw [hTrace]
      change chartIncl c y ∈ strictTransform n P W
      rwa [hyz]
    obtain ⟨d,hd⟩ := (hComplete c.U c.Y c.T c.mem).smooth.2 y hy
    exact ⟨d,hyz ▸ regularAtDim_of_chart c (hTrace ▸ hd)⟩
  have hExc := exceptionalLocus_eq_singular_preimage W hW.isClosed P hG.1 hIso hSmooth
  have hImage : P '' strictTransform n P W = W := by
    apply Subset.antisymm
    · rintro _ ⟨y,hy,rfl⟩
      exact strictTransform_subset_preimage hG.1.continuous hW.isClosed hy
    · refine (HironakaResolutionSpace.subset_closure_diff_singularSet hW).trans
        (closure_minimal ?_ (hG.2.1.isClosedMap _ isClosed_closure))
      rintro x ⟨hxW,hxS⟩
      obtain ⟨y,hy⟩ := hG.2.2.1 x
      refine ⟨y,subset_closure ⟨?_,?_⟩,hy⟩
      · change P y ∈ W
        rwa [hy]
      · rw [hExc]
        change P y ∉ singularSet (n := n) W
        rwa [hy]
  exact ⟨hG,hIso,hSmooth,hImage,hExc,fun c => hComplete c.U c.Y c.T c.mem,
    fun c => chart_born_geometry hW.isClosed hG.1 c (hComplete c.U c.Y c.T c.mem)⟩

/-- A supplied covering class with comparisons glues to an actual complete embedded atlas. -/
theorem exists_glued_complete_embedded_atlas {n : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {K : LocalTowerClass X} (hCover : Covers K)
    (hCompare : HasComparisons K) (hComplete : ClassHasCompleteEmbeddedHistories W K) :
    ∃ (Z : CMfd.{0} n) (P : Z → X), CompleteEmbeddedAtlas W K P := by
  obtain ⟨Z,P,hG⟩ := exists_isGluedFrom hCover hCompare
  exact ⟨Z,P,complete_embedded_atlas_readback hW hG hComplete⟩

end
end Hironaka.HironakaG8CompleteEmbeddedAtlas
