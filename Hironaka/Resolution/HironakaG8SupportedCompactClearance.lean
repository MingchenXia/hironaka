import Hironaka.Resolution.HironakaG8ClosedSupportedGrowingExtension
import Hironaka.Resolution.HironakaG8CompactStageLimit
import Hironaka.Resolution.HironakaG8ClosedNativeTestGlobalization

/-! Every compact task in a completed supported growing TEST has a finite ambient continuation. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8SupportedCompactClearance

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism RestrictEmptyTower ResolutionInvariantSeq
  HironakaEmbeddedAnalytic HironakaStageCenters AnalyticSubsetOpens
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaLocallyFiniteResolutionSequence HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaG8ClosedSupportedGrowingExtension HironakaG8CompactStageLimit
  HironakaG8ClosedNativeTestGlobalization

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

/-- The same ambient extension of a supported completed local TEST
clears the entire compact task at every sufficiently late finite stage. -/
theorem exists_compact_clearance_in_supported_growing_test
    {m : ℕ} {X : CMfd.{0} (m+1)}
    (U : Opens X) (F : Set X) (hF : IsClosed F) (hFU : F ⊆ U)
    (s : GrowingSeq (CMfd.of (n := m+1) U)) (hLF : LocallyFinite (centreImage s))
    (hImages : ∀ i, centreImage s i ⊆ (Subtype.val : U → X) ⁻¹' F)
    (M : MarkedIdeal (m+1) X) (hM : M.IsWellFormed)
    (hTest : ∀ i, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (s.stage i).2)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := m+1) W)
    (hSing : ∀ i, StageCentres (fun P C => C ⊆ singularSet (n := m+1)
      (strictTransform (m+1) P.proj ((Subtype.val : U → X) ⁻¹' W))) (s.stage i).2)
    (hSmooth : IsClosedSubmanifold (m+1)
      (strictTransform (m+1) (gluedProjection s hLF) ((Subtype.val : U → X) ⁻¹' W)))
    (K : Set X) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : GrowingSeq X, LocallyFinite (centreImage g) ∧
      (∀ i, CentresOver F (g.stage i).2) ∧
      (∀ i, IsGeoTestTower M (g.stage i).2) ∧
      (∀ i, StageCentres (fun P C => C ⊆ singularSet (n := m+1)
        (strictTransform (m+1) P.proj W)) (g.stage i).2) ∧
      ∃ N : ℕ, ∀ i ≥ N,
        Disjoint (singularSet (n := m+1) (strictTransform (m+1) (g.stage i).2.proj W))
          ((g.stage i).2.proj ⁻¹' K) := by
  let MU := MarkedIdeal.pullback (Subtype.val : U → X) M
  let WU := (Subtype.val : U → X) ⁻¹' W
  let KU := (Subtype.val : U → X) ⁻¹' K
  have hKUCompact : IsCompact KU :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (fun x hx => ⟨⟨x,hKU hx⟩,rfl⟩)).mpr hK
  obtain ⟨N,hClear⟩ := exists_compact_task_cleared_at_finite_stage s hLF MU
    (MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM U) hTest WU
    (isComplexAnalyticSubset_preimage_val hW U) hSing hSmooth KU hKUCompact
  obtain ⟨g,hG,hSupport,hGeo,hStage,hLocal,_,_,_,_,_,_⟩ :=
    exists_supported_growing_test_extension U F hF hFU s hLF hImages M hM hTest W hW hSing
  refine ⟨g,hG,hSupport,hGeo,hStage,N,fun i hi => ?_⟩
  obtain ⟨e,he⟩ := hLocal i
  have hProj (z : (s.stage i).1) : (g.stage i).2.proj (e z).val = ((s.stage i).2.proj z).val :=
    (proj_restrict U (g.stage i).2 (e z)).symm.trans (congrArg Subtype.val (he.proj_comm z)).symm
  exact singular_fibre_clear_of_extension_iso W hW.isClosed K U hKU (g.stage i).2
    (s.stage i).2 e he hProj (hClear i hi).symm

end Hironaka.HironakaG8SupportedCompactClearance
