import Hironaka.Resolution.HironakaG8FiniteSingularTowerMerge
import Hironaka.Resolution.HironakaActualLocallyFiniteLimitStrictTransforms

/-! Complete finite TESTs on stable windows of a locally finite growing TEST. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8StableWindowTest

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaBaseChange HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8FiniteSingularTowerMerge MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X : CMfd.{0} n}

/-- At a stable index, the literal open restriction of a growing TEST
is a completed finite TEST for the same restricted initial data. -/
theorem stable_window_completed_test
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s)) (x : X)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : ∀ k, IsGeoTestTower M (s.stage k).2)
    (W : Set X)
    (hSing : ∀ k, StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj W)) (s.stage k).2)
    (hSmooth : IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W)) :
    let O := stableWindow s hLF x
    let N := stableIndex s hLF x
    let T := restrict O (s.stage N).2
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : O → X) M) T ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj ((Subtype.val : O → X) ⁻¹' W))) T ∧
      IsClosedSubmanifold n (strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)) := by
  let O := stableWindow s hLF x
  let N := stableIndex s hLF x
  let T := restrict O (s.stage N).2
  refine ⟨MarkedIdealRestrictOpen.isGeoTestTower_restrict O
    hM.isClosedSubmanifold_N hM.isCoherent (s.stage N).2 (hTest N),
    singular_stages_restrict W O (s.stage N).2 (hSing N), ?_⟩
  let V := limitWindow s hLF O
  let e := stableWindowDiffeomorph s hLF x
  let j : localEndpoint s hLF x → limitManifold s hLF :=
    actualHistoryLocalInclusion s hLF x
  have hComm (y : localEndpoint s hLF x) :
      gluedProjection s hLF (j y) = (T.proj y).val := by
    change gluedProjection s hLF (actualHistoryLocalInclusion s hLF x y) = _
    rw [gluedProjection_local, proj_restrict]
    rfl
  rw [strictTransform_preimage_eq (gluedProjection_contMDiff s hLF) T.contMDiff_proj
    (isOpenHoloEmbedding_val O) (isOpenHoloEmbedding_localInclusion s hLF x) hComm]
  change IsClosedSubmanifold n (e ⁻¹' ((Subtype.val : V → limitManifold s hLF) ⁻¹'
    strictTransform n (gluedProjection s hLF) W))
  exact (isClosedSubmanifold_preimage_iff e).mpr
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hSmooth V)

end Hironaka.HironakaG8StableWindowTest
