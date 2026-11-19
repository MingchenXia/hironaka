import Hironaka.Resolution.HironakaG3RTowerClass
import Hironaka.Resolution.HironakaOriginalOldBranchEmptyProjection
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Resolution.HironakaG3BiholomorphicFirstMeeting
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EmptyChartPhysicalComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HironakaG3RTowerClass
  MaxLocusLocal RestrictEmptyTower HironakaG3EmptyAwareHistory HironakaG3BiholomorphicFirstMeeting
open ResolutionInvariantExt (IsEmptyTower)

theorem empty_chart_physical_comparison {n : ℕ} {Z Y B : CMfd.{0} n}
    (A : Opens Z) {σ : Y → Z} (𝒞 : LocalTowerClass Z) (c : TowerChart 𝒞 Y σ)
    (hcA : c.U ≤ A) (hEmpty : IsEmptyTower c.T)
    (M : BlowupTower (CMfd.of (n := n) A) B) (F : Set A) (hM : CentresOver F M)
    (hDis : Disjoint (nestedOpens A c.U : Set A) F) :
    ∃ e : (CMfd.of (n := n) (openPreimage M (nestedOpens A c.U))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ c.Y,
      EmptyAwareTowerIso (nestedOpensDiffeo (n := n) hcA) (restrict (nestedOpens A c.U) M) c.T e := by
  have hEmptyM := isEmptyTower_restrict_of_centresOver (nestedOpens A c.U) hDis M hM
  exact emptyAware_of_empty_towers (nestedOpensDiffeo (n := n) hcA)
    (restrict (nestedOpens A c.U) M) c.T hEmptyM hEmpty
end
end Hironaka.HironakaG3EmptyChartPhysicalComparison
