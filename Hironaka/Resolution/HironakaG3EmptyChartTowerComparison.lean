import Hironaka.Resolution.HironakaG3EmptyChartPhysicalComparison
import Hironaka.Resolution.HironakaG3RTowerClass
import Hironaka.Resolution.HironakaOriginalOldBranchEmptyProjection
import Hironaka.Invariant.MaxLocusLocal
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EmptyChartTowerComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HironakaG3RTowerClass
  MaxLocusLocal RestrictEmptyTower HironakaOriginalOldBranchEmptyProjection
open ResolutionInvariantExt (IsEmptyTower)

theorem empty_chart_tower_comparison {n : ℕ} {Z Y B : CMfd.{0} n}
    (A : Opens Z) {σ : Y → Z} (𝒞 : LocalTowerClass Z) (c : TowerChart 𝒞 Y σ)
    (hcA : c.U ≤ A) (hEmpty : IsEmptyTower c.T)
    (M : BlowupTower (CMfd.of (n := n) A) B) (F : Set A) (hM : CentresOver F M)
    (hDis : Disjoint (nestedOpens A c.U : Set A) F) :
    ∃ e : (CMfd.of (n := n) (openPreimage M (nestedOpens A c.U))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ c.Y,
      ∀ z, ((c.T.proj (e z) : c.U) : Z) = ((M.proj z.val : A) : Z) := by
  obtain ⟨e,he⟩ := HironakaG3EmptyChartPhysicalComparison.empty_chart_physical_comparison
    A 𝒞 c hcA hEmpty M F hM hDis
  refine ⟨e,?_⟩
  intro z
  have hh := congrArg Subtype.val (HironakaG3EmptyAwareHistory.emptyAware_proj_comm he z)
  change ((c.T.proj (e z) : c.U) : Z) =
    ((((restrict (nestedOpens A c.U) M).proj z : nestedOpens A c.U) : A) : Z) at hh
  have hp := congrArg Subtype.val (proj_restrict (nestedOpens A c.U) M z)
  exact hh.trans hp
end
end Hironaka.HironakaG3EmptyChartTowerComparison
