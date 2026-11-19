import Hironaka.Resolution.HironakaG3EmptyAwareBornSlots
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
import Hironaka.Resolution.HironakaG3RPureEmbedded
import Hironaka.Resolution.HironakaG3GluedClassFootprint
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BornChartFootprint
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG3RTowerClass HironakaG3RPureEmbedded
  HironakaDisjointFiniteControlledHistory
  HironakaG3EmptyAwareBornSlots HironakaG3EmptyAwareFullBoundary HironakaEmbeddedBoundary
  HironakaPrincipalizationBoundary RestrictEmptyTower

/-- Every literal born slot of an actual tower chart lies over any set
containing the images of all of that tower's centres. -/
theorem born_chart_image_subset_of_centresOver {n : ℕ} {X Z : CMfd.{0} n}
    {𝒞 : LocalTowerClass X} {P : Z → X} (c : TowerChart 𝒞 Z P) (F : Set X)
    (hOver : CentresOver ((Subtype.val : c.U → X) ⁻¹' F) c.T)
    {H : Set c.Y} (hH : H ∈ bornAlong c.T) : chartIncl c '' H ⊆ P ⁻¹' F := by
  let M := fullMarked ([] : List (Set c.U)) (vanishingIdeal (n := n) (∅ : Set c.U))
  have hBorn : (exceptionalDivisor c.T).support = ⋃ H ∈ bornAlong c.T, H := by
    have hh := support_exceptionalDivisor_eq_biUnion_drop M (by simp [M,fullMarked]) c.T
    have hE : (geoTransformAlong M c.T).E = bornAlong c.T := by rw [boundary_decomp]; rfl
    change (exceptionalDivisor c.T).support = ⋃ H ∈ (geoTransformAlong M c.T).E.drop 0, H at hh
    rw [List.drop_zero,hE] at hh
    exact hh
  have hSupport := support_exceptionalDivisor_subset_of_centresOver ((Subtype.val : c.U → X) ⁻¹' F) c.T hOver
  rintro _ ⟨y,hy,rfl⟩
  have hyBorn : y ∈ ⋃ H ∈ bornAlong c.T, H := mem_iUnion₂.mpr ⟨H,hH,hy⟩
  have hyF := hSupport (hBorn.symm ▸ hyBorn)
  show P (chartIncl c y) ∈ F
  rw [proj_chartIncl c y]
  exact hyF
end
end Hironaka.HironakaG3BornChartFootprint
