import Hironaka.Resolution.HironakaG3IndexedMixedChartBoundary
import Hironaka.Resolution.HironakaG3REmbeddedGlobalSNC
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedMixedChartGeometry
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3IndexedMixedGluing
  HironakaG3IndexedMixedChartBoundary
variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
variable (V : ι → ClosedIrreducibleAnalyticSubvariety n X) (D : κ → Set X)

theorem mixed_chart_boundary_subset (c : TowerChart (indexedMixedClass V D) Z P)
    (Ef : List (Set c.Y)) {H : Set Z} (hH : H ∈ mixedChartBoundary V D c Ef) : H ⊆ c.V := by
  obtain ⟨K,_,rfl⟩ := List.mem_map.mp hH
  rintro _ ⟨y,_,rfl⟩
  exact (c.φ y).2

theorem mixed_chart_boundary_map_val (c : TowerChart (indexedMixedClass V D) Z P)
    (Ef : List (Set c.Y)) :
    (mixedChartBoundary V D c Ef).map ((Subtype.val : c.V → Z) ⁻¹' ·) =
      Ef.map (c.φ.symm ⁻¹' ·) := by
  unfold mixedChartBoundary
  rw [List.map_map]
  congr 1
  funext H
  ext v
  simp only [Function.comp_apply, mem_preimage, mem_image]
  constructor
  · rintro ⟨y,hy,hyv⟩
    have hv : c.φ y = v := Subtype.ext hyv
    rw [← hv,c.φ.symm_apply_apply]
    exact hy
  · intro hv
    exact ⟨c.φ.symm v,hv,by rw [chartIncl_symm]⟩

theorem mixed_chart_boundary_snc (c : TowerChart (indexedMixedClass V D) Z P)
    (Ef : List (Set c.Y)) (hSNC : IsSNCDivisor n Ef) :
    IsSNCDivisor n ((mixedChartBoundary V D c Ef).map ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
  rw [mixed_chart_boundary_map_val V D]
  exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff c.φ.symm).mpr hSNC
end
end Hironaka.HironakaG3IndexedMixedChartGeometry
