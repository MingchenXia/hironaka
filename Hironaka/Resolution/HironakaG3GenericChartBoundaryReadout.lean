import Hironaka.Resolution.HironakaG3SeparatedVisibleChartBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3GenericChartBoundaryReadout
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaDisjointFiniteControlledHistory HironakaG3RTowerClass HironakaG3RPureEmbedded

variable {n : ℕ} {X Z : CMfd.{0} n} {𝒞 : LocalTowerClass X} {P : Z → X}

def chartBoundaryOfList (c : TowerChart 𝒞 Z P) (E : List (Set X)) : List (Set Z) :=
  let J := GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X))
  (geoTransformAlong (fullMarked (E.map ((Subtype.val : c.U → X) ⁻¹' ·)) J) c.T).E.map (chartIncl c '' ·)

theorem chart_boundary_of_list_subset (c : TowerChart 𝒞 Z P) (E : List (Set X))
    {H : Set Z} (hH : H ∈ chartBoundaryOfList c E) : H ⊆ c.V := by
  obtain ⟨K,_,rfl⟩ := List.mem_map.mp hH
  rintro _ ⟨y,_,rfl⟩
  exact (c.φ y).2

theorem chart_boundary_of_list_map_val (c : TowerChart 𝒞 Z P) (E : List (Set X)) :
    (chartBoundaryOfList c E).map ((Subtype.val : c.V → Z) ⁻¹' ·) =
      (geoTransformAlong (fullMarked (E.map ((Subtype.val : c.U → X) ⁻¹' ·))
        (GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X)))) c.T).E.map
          (c.φ.symm ⁻¹' ·) := by
  unfold chartBoundaryOfList
  rw [List.map_map]
  congr 1
  funext H
  ext v
  simp only [Function.comp_apply,mem_preimage,mem_image]
  constructor
  · rintro ⟨y,hy,hyv⟩
    have hv : c.φ y = v := Subtype.ext hyv
    rw [← hv,c.φ.symm_apply_apply]
    exact hy
  · intro hv
    exact ⟨c.φ.symm v,hv,by rw [chartIncl_symm]⟩
end
end Hironaka.HironakaG3GenericChartBoundaryReadout
