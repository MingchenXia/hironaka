import Hironaka.Resolution.HironakaG3SeparatedVisibleChartWindow
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedVisibleChartBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaDisjointFiniteControlledHistory HironakaG3RTowerClass
  HironakaG3RPureEmbedded HironakaG3IndexedAvoidingBoundaryClass HironakaG3DisjointLocalTowerAtlas
  HironakaG3FiniteVisibleAtlas HironakaG3SeparatedVisibleChartWindow
variable {n : ℕ} {X : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
  (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X) {Z : CMfd.{0} n} {P : Z → X}

def separatedVisibleChartBoundary (c : TowerChart (finiteVisibleClass (disjointWindowClass C W
    (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) : List (Set Z) :=
  let R := separatedChartWindow C r D W c
  let E := (R.sort (· ≤ ·)).map D
  let J := GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X))
  (geoTransformAlong (fullMarked (E.map ((Subtype.val : c.U → X) ⁻¹' ·)) J) c.T).E.map (chartIncl c '' ·)

theorem separated_visible_chart_boundary_subset (c : TowerChart (finiteVisibleClass (disjointWindowClass C W
    (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P)
    {H : Set Z} (hH : H ∈ separatedVisibleChartBoundary C r D W c) : H ⊆ c.V := by
  obtain ⟨K,_,rfl⟩ := List.mem_map.mp hH
  rintro _ ⟨y,_,rfl⟩
  exact (c.φ y).2

theorem separated_visible_chart_boundary_map_val (c : TowerChart (finiteVisibleClass (disjointWindowClass C W
    (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) :
    (separatedVisibleChartBoundary C r D W c).map ((Subtype.val : c.V → Z) ⁻¹' ·) =
      (geoTransformAlong (fullMarked
        (((separatedChartWindow C r D W c).sort (· ≤ ·)).map D |>.map ((Subtype.val : c.U → X) ⁻¹' ·))
        (GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X)))) c.T).E.map
          (c.φ.symm ⁻¹' ·) := by
  unfold separatedVisibleChartBoundary
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
end Hironaka.HironakaG3SeparatedVisibleChartBoundary
