import Hironaka.Resolution.HironakaG3GenericChartExactSupport
import Hironaka.Resolution.HironakaG3BoundaryDivisorBoundClass
import Hironaka.Resolution.HironakaG3ContainedExceptionalDivisorBound
import Hironaka.Resolution.HironakaG3DisjointSortedChartWindow
import Hironaka.Resolution.HironakaG3TopContactEmptyClass
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointSortedChartExactSupport
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings RestrictEmptyTower
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3DisjointLocalTowerAtlas
  HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry HironakaG3DisjointSortedChartWindow
  HironakaG3GenericChartBoundaryReadout HironakaG3GenericChartExactSupport HironakaG3BoundaryDivisorBoundClass
  HironakaG3ContainedExceptionalDivisorBound HironakaG3TopContactEmptyClass

/-- Actual class-member divisor bounds and the complement's empty tower
supply the exact support of the selected sorted chart boundary. -/
theorem disjoint_sorted_chart_exact_support {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (A : ι → Set X) (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hBound : ∀ i, HasBoundaryDivisorBound D (K i))
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (A i) D (K i)) {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P) :
    (⋃ H ∈ chartBoundaryOfList c (((disjointSortedChartWindow A D W K hD hGeo c).sort (· ≤ ·)).map D), H) =
      (P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P) ∩ c.V := by
  let R := disjointSortedChartWindow A D W K hD hGeo c
  have hDiv : (exceptionalDivisor c.T).support ⊆
      c.T.proj ⁻¹' ((Subtype.val : c.U → X) ⁻¹' (⋃ j, D j)) ∪ exceptionalLocus n c.T.proj := by
    rcases c.mem.1 with ⟨i,_hUW,hK⟩ | ⟨_hAvoid,hEmpty⟩
    · exact hBound i c.U c.Y c.T hK
    · have hOver := empty_tower_class_centres_over (∅ : Set X) c.U c.Y c.T hEmpty
      exact exceptional_divisor_bound_of_centres_over_boundary (⋃ j, D j) ∅ (empty_subset _) c.U c.T hOver
  apply chart_boundary_exact_support_of_exceptional_divisor_bound D hD.2.1 hP c ((R.sort (· ≤ ·)).map D) ?_ ?_ hDiv
  · intro H hH
    obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hH
    exact ⟨j,rfl⟩
  · intro j hj
    apply List.mem_map.mpr
    exact ⟨j,by simpa [R] using (disjoint_sorted_chart_window_spec A D W K hD hGeo c).1 j hj,rfl⟩
end
end Hironaka.HironakaG3DisjointSortedChartExactSupport
