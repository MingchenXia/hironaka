import Hironaka.Resolution.HironakaG3GenericBornChartOverlap
import Hironaka.Resolution.HironakaG3DisjointSortedChartGeometry
import Hironaka.Resolution.HironakaG3BornChartFootprint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointBornChartGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms NormalCrossings
  NormalCrossingsComparison HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry
  HironakaG3DisjointSortedChartWindow HironakaG3DisjointSortedChartGeometry HironakaG3GenericChartBoundaryReadout
  HironakaG3GenericBornChartOverlap HironakaG3BornChartFootprint HironakaG3EmptyAwareBornSlots
  HironakaG3EmptyAwareFullBoundary RestrictEmptyTower

/-- The born list is a literal sublist of the selected full boundary. -/
theorem disjoint_born_chart_sublist {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (A : ι → Set X) (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (A i) D (K i)) {P : Z → X}
    (c : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P) :
    (bornChartBoundary c).Sublist
      (chartBoundaryOfList c (((disjointSortedChartWindow A D W K hD hGeo c).sort (· ≤ ·)).map D)) := by
  unfold bornChartBoundary chartBoundaryOfList
  apply List.Sublist.map
  rw [boundary_decomp]
  exact List.sublist_append_right _ _

/-- Every actual born chart member lies in the same chart open. -/
theorem disjoint_born_chart_subset {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (A : ι → Set X) (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (A i) D (K i)) {P : Z → X}
    (c : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P) {H : Set Z}
    (hH : H ∈ bornChartBoundary c) : H ⊆ c.V :=
  chart_boundary_of_list_subset c _ ((disjoint_born_chart_sublist A D hD W K hGeo c).subset hH)

/-- Its born sublist retains SNC from the actual selected full window. -/
theorem disjoint_born_chart_snc {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (A : ι → Set X) (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (A i) D (K i)) {P : Z → X}
    (c : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P) :
    IsSNCDivisor n ((bornChartBoundary c).map ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
  exact isSNCDivisor_of_sublist (disjoint_sorted_chart_boundary_snc A D hD W K hGeo c)
    ((disjoint_born_chart_sublist A D hD W K hGeo c).map _)

/-- Actual centres-over-component give the born chart slots their footprint. -/
theorem disjoint_born_chart_over_component {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*}
    (A F : ι → Set X) (D : κ → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' F i) T) {P : Z → X}
    (i : ι) (c : TowerChart (finiteVisibleClass (disjointWindowClass A W K) D) Z P)
    (hK : K i c.U c.Y c.T) {H : Set Z} (hH : H ∈ bornChartBoundary c) : H ⊆ P ⁻¹' F i := by
  obtain ⟨H',hH',rfl⟩ := List.mem_map.mp hH
  exact born_chart_image_subset_of_centresOver c (F i) (hCentres i c.U c.Y c.T hK) hH'
end
end Hironaka.HironakaG3DisjointBornChartGeometry
