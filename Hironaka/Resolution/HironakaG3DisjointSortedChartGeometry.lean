import Hironaka.Resolution.HironakaG3DisjointSortedChartWindow
import Hironaka.Resolution.HironakaG3GenericChartBoundaryReadout
import Hironaka.Resolution.HironakaG3RPureEmbedded
import Hironaka.Resolution.HironakaAdmissibleCalculus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3DisjointSortedChartGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3RTowerClass HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas
  HironakaG3SortedLocalWindowGeometry HironakaG3DisjointSortedChartWindow HironakaG3GenericChartBoundaryReadout
  HironakaG3RPureEmbedded

theorem disjoint_sorted_chart_boundary_snc {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i)) {P : Z → X}
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P) :
    IsSNCDivisor n ((chartBoundaryOfList c (((disjointSortedChartWindow C D W K hD hGeo c).sort (· ≤ ·)).map D)).map
      ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
  have hSNC := (disjoint_sorted_chart_window_spec C D W K hD hGeo c).2.1
  rw [chart_boundary_of_list_map_val]
  exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff c.φ.symm).mpr hSNC

theorem disjoint_sorted_chart_component_nc {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i)) (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D)
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X))
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i)) {P : Z → X}
    (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P) (i : ι) :
    HasNormalCrossings n ((Subtype.val : c.V → Z) ⁻¹' strictTransform n P (C i))
      ((chartBoundaryOfList c (((disjointSortedChartWindow C D W K hD hGeo c).sort (· ≤ ·)).map D)).map
        ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
  intro z hz
  have hzC : P z ∈ C i := HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.continuous (hC i) hz
  have hzU : P z ∈ c.U := by
    have hzV : (z : Z) ∈ ((c.V : Opens Z) : Set Z) := z.property
    rwa [c.V_eq] at hzV
  have hSpec := (disjoint_sorted_chart_window_spec C D W K hD hGeo c).2.2
  rcases hSpec with ⟨j,hUW,_hK,hNC⟩ | ⟨hAvoid,_hEmpty⟩
  · have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hWindow j i hne) hzC (hUW hzU)
    subst j
    have hst := strictTransform_chart c hP (C i)
    have hpre : (Subtype.val : c.V → Z) ⁻¹' strictTransform n P (C i) =
        c.φ.symm ⁻¹' strictTransform n c.T.proj ((Subtype.val : c.U → X) ⁻¹' C i) := by
      rw [hst]
      ext v
      change (v : Z) ∈ strictTransform n P (C i) ↔ chartIncl c (c.φ.symm v) ∈ strictTransform n P (C i)
      rw [chartIncl_symm]
    have hglobal : HasNormalCrossings n ((Subtype.val : c.V → Z) ⁻¹' strictTransform n P (C i))
        ((chartBoundaryOfList c (((disjointSortedChartWindow C D W K hD hGeo c).sort (· ≤ ·)).map D)).map
          ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
      rw [chart_boundary_of_list_map_val,hpre]
      exact (MarkedIdealTowerTransport.hasNormalCrossings_preimage_iff c.φ.symm).mpr hNC
    exact hglobal z hz
  · exact False.elim ((hAvoid hzU) (mem_iUnion.mpr ⟨i,hzC⟩))
end
end Hironaka.HironakaG3DisjointSortedChartGeometry
