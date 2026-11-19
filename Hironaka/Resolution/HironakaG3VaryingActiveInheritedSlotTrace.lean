import Hironaka.Resolution.HironakaG3VaryingActiveInheritedOldSlot
import Hironaka.Resolution.HironakaG3DisjointSortedChartWindow
import Hironaka.Resolution.HironakaG3GenericChartBoundaryReadout
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingActiveInheritedSlotTrace
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower HomogenizedGlueingTower
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3IndexedContainingBoundary
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry
  HironakaG3DisjointSortedChartWindow HironakaG3VaryingActiveInheritedOldSlot HironakaG3GenericChartBoundaryReadout
  HironakaG3EmptyAwareFullBoundary HironakaG3RPureEmbedded HironakaDisjointFiniteControlledHistory

theorem varying_inherited_trace_is_selected_slot {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
        (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
          r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i))
    {P : Z → X} (hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P)
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (j : κ) (hTrace : (strictTransform n P (D j) ∩ c.V).Nonempty) :
    strictTransform n P (D j) ∩ c.V ∈
      chartBoundaryOfList c (((disjointSortedChartWindow C D W K hD hGeo c).sort (· ≤ ·)).map D) := by
  let L := disjointSortedChartWindow C D W K hD hGeo c
  let E := (L.sort (· ≤ ·)).map D
  let J := GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X))
  let M := fullMarked (E.map ((Subtype.val : c.U → X) ⁻¹' ·)) J
  have hOld := varying_active_inherited_old_slot C r D hC hLF hD hr hpure W K hCentres hP c j
  have hMeet : (D j ∩ (c.U : Set X)).Nonempty := by
    obtain ⟨z,hzD,hzV⟩ := hTrace
    have hzPre := HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.continuous (hD.2.1 j) hzD
    exact ⟨P z,hzPre,by rw [c.V_eq] at hzV; exact hzV⟩
  have hE : (Subtype.val : c.U → X) ⁻¹' D j ∈ M.E := by
    change _ ∈ E.map ((Subtype.val : c.U → X) ⁻¹' ·)
    apply List.mem_map.mpr
    refine ⟨D j,?_,rfl⟩
    apply List.mem_map.mpr
    exact ⟨j,by simpa [L] using (disjoint_sorted_chart_window_spec C D W K hD hGeo c).1 j hMeet,rfl⟩
  have hSlot : strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' D j) ∈ (geoTransformAlong M c.T).E := by
    rw [boundary_decomp]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_,hE,rfl⟩)
  have hImage : chartIncl c '' (strictAlong c.T ((Subtype.val : c.U → X) ⁻¹' D j)) =
      strictTransform n P (D j) ∩ c.V := by
    rw [hOld,Set.image_preimage_eq_inter_range,range_chartIncl]
  unfold chartBoundaryOfList
  change _ ∈ (geoTransformAlong M c.T).E.map (chartIncl c '' ·)
  rw [← hImage]
  exact List.mem_map.mpr ⟨_,hSlot,rfl⟩
end
end Hironaka.HironakaG3VaryingActiveInheritedSlotTrace
