import Hironaka.Resolution.HironakaG3SortedLocalWindowGeometry
import Hironaka.Resolution.HironakaG3IndexedAvoidingBoundaryClass
import Hironaka.Resolution.HironakaG3SeparatedVisibleChartSNC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AvoidingSortedWindowGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaActualLocallyFiniteBoundary
  HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3SortedLocalWindowGeometry HironakaG3RBoundaryEmbedded
  HironakaG3SeparatedVisibleChartWindow HironakaDisjointFiniteControlledHistory

theorem indexed_avoiding_sorted_local_window_geometry {n r : ℕ} {X : CMfd.{0} n}
    {κ : Type*} [LinearOrder κ] (C : Set X) (D : κ → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅) (hr : r < n)
    (hpure : C ⊆ closure (regularLocus (n := n) C r)) :
    HasSortedLocalWindowGeometry C D (indexedAvoidingBoundaryClass C r D) := by
  intro U Y T hT R _hR
  obtain ⟨L,hVis,hStop⟩ := hT
  refine ⟨L,hVis,?_⟩
  let B := (L.sort (· ≤ ·)).map D
  let J := GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) (∅ : Set X))
  have hB : IsSNCDivisor n B := sorted_boundary_snc D hD L
  have hAvoid : C ⊆ closure (C \ ⋃ H ∈ B, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hH
    have hjS : j ∉ containingLabels C D hC.nonempty hD.1 := by rw [hS]; simp
    exact hxOut (mem_iUnion.mpr ⟨⟨j,hjS⟩,hxH⟩)
  have hg := bdry_stopped_geometry hC.analytic hr hpure hB hAvoid U T hStop
  simp only [MarkedIdealBiholomorphism.MarkedIdeal.pullback,preimage_univ] at hg
  have heq := transformed_boundary_independent_of_ideal (B.map ((Subtype.val : U → X) ⁻¹' ·)) J
    (GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) C)) T
  change IsSNCDivisor n (geoTransformAlong (fullMarked (B.map ((Subtype.val : U → X) ⁻¹' ·)) J) T).E ∧
    HasNormalCrossings n (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' C))
      (geoTransformAlong (fullMarked (B.map ((Subtype.val : U → X) ⁻¹' ·)) J) T).E
  rw [heq]
  exact ⟨hg.1,hg.2.2.2.2.2.2.2.2⟩
end
end Hironaka.HironakaG3AvoidingSortedWindowGeometry
