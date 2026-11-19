import Hironaka.Resolution.HironakaG3SeparatedVisibleChartBoundary
import Hironaka.Resolution.HironakaG8P1ArcPair
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedVisibleChartSNC
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace NormalCrossingsInvariance
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3IndexedContainingBoundary
  HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows HironakaG3IndexedAvoidingBoundaryClass
  HironakaG3RBoundaryEmbedded HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas
  HironakaG3SeparatedVisibleChartWindow HironakaG3SeparatedVisibleChartBoundary HironakaDisjointFiniteControlledHistory
open ResolutionInvariantExt (IsEmptyTower isGeoTestTower_of_isEmptyTower)

theorem separated_visible_chart_boundary_snc {n : ℕ} {X Z : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (W : ι → Opens X) {P : Z → X}
    (c : TowerChart (finiteVisibleClass (disjointWindowClass C W
      (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) D) Z P) :
    IsSNCDivisor n ((separatedVisibleChartBoundary C r D W c).map ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
  let R := separatedChartWindow C r D W c
  let E := (R.sort (· ≤ ·)).map D
  let E₀ := E.map ((Subtype.val : c.U → X) ⁻¹' ·)
  let J := GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (∅ : Set X))
  have hChoice := separated_chart_window_spec C r D W c
  change (∀ j, (D j ∩ (c.U : Set X)).Nonempty → j ∈ R) ∧
    ((∃ i, c.U ≤ W i ∧ bdryClass (C i) (r i) E c.U c.Y c.T) ∨
      ((c.U : Set X) ⊆ (⋃ i, C i)ᶜ ∧ IsEmptyTower c.T)) at hChoice
  have hE : IsSNCDivisor n E := sorted_boundary_snc D hD R
  have hE₀ : IsSNCDivisor n E₀ :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage (pullsBackCoordinates_val c.U) continuous_subtype_val hE
  have hSNC : IsSNCDivisor n (geoTransformAlong (fullMarked E₀ J) c.T).E := by
    rcases hChoice.2 with ⟨i,_hU,hStop⟩ | ⟨_hAvoid,hEmpty⟩
    · have hAvoid : C i ⊆ closure (C i \ ⋃ H ∈ E, H) := by
        apply (dense_off_residual_family (C i) D (hC i) hD).trans
        apply closure_mono
        rintro x ⟨hxC,hxOut⟩
        refine ⟨hxC,?_⟩
        intro hxB
        obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hH
        have hjS : j ∉ containingLabels (C i) D (hC i).nonempty hD.1 := by rw [hS i]; simp
        exact hxOut (mem_iUnion.mpr ⟨⟨j,hjS⟩,hxH⟩)
      have hg := bdry_stopped_geometry (hC i).analytic (hr i) (hpure i) hE hAvoid c.U c.T hStop
      have heq := transformed_boundary_independent_of_ideal E₀ J
        (GermIdeal.pullback (m := n) (Subtype.val : c.U → X) (vanishingIdeal (n := n) (C i))) c.T
      rw [heq]
      exact hg.1
    · exact HironakaG8P1ArcPair.isSNCDivisor_geoTransformAlong hE₀ c.T
        (isGeoTestTower_of_isEmptyTower (fullMarked E₀ J) c.T hEmpty)
  rw [separated_visible_chart_boundary_map_val]
  exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff c.φ.symm).mpr hSNC
end
end Hironaka.HironakaG3SeparatedVisibleChartSNC
