import Hironaka.Resolution.HironakaG3VaryingCombinedComponentSlots
import Hironaka.Resolution.HironakaG3DisjointBornCoverage
import Hironaka.Resolution.HironakaG3PhysicalClassComparisons
import Hironaka.Resolution.HironakaG3VaryingActiveInheritedOldSlot
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingCombinedExactSupport
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower HironakaDisjointFiniteControlledHistory
  HironakaG3RTowerClass HironakaActualLocallyFiniteBoundary HironakaG3REmbeddedGlobalSNC HironakaG3IndexedContainingBoundary
  HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas HironakaG3SortedLocalWindowGeometry
  HironakaG3DisjointSortedChartWindow HironakaG3GenericChartBoundaryReadout HironakaG3VaryingCombinedComponentSlots
  HironakaG3VaryingActiveInheritedOldSlot HironakaG3DisjointBornCoverage HironakaG3DisjointBornChartGeometry
  HironakaG3GenericBornChartOverlap HironakaG3PhysicalClassComparisons HironakaG3RPureEmbedded
  HironakaG3EmptyAwareFullBoundary HomogenizedGlueingTower MaxLocusLocal

theorem varying_combined_exact_support {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (hCW : ∀ i, C i ⊆ W i) (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X))
    (hSame : ∀ i, HasPhysicalComparisons (K i))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T)
    (hActiveCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
        (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
          r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i)) {P : Z → X}
    (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (hChartSupport : ∀ c : TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P,
      (⋃ H ∈ chartBoundaryOfList c (((disjointSortedChartWindow C D W K hD hGeo c).sort (· ≤ ·)).map D), H) =
        (P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P) ∩ c.V)
    (c : ι → ℕ → TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (varyingComponentWindow C D W K hG i)))
    (hExW : ∀ i k, (Ex i).W k = nestedOpens (varyingComponentWindow C D W K hG i) (c i k).V)
    (hExB : ∀ i k, (Ex i).B k = (bornChartBoundary (c i k)).map
      ((Subtype.val : varyingComponentWindow C D W K hG i → Z) ⁻¹' ·)) :
    (⋃ a, varyingCombinedBoundary C D W K hG Ex a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P := by
  let Q := varyingComponentWindow C D W K hG
  ext z
  constructor
  · intro hz
    obtain ⟨a,ha⟩ := mem_iUnion.mp hz
    cases a with
    | inl j =>
      left
      exact mem_iUnion.mpr ⟨j,HironakaAdmissibleCalculus.strictTransform_subset_preimage hG.1.continuous (hD.2.1 j) ha⟩
    | inr p =>
      rcases p with ⟨i,b⟩
      obtain ⟨x,hxB,rfl⟩ := ha
      obtain ⟨k,hxW⟩ := (Ex i).cover x
      have hTrace := b.2.mem_of_nonempty (Ex i) k ⟨x,hxB,hxW⟩
      rw [hExB i k] at hTrace
      obtain ⟨H,hH,hEq⟩ := List.mem_map.mp hTrace
      have hxH : (x : Z) ∈ H := by
        have hxTrace : x ∈ b.1 ∩ (Ex i).W k := ⟨hxB,hxW⟩
        rw [← hEq] at hxTrace
        exact hxTrace
      have hxFull : (x : Z) ∈ ⋃ H ∈ chartBoundaryOfList (c i k)
          (((disjointSortedChartWindow C D W K hD hGeo (c i k)).sort (· ≤ ·)).map D), H :=
        mem_iUnion₂.mpr ⟨H,(disjoint_born_chart_sublist C D hD W K hGeo (c i k)).subset hH,hxH⟩
      rw [hChartSupport] at hxFull
      exact hxFull.1
  · intro hz
    obtain ⟨c₀,hc₀⟩ := hG.2.2.2 (P z)
    have hzV : z ∈ c₀.V := c₀.mem_V hc₀
    have hzFull : z ∈ ⋃ H ∈ chartBoundaryOfList c₀
        (((disjointSortedChartWindow C D W K hD hGeo c₀).sort (· ≤ ·)).map D), H := by
      rw [hChartSupport]
      exact ⟨hz,hzV⟩
    obtain ⟨H,hH,hzH⟩ := mem_iUnion₂.mp hzFull
    let R := disjointSortedChartWindow C D W K hD hGeo c₀
    let E := (R.sort (· ≤ ·)).map D
    let M := fullMarked (E.map ((Subtype.val : c₀.U → X) ⁻¹' ·))
      (GermIdeal.pullback (m := n) (Subtype.val : c₀.U → X) (vanishingIdeal (n := n) (∅ : Set X)))
    change H ∈ (geoTransformAlong M c₀.T).E.map (chartIncl c₀ '' ·) at hH
    obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hH
    rw [boundary_decomp] at hL
    rcases List.mem_append.mp hL with hOld | hBorn
    · obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hOld
      obtain ⟨D',hD',rfl⟩ := List.mem_map.mp hA
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hD'
      have hOld := varying_active_inherited_old_slot C r D hC hLF hD hr hpure W K hActiveCentres hG.1 c₀ j
      have hImage : chartIncl c₀ '' strictAlong c₀.T ((Subtype.val : c₀.U → X) ⁻¹' D j) =
          strictTransform n P (D j) ∩ c₀.V := by
        rw [hOld,Set.image_preimage_eq_inter_range,range_chartIncl]
      have hzOld : z ∈ strictTransform n P (D j) ∩ c₀.V := by rw [← hImage]; exact hzH
      exact mem_iUnion.mpr ⟨Sum.inl j,hzOld.1⟩
    · have hB : chartIncl c₀ '' L ∈ bornChartBoundary c₀ := List.mem_map.mpr ⟨L,hBorn,rfl⟩
      obtain ⟨i,b,hzB⟩ := disjoint_born_chart_slot_covered C D hD W K hCW hWindow hSame hCentres hGeo hG c Ex hExW hExB c₀ _ hB z hzH
      exact mem_iUnion.mpr ⟨Sum.inr ⟨i,b⟩,hzB⟩
end
end Hironaka.HironakaG3VaryingCombinedExactSupport
