import Hironaka.Resolution.HironakaG3VaryingCombinedComponentSlots
import Hironaka.Resolution.HironakaG3VaryingActiveInheritedLabels
import Hironaka.Resolution.HironakaG3DisjointSortedChartGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingOffComponentSlots
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings RestrictEmptyTower
  HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC HironakaActualLocallyFiniteBoundary
  HironakaG3IndexedContainingBoundary HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas
  HironakaG3SortedLocalWindowGeometry HironakaG3DisjointSortedChartWindow HironakaG3GenericChartBoundaryReadout
  HironakaG3DisjointSortedChartGeometry HironakaG3VaryingActiveInheritedSlotTrace
  HironakaG3VaryingActiveInheritedLabels HironakaG3VaryingCombinedComponentSlots MaxLocusLocal

theorem varying_off_component_local_slots {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (hActiveCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
        (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
          r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i)) {P : Z → X}
    (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (hExc : exceptionalLocus n P ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD))
    (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (varyingComponentWindow C D W K hG i)))
    (hBorn : ∀ (p : Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H}),
      ((Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1) ⊆ P ⁻¹' C p.1)
    (x : Z) (hx : P x ∉ ⋃ i, C i) :
    ∃ (U : Opens Z) (E : List (Set Z)), x ∈ U ∧
      IsSNCDivisor n (E.map ((Subtype.val : U → Z) ⁻¹' ·)) ∧
      (∀ a, x ∈ varyingCombinedBoundary C D W K hG Ex a →
        ∃ p : Fin (E.map ((Subtype.val : U → Z) ⁻¹' ·)).length,
          (E.map ((Subtype.val : U → Z) ⁻¹' ·)).get p =
            (Subtype.val : U → Z) ⁻¹' varyingCombinedBoundary C D W K hG Ex a) ∧
      (∀ a b, x ∈ varyingCombinedBoundary C D W K hG Ex a →
        x ∈ varyingCombinedBoundary C D W K hG Ex b →
        (Subtype.val : U → Z) ⁻¹' varyingCombinedBoundary C D W K hG Ex a =
          (Subtype.val : U → Z) ⁻¹' varyingCombinedBoundary C D W K hG Ex b → a = b) := by
  obtain ⟨c,hxc⟩ := hG.2.2.2 (P x)
  have hxV : x ∈ c.V := c.mem_V hxc
  let E := chartBoundaryOfList c (((disjointSortedChartWindow C D W K hD hGeo c).sort (· ≤ ·)).map D)
  refine ⟨c.V,E,hxV,disjoint_sorted_chart_boundary_snc C D hD W K hGeo c,?_,?_⟩
  · intro a ha
    cases a with
    | inl j =>
      have hmem := varying_inherited_trace_is_selected_slot C r D hC hLF hD hr hpure W K hActiveCentres hGeo hG.1 c j ⟨x,ha,hxV⟩
      obtain ⟨p,hp⟩ := List.mem_iff_get.mp hmem
      have hp' : p.val < (E.map ((Subtype.val : c.V → Z) ⁻¹' ·)).length := by simp [E]
      refine ⟨⟨p.val,hp'⟩,?_⟩
      simp only [List.get_eq_getElem,List.getElem_map]
      change (Subtype.val : c.V → Z) ⁻¹' E.get p = (Subtype.val : c.V → Z) ⁻¹' strictTransform n P (D j)
      rw [hp]
      ext z
      simp
    | inr p => exact False.elim (hx (mem_iUnion.mpr ⟨p.1,hBorn p ha⟩))
  · intro a b ha hb heq
    cases a with
    | inl j =>
      cases b with
      | inl k =>
        congr 1
        apply varying_inherited_trace_labels_eq C r D hC hLF hD hr hpure hG.1 hExc j k c.V ⟨x,ha,hxV⟩
        ext z
        constructor <;> rintro ⟨hz,hzV⟩
        · exact ⟨(Set.ext_iff.mp heq ⟨z,hzV⟩).mp hz,hzV⟩
        · exact ⟨(Set.ext_iff.mp heq ⟨z,hzV⟩).mpr hz,hzV⟩
      | inr p => exact False.elim (hx (mem_iUnion.mpr ⟨p.1,hBorn p hb⟩))
    | inr p => exact False.elim (hx (mem_iUnion.mpr ⟨p.1,hBorn p ha⟩))
end
end Hironaka.HironakaG3VaryingOffComponentSlots
