import Hironaka.Resolution.HironakaG3VaryingCombinedComponentDistinct
import Hironaka.Resolution.HironakaG3VaryingOffComponentSlots
import Hironaka.Resolution.HironakaG3IndexedSNCLocalSlots
import Hironaka.Resolution.HironakaG3SeparatedInheritedBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingCombinedIndexedSNC
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings RestrictEmptyTower
  HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaG3IndexedContainingBoundary HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas
  HironakaG3SortedLocalWindowGeometry HironakaG3DisjointSortedChartWindow HironakaG3GenericChartBoundaryReadout
  HironakaG3DisjointSortedChartGeometry HironakaG3VaryingActiveInheritedLabels HironakaG3VaryingCombinedComponentSlots
  HironakaG3VaryingCombinedComponentDistinct HironakaG3VaryingOffComponentSlots HironakaG3IndexedSNCLocalSlots
  HironakaG3SeparatedInheritedBoundary HironakaG3GenericBornChartOverlap MaxLocusLocal

theorem varying_combined_indexed_snc {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
    (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hD : IsLocallyFiniteSNCDivisor n D)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (hCW : ∀ i, C i ⊆ W i) (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T)
    (hActiveCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
        (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
          r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i)) {P : Z → X}
    (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (hExc : exceptionalLocus n P ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD))
    (c : ι → ℕ → TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (hMem : ∀ i k, K i (c i k).U (c i k).Y (c i k).T)
    (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (varyingComponentWindow C D W K hG i)))
    (hExW : ∀ i k, (Ex i).W k = nestedOpens (varyingComponentWindow C D W K hG i) (c i k).V)
    (hExB : ∀ i k, (Ex i).B k = (bornChartBoundary (c i k)).map
      ((Subtype.val : varyingComponentWindow C D W K hG i → Z) ⁻¹' ·))
    (hBornLF : LocallyFinite (fun p : Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H} =>
      (Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1))
    (hBornClosed : ∀ (p : Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H}),
      IsClosed ((Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1))
    (hBorn : ∀ (p : Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H}),
      ((Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1) ⊆ P ⁻¹' C p.1)
    (hBornActive : ∀ (p : Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H}),
      ((Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1) ⊆ P ⁻¹' (varyingActiveUnion C r D hC hD)) :
    IsLocallyFiniteSNCDivisor n (varyingCombinedBoundary C D W K hG Ex) ∧
      ∀ j, HasNormalCrossingsWithBoundary (strictTransform n P (C j)) (varyingCombinedBoundary C D W K hG Ex) := by
  let F := varyingCombinedBoundary C D W K hG Ex
  have hOldLF := inherited_strict_family_locally_finite D hD.2.1 hD.1 hG.1
  have hFullLF : LocallyFinite F := hOldLF.sumElim hBornLF
  have hClosed : ∀ a, IsClosed (F a) := by
    intro a
    cases a with
    | inl j => exact isClosed_closure
    | inr p => exact hBornClosed p
  have hComponent (i : ι) (x : Z) (hxC : P x ∈ C i) :
      ∃ (U : Opens Z) (E : List (Set Z)), x ∈ U ∧
        IsSNCDivisor n (E.map ((Subtype.val : U → Z) ⁻¹' ·)) ∧
        (∀ a, x ∈ F a → ∃ p : Fin (E.map ((Subtype.val : U → Z) ⁻¹' ·)).length,
          (E.map ((Subtype.val : U → Z) ⁻¹' ·)).get p = (Subtype.val : U → Z) ⁻¹' F a) ∧
        (∀ a b, x ∈ F a → x ∈ F b → (Subtype.val : U → Z) ⁻¹' F a = (Subtype.val : U → Z) ⁻¹' F b → a = b) ∧
        ∀ j, HasNormalCrossings n ((Subtype.val : U → Z) ⁻¹' strictTransform n P (C j))
          (E.map ((Subtype.val : U → Z) ⁻¹' ·)) := by
    have hxQ : x ∈ varyingComponentWindow C D W K hG i := hCW i hxC
    obtain ⟨k,hxk⟩ := (Ex i).cover ⟨x,hxQ⟩
    have hxV : x ∈ (c i k).V := by rw [hExW] at hxk; exact hxk
    let U := (c i k).V
    let E := chartBoundaryOfList (c i k) (((disjointSortedChartWindow C D W K hD hGeo (c i k)).sort (· ≤ ·)).map D)
    refine ⟨U,E,hxV,disjoint_sorted_chart_boundary_snc C D hD W K hGeo (c i k),?_,?_,?_⟩
    · intro a ha
      have hmem := varying_component_chart_combined_slots C D W K hG r hC hLF hD hr hpure hCW hWindow
        hCentres hActiveCentres hGeo c hMem Ex hExW hExB hBorn i k x hxV hxC a ha
      obtain ⟨p,hp⟩ := List.mem_iff_get.mp hmem
      have hp' : p.val < (E.map ((Subtype.val : U → Z) ⁻¹' ·)).length := by
        rw [List.length_map]
        exact p.isLt
      refine ⟨⟨p.val,hp'⟩,?_⟩
      simp only [List.get_eq_getElem,List.getElem_map]
      change (Subtype.val : U → Z) ⁻¹' E.get p = (Subtype.val : U → Z) ⁻¹' F a
      rw [hp]
      ext z
      simp [U,F]
    · exact varying_component_chart_combined_labels_distinct C D W K hG r hC hLF hDis hD hr hpure hExc
        c Ex hExW hBorn hBornActive i k x hxV hxC
    · exact fun j => disjoint_sorted_chart_component_nc C (fun i => (hC i).analytic.isClosed) D hD W K hWindow hGeo hG.1 (c i k) j
  constructor
  · apply indexed_snc_of_local_slots F hFullLF hClosed
    intro x
    by_cases hx : P x ∈ ⋃ i, C i
    · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
      obtain ⟨U,E,hxU,hSNC,hSlot,hUnique,_⟩ := hComponent i x hxi
      exact ⟨U,E,hxU,hSNC,hSlot,hUnique⟩
    · exact varying_off_component_local_slots C r D W K hC hLF hD hr hpure hActiveCentres hGeo hG hExc Ex hBorn x hx
  · intro j
    apply indexed_nc_of_local_slots (strictTransform n P (C j)) F
    intro x hx
    have hxC : P x ∈ C j := HironakaAdmissibleCalculus.strictTransform_subset_preimage hG.1.continuous (hC j).analytic.isClosed hx
    obtain ⟨U,E,hxU,_hSNC,hSlot,_hUnique,hNC⟩ := hComponent j x hxC
    exact ⟨U,E,hxU,hNC j,hSlot⟩
end
end Hironaka.HironakaG3VaryingCombinedIndexedSNC
