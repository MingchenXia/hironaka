import Hironaka.Resolution.HironakaG3VaryingActiveInheritedSlotTrace
import Hironaka.Resolution.HironakaG3DisjointBornChartGeometry
import Hironaka.Resolution.HironakaG3GlobalMemberSafeTrace
import Hironaka.Resolution.HironakaG3REmbeddedGlobalSNC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3VaryingCombinedComponentSlots
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings RestrictEmptyTower
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3REmbeddedGlobalSNC
  HironakaG3IndexedContainingBoundary HironakaG3DisjointLocalTowerAtlas HironakaG3FiniteVisibleAtlas
  HironakaG3SortedLocalWindowGeometry HironakaG3DisjointSortedChartWindow HironakaG3GenericChartBoundaryReadout
  HironakaG3VaryingActiveInheritedSlotTrace HironakaG3GenericBornChartOverlap HironakaG3DisjointBornChartGeometry
  HironakaG3GlobalMemberSafeTrace MaxLocusLocal

variable {n : ℕ} {X Z : CMfd.{0} n} {ι κ : Type*} [LinearOrder κ]
  (C : ι → Set X) (D : κ → Set X) (W : ι → Opens X) (K : ι → LocalTowerClass X)
  {P : Z → X} (hG : IsGluedFrom (finiteVisibleClass (disjointWindowClass C W K) D) Z P)

def varyingComponentWindow (i : ι) : Opens Z := ⟨P ⁻¹' (W i : Set X),(W i).isOpen.preimage hG.1.continuous⟩

def varyingCombinedBoundary (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (varyingComponentWindow C D W K hG i))) :
    (κ ⊕ (Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H})) → Set Z :=
  Sum.elim (fun j => strictTransform n P (D j))
    (fun p => (Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1)

theorem varying_component_chart_combined_slots
    (r : ι → ℕ) (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i)) (hLF : LocallyFinite C)
    (hD : IsLocallyFiniteSNCDivisor n D) (hr : ∀ i, r i < n)
    (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (hCW : ∀ i, C i ⊆ W i) (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X))
    (hCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' C i) T)
    (hActiveCentres : ∀ (i : ι) (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K i U Y T → CentresOver ((Subtype.val : U → X) ⁻¹'
        (if (containingLabels (C i) D (hC i).nonempty hD.1).card = 0 ∨
          r i < n - (containingLabels (C i) D (hC i).nonempty hD.1).card then C i else ∅)) T)
    (hGeo : ∀ i, HasSortedLocalWindowGeometry (C i) D (K i))
    (c : ι → ℕ → TowerChart (finiteVisibleClass (disjointWindowClass C W K) D) Z P)
    (hMem : ∀ i k, K i (c i k).U (c i k).Y (c i k).T)
    (Ex : ∀ i, SNCExhaustion (CMfd.of (n := n) (varyingComponentWindow C D W K hG i)))
    (hExW : ∀ i k, (Ex i).W k = nestedOpens (varyingComponentWindow C D W K hG i) (c i k).V)
    (hExB : ∀ i k, (Ex i).B k = (bornChartBoundary (c i k)).map
      ((Subtype.val : varyingComponentWindow C D W K hG i → Z) ⁻¹' ·))
    (hBorn : ∀ (p : Σ i, {H : Set (varyingComponentWindow C D W K hG i) // (Ex i).IsGlobalMember H}),
      ((Subtype.val : varyingComponentWindow C D W K hG p.1 → Z) '' p.2.1) ⊆ P ⁻¹' C p.1)
    (i : ι) (k : ℕ) (x : Z) (hxV : x ∈ (c i k).V) (hxC : P x ∈ C i) :
    ∀ a, x ∈ varyingCombinedBoundary C D W K hG Ex a →
      varyingCombinedBoundary C D W K hG Ex a ∩ (c i k).V ∈
        chartBoundaryOfList (c i k) (((disjointSortedChartWindow C D W K hD hGeo (c i k)).sort (· ≤ ·)).map D) := by
  let Q := varyingComponentWindow C D W K hG i
  let c₀ := c i k
  have hBornQ : ∀ H ∈ bornChartBoundary c₀, H ⊆ (Q : Set Z) := by
    intro H hH z hz
    exact hCW i (disjoint_born_chart_over_component C C D W K hCentres i c₀ (hMem i k) hH hz)
  intro a hx
  cases a with
  | inl j =>
    have hNE : (strictTransform n P (D j) ∩ c₀.V).Nonempty := ⟨x,hx,hxV⟩
    exact varying_inherited_trace_is_selected_slot C r D hC hLF hD hr hpure W K hActiveCentres hGeo hG.1 c₀ j hNE
  | inr p =>
    rcases p with ⟨j,b⟩
    have hxCj : P x ∈ C j := hBorn ⟨j,b⟩ hx
    have hj : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hWindow i j (Ne.symm hne)) hxCj (hCW i hxC)
    subst j
    have hxQ : x ∈ Q := hCW i hxC
    have hNE : (((Subtype.val : Q → Z) '' b.1) ∩ (Q ⊓ c₀.V : Opens Z)).Nonempty := ⟨x,hx,hxQ,hxV⟩
    have hslot := global_member_safe_trace_is_slot Q c₀.V (Ex i) k (bornChartBoundary c₀)
      (hExW i k) (hExB i k) (fun H hH => disjoint_born_chart_subset C D hD W K hGeo c₀ hH) b hNE
    obtain ⟨H,hH,hEq⟩ := List.mem_map.mp hslot
    have hImgQ : ((Subtype.val : Q → Z) '' b.1) ⊆ (Q : Set Z) := by rintro _ ⟨z,_,rfl⟩; exact z.property
    have hTrace : ((Subtype.val : Q → Z) '' b.1) ∩ c₀.V = H := by
      ext z
      constructor
      · rintro ⟨hzB,hzV⟩
        have hz : z ∈ ((Subtype.val : Q → Z) '' b.1) ∩ (Q ⊓ c₀.V : Opens Z) := ⟨hzB,hImgQ hzB,hzV⟩
        rw [← hEq] at hz
        exact hz.1
      · intro hzH
        have hz : z ∈ H ∩ (Q : Set Z) := ⟨hzH,hBornQ H hH hzH⟩
        rw [hEq] at hz
        exact ⟨hz.1,hz.2.2⟩
    change ((Subtype.val : Q → Z) '' b.1) ∩ c₀.V ∈
      chartBoundaryOfList c₀ (((disjointSortedChartWindow C D W K hD hGeo c₀).sort (· ≤ ·)).map D)
    rw [hTrace]
    exact (disjoint_born_chart_sublist C D hD W K hGeo c₀).subset hH
end
end Hironaka.HironakaG3VaryingCombinedComponentSlots
