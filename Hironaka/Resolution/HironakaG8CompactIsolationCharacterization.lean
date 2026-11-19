import Hironaka.Resolution.HironakaG8CompactConnectedSingular

/-! The compact isolation hypothesis is exact for analytic supports. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG8CompactIsolationCharacterization

open HironakaG8DiscreteOriginalSingular HironakaG8CompactConnectedSingular

/-- A single compact task at a point captures its whole connected component. -/
theorem compact_connectedComponentIn_of_hasCompactIsolation
    {M : Type*} [TopologicalSpace M] [T2Space M] {F : Set M}
    (hF : HasCompactIsolation F) {x : M} (hx : x ∈ F) :
    IsCompact (connectedComponentIn F x) := by
  obtain ⟨D,hD,hMeet,hSub,hClosed⟩ := hF {x} isCompact_singleton
  have hxD : x ∈ D := hMeet ⟨hx,mem_singleton x⟩
  have hCover : D ∪ (F \ D) = F := union_sdiff_cancel hSub
  have hContained : connectedComponentIn F x ⊆ D := by
    have hPre : IsPreconnected (connectedComponentIn F x) :=
      isPreconnected_connectedComponentIn
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hPre
    have hDisj : connectedComponentIn F x ∩ (D ∩ (F \ D)) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun _ h => h.2.2.2 h.2.1
    have hC : connectedComponentIn F x ⊆ D ∪ (F \ D) :=
      hCover.symm ▸ connectedComponentIn_subset F x
    exact (hPre D (F \ D) hD.isClosed hClosed hC hDisj).resolve_right
      (fun h => (h (mem_connectedComponentIn hx)).2 hxD)
  have hFClosed : IsClosed F := hCover ▸ hD.isClosed.union hClosed
  have hCClosed : IsClosed (connectedComponentIn F x) := by
    rw [connectedComponentIn_eq_image hx]
    exact hFClosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  exact hD.of_isClosed_subset hCClosed hContained

/-- For a closed analytic support, compact isolation is equivalent to
compactness of every connected component. -/
theorem hasCompactIsolation_iff_compact_connectedComponentIn
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {F : Set M}
    (hF : IsComplexAnalyticSubset (n := n) F) :
    HasCompactIsolation F ↔ ∀ x ∈ F, IsCompact (connectedComponentIn F x) := by
  refine ⟨fun h _ hx => compact_connectedComponentIn_of_hasCompactIsolation h hx,?_⟩
  intro h
  rw [← iUnion_componentCarriers F]
  apply hasCompactIsolation_iUnion (fun C : componentCarriers F => (C : Set M))
  · intro C
    obtain ⟨x,hx,hC⟩ := C.property
    rw [← hC]
    exact h x hx
  · exact locallyFinite_componentCarriers hF
  · exact disjoint_componentCarriers F

/-- The exact compact isolation criterion for the original analytic singular set. -/
theorem hasCompactIsolation_singularSet_iff
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    HasCompactIsolation (HironakaEmbeddedAnalytic.singularSet (n := n) W) ↔
      ∀ x ∈ HironakaEmbeddedAnalytic.singularSet (n := n) W,
        IsCompact (connectedComponentIn (HironakaEmbeddedAnalytic.singularSet (n := n) W) x) :=
  hasCompactIsolation_iff_compact_connectedComponentIn
    (HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet hW)

end Hironaka.HironakaG8CompactIsolationCharacterization
