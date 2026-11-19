import Hironaka.Resolution.HironakaG3DisjointLocalTowerAtlas
import Hironaka.Resolution.HironakaG3IndexedAvoidingCentresOver
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3SeparatedAvoidingAtlas
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings HironakaG3RTowerClass
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3IndexedAvoidingCentresOver HironakaG3DisjointLocalTowerAtlas

/-- Actual avoiding histories for separated components glue in one native atlas. -/
theorem exists_glued_separated_avoiding_atlas {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder κ] (C : ι → Set X) (r : ι → ℕ) (D : κ → Set X)
    (hC : ∀ i, IsComplexAnalyticallyIrreducible (n := n) (C i))
    (hLF : LocallyFinite C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : ∀ i, containingLabels (C i) D (hC i).nonempty hD.1 = ∅)
    (hr : ∀ i, r i < n) (hpure : ∀ i, C i ⊆ closure (regularLocus (n := n) (C i) (r i)))
    (W : ι → Opens X) (hCW : ∀ i, C i ⊆ W i)
    (hWindow : ∀ i j, i ≠ j → Disjoint (C j) (W i : Set X)) :
    ∃ (Z : CMfd.{0} n) (P : Z → X),
      IsGluedFrom (disjointWindowClass C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)) Z P := by
  apply exists_glued_disjoint_window_atlas C W (fun i => indexedAvoidingBoundaryClass (C i) (r i) D)
    (fun i => (hC i).analytic.isClosed) hLF hWindow
  · exact fun i => indexed_avoiding_boundary_comparisons (C i) D (hC i) hD (hS i) (hr i) (hpure i)
  · intro i U Y T hT
    exact indexed_avoiding_centres_over (C i) D (hC i).analytic hD (hr i) (hpure i) U Y T hT
  · let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
    intro i x hx
    obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds x
    let U : Opens X := ⟨interior K ∩ (W i : Set X),isOpen_interior.inter (W i).isOpen⟩
    have hxU : x ∈ U := ⟨mem_interior_iff_mem_nhds.mpr hxK,hCW i hx⟩
    have hUK : (U : Set X) ⊆ K := fun _ h => interior_subset h.1
    obtain ⟨Y,T,hT⟩ := indexed_avoiding_boundary_member_over_compact_window (C i) D (hC i) hD (hr i) (hpure i) U K hK hUK
    exact ⟨U,hxU,fun _ h => h.2,Y,T,hT⟩
end
end Hironaka.HironakaG3SeparatedAvoidingAtlas
