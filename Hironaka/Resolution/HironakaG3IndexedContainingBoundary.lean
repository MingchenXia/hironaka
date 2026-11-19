import Hironaka.Resolution.HironakaG3MixedComponentOpen
import Hironaka.Resolution.HironakaG3OrderedFiniteWindows

/-!
# The canonical original boundary labels containing an irreducible component

Local finiteness makes the whole containing-label set finite for a nonempty
target. Analytic irreducibility then makes containment on every nonempty open
trace equivalent to global containment. Complete sorted windows consequently
have the same literal containing labels and actual labelled open traces.
Neither an empty target nor an empty target-window intersection is allowed
in the corresponding nonvacuity hypothesis.

Blueprint: `hironaka-g3-indexed-containing-boundary.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3IndexedContainingBoundary

noncomputable section

attribute [local instance] Classical.propDecidable

section Topological

variable {X ι : Type*} [TopologicalSpace X]

/-- All original labels containing a nonempty target form a finite set.
The actual locally finite point window supplies the finite bound. -/
theorem finite_containing_indices (C : Set X) (D : ι → Set X)
    (hC : C.Nonempty) (hD : LocallyFinite D) : {i | C ⊆ D i}.Finite := by
  obtain ⟨x,hx⟩ := hC
  exact (hD.point_finite x).subset (fun _ hi => hi hx)

/-- The entire containing-label set, independent of any finite window. -/
def containingLabels (C : Set X) (D : ι → Set X)
    (hC : C.Nonempty) (hD : LocallyFinite D) : Finset ι :=
  (finite_containing_indices C D hC hD).toFinset

@[simp]
theorem mem_containingLabels (C : Set X) (D : ι → Set X)
    (hC : C.Nonempty) (hD : LocallyFinite D) (i : ι) :
    i ∈ containingLabels C D hC hD ↔ C ⊆ D i := by
  simp only [containingLabels,Set.Finite.mem_toFinset,mem_ofPred_eq]

end Topological

open BlowupTowers HironakaG3MixedComponentOpen HironakaG3OrderedFiniteWindows

variable {n : ℕ} {X : CMfd.{0} n} {ι : Type*}

/-- For an irreducible analytic target, containment on any nonempty actual
open trace is exactly containment of the whole original target. -/
theorem inter_open_subset_iff {C H : Set X}
    (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hH : IsComplexAnalyticSubset (n := n) H) (U : Opens X)
    (hCU : (C ∩ (U : Set X)).Nonempty) :
    C ∩ (U : Set X) ⊆ H ↔ C ⊆ H := by
  constructor
  · intro hlocal
    by_contra hNot
    have hDense : C ⊆ closure (C \ H) := by
      simpa using irreducible_dense_off_list hC [H]
        (fun K hK => (List.mem_singleton.mp hK) ▸ hH)
        (fun K hK => (List.mem_singleton.mp hK) ▸ hNot)
    obtain ⟨x,hxC,hxU⟩ := hCU
    obtain ⟨y,hyU,hyC,hyNot⟩ := mem_closure_iff.mp (hDense hxC) _ U.isOpen hxU
    exact hyNot (hlocal ⟨hyC,hyU⟩)
  · exact fun h x hx => h hx.1

/-- Every complete finite window identifies the whole containing-label set
from its actual nonempty target trace, without a supplied containing packet. -/
theorem window_containing_labels_eq (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : LocallyFinite D)
    (hDa : ∀ i, IsComplexAnalyticSubset (n := n) (D i))
    (U : Opens X) (hCU : (C ∩ (U : Set X)).Nonempty) (s : Finset ι)
    (hvisible : ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ s) :
    s.filter (fun i => C ∩ (U : Set X) ⊆ D i) = containingLabels C D hC.nonempty hD := by
  ext i
  rw [Finset.mem_filter,mem_containingLabels,
    inter_open_subset_iff hC (hDa i) U hCU]
  constructor
  · exact And.right
  · intro hi
    obtain ⟨x,hxC,hxU⟩ := hCU
    exact ⟨hvisible i ⟨x,hi hxC,hxU⟩,hi⟩

/-- Filtering a sorted complete window retains exactly the globally
containing original labels, in their original index order. -/
theorem sorted_window_containing_labels_eq [LinearOrder ι]
    (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : LocallyFinite D)
    (hDa : ∀ i, IsComplexAnalyticSubset (n := n) (D i))
    (U : Opens X) (hCU : (C ∩ (U : Set X)).Nonempty) (s : Finset ι)
    (hvisible : ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ s) :
    (s.sort (· ≤ ·)).filter (fun i => decide (C ∩ (U : Set X) ⊆ D i)) =
      (containingLabels C D hC.nonempty hD).sort (· ≤ ·) := by
  rw [sort_filter,window_containing_labels_eq C D hC hD hDa U hCU s hvisible]

private theorem preimage_val_subset_iff (C H : Set X) (U : Opens X) :
    (Subtype.val : U → X) ⁻¹' C ⊆ (Subtype.val : U → X) ⁻¹' H ↔
      C ∩ (U : Set X) ⊆ H := by
  constructor
  · intro h x hx
    exact h (show (⟨x,hx.2⟩ : U) ∈ (Subtype.val : U → X) ⁻¹' C from hx.1)
  · intro h x hx
    exact h ⟨hx,x.property⟩

/-- The containing sublist keeps every original label paired with its
literal open trace; coincident sets do not merge distinct labels. -/
theorem sorted_window_containing_boundary_dictionary [LinearOrder ι]
    (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : LocallyFinite D)
    (hDa : ∀ i, IsComplexAnalyticSubset (n := n) (D i))
    (U : Opens X) (hCU : (C ∩ (U : Set X)).Nonempty) (s : Finset ι)
    (hvisible : ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ s) :
    ((s.sort (· ≤ ·)).filter (fun i => decide
      ((Subtype.val : U → X) ⁻¹' C ⊆ (Subtype.val : U → X) ⁻¹' D i))).map
        (fun i => (i,(Subtype.val : U → X) ⁻¹' D i)) =
      ((containingLabels C D hC.nonempty hD).sort (· ≤ ·)).map
        (fun i => (i,(Subtype.val : U → X) ⁻¹' D i)) := by
  have hpred : (fun i => decide
      ((Subtype.val : U → X) ⁻¹' C ⊆ (Subtype.val : U → X) ⁻¹' D i)) =
      (fun i => decide (C ∩ (U : Set X) ⊆ D i)) := by
    funext i
    simp only [preimage_val_subset_iff]
  rw [hpred,sorted_window_containing_labels_eq C D hC hD hDa U hCU s hvisible]

/-- Original local finiteness internally gives a complete finite window at
each target point, with its canonical sorted original containing labels. -/
theorem exists_complete_window_with_containing_labels [LinearOrder ι]
    (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : LocallyFinite D)
    (hDa : ∀ i, IsComplexAnalyticSubset (n := n) (D i)) (x : X) (hx : x ∈ C) :
    ∃ (U : Opens X) (s : Finset ι), x ∈ U ∧
      (∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ s) ∧
      (s.sort (· ≤ ·)).filter (fun i => decide (C ∩ (U : Set X) ⊆ D i)) =
        (containingLabels C D hC.nonempty hD).sort (· ≤ ·) := by
  obtain ⟨A,hAx,hfin⟩ := hD x
  obtain ⟨O,hOA,hOo,hxO⟩ := mem_nhds_iff.mp hAx
  let U : Opens X := ⟨O,hOo⟩
  let s := hfin.toFinset
  have hvisible : ∀ i, (D i ∩ (U : Set X)).Nonempty → i ∈ s := by
    intro i hi
    apply hfin.mem_toFinset.mpr
    obtain ⟨y,hyD,hyU⟩ := hi
    exact ⟨y,hyD,hOA hyU⟩
  refine ⟨U,s,hxO,hvisible,?_⟩
  exact sorted_window_containing_labels_eq C D hC hD hDa U ⟨x,hx,hxO⟩ s hvisible

end

end Hironaka.HironakaG3IndexedContainingBoundary
