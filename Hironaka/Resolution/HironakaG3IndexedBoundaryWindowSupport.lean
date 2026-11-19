import Hironaka.Resolution.HironakaG3IndexedContainingBoundary

/-! Exact local support of a visible finite indexed boundary window.
Blueprint first: hironaka-g3-indexed-boundary-window-support.tex. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG3IndexedBoundaryWindowSupport
noncomputable section
open HironakaG3IndexedContainingBoundary

/-- Sorting the complete visible labels retains the entire indexed support on U. -/
theorem indexed_window_support_inter {α ι : Type*} [LinearOrder ι]
    (D : ι → Set α) (S R : Finset ι) (U : Set α)
    (hVis : ∀ i, i ∉ S → (D i ∩ U).Nonempty → i ∈ R) :
    (⋃ H ∈ ((R.sort (· ≤ ·)).map D ++ (S.sort (· ≤ ·)).map D), H) ∩ U =
      (⋃ i, D i) ∩ U := by
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    obtain ⟨H, hH, hxH⟩ := mem_iUnion₂.mp hx
    rw [List.mem_append] at hH
    rcases hH with hR | hS
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hR
      exact ⟨mem_iUnion.mpr ⟨i,hxH⟩,hxU⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hS
      exact ⟨mem_iUnion.mpr ⟨i,hxH⟩,hxU⟩
  · rintro ⟨hx, hxU⟩
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    refine ⟨mem_iUnion₂.mpr ⟨D i,?_,hxi⟩,hxU⟩
    rw [List.mem_append]
    by_cases hiS : i ∈ S
    · right
      exact List.mem_map.mpr ⟨i, by simpa using hiS, rfl⟩
    · left
      have hiR := hVis i hiS ⟨x,hxi,hxU⟩
      exact List.mem_map.mpr ⟨i, by simpa using hiR, rfl⟩

/-- A positive set of actual containing labels puts the whole target in the indexed support. -/
theorem positive_containing_labels_target_subset {α ι : Type*} [TopologicalSpace α]
    (C : Set α) (D : ι → Set α) (hC : C.Nonempty) (hD : LocallyFinite D)
    (hS : 0 < (containingLabels C D hC hD).card) : C ⊆ ⋃ i, D i := by
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hS
  have hCD : C ⊆ D i := (mem_containingLabels C D hC hD i).mp hi
  intro x hx
  exact mem_iUnion.mpr ⟨i,hCD hx⟩

end
end Hironaka.HironakaG3IndexedBoundaryWindowSupport

