import Hironaka.Resolution.HironakaG3LocallyFiniteSupportedFamilies
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology
namespace Hironaka.HironakaG3ActiveSupportedFamily
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Conditional support preserves closedness, local finiteness, window
containment, and exactly the union over the active subtype. -/
theorem active_supported_family {X : Type*} [TopologicalSpace X] {ι : Type*}
    (A W : ι → Set X) (active : ι → Prop)
    (hClosed : ∀ i, IsClosed (A i)) (hLF : LocallyFinite A)
    (hAW : ∀ i, A i ⊆ W i) :
    let F : ι → Set X := fun i => if active i then A i else ∅
    (∀ i, IsClosed (F i)) ∧ LocallyFinite F ∧ (∀ i, F i ⊆ W i) ∧
      (⋃ i, F i) = ⋃ i : {i // active i}, A i.val := by
  let F : ι → Set X := fun i => if active i then A i else ∅
  have hsub : ∀ i, F i ⊆ A i := by
    intro i
    by_cases hi : active i <;> simp [F,hi]
  refine ⟨?_,hLF.subset hsub,fun i => (hsub i).trans (hAW i),?_⟩
  · intro i
    by_cases hi : active i <;> simp [hi,hClosed i]
  · ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      by_cases ha : active i
      · exact mem_iUnion.mpr ⟨⟨i,ha⟩,by simpa [F,ha] using hi⟩
      · simp [ha] at hi
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.val,by simpa [F,i.property] using hi⟩
end
end Hironaka.HironakaG3ActiveSupportedFamily
