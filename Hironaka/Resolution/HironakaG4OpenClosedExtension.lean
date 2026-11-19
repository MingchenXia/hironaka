import Hironaka.Resolution.HironakaG4ToricProtectedWindow

/-! A closed local divisor extends as a closed set with the same restriction. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology
universe u
namespace Hironaka.HironakaG4OpenClosedExtension

variable {X : Type u} [TopologicalSpace X]

/-- A subset closed in an open window is the restriction of its ambient closure. -/
theorem preimage_closure_image_eq (U : Opens X) {H : Set U} (hH : IsClosed H) :
    (Subtype.val : U → X) ⁻¹' closure ((Subtype.val : U → X) '' H) = H := by
  have key : (Subtype.val : U → X) ⁻¹' closure ((Subtype.val : U → X) '' H) =
      closure ((Subtype.val : U → X) ⁻¹' ((Subtype.val : U → X) '' H)) :=
    (U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val ((Subtype.val : U → X) '' H)
  have hinj : (Subtype.val : U → X) ⁻¹' ((Subtype.val : U → X) '' H) = H := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      have : y = x := Subtype.val_injective he
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hinj, hH.closure_eq] at key
  exact key

end Hironaka.HironakaG4OpenClosedExtension
