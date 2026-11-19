import Mathlib.Topology.Constructions
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG3ClosedSupportedWindowExtension

/-- A relatively closed subset supported in a closed set inside the window is globally closed. -/
theorem isClosed_image_of_closed_support {M : Type*} [TopologicalSpace M]
    (Q F : Set M) (hF : IsClosed F) (hFQ : F ⊆ Q) (H : Set Q) (hH : IsClosed H)
    (hHF : H ⊆ (Subtype.val : Q → M) ⁻¹' F) : IsClosed ((Subtype.val : Q → M) '' H) := by
  let f : F → Q := fun x => ⟨x,hFQ x.property⟩
  have hf : Continuous f := Continuous.subtype_mk continuous_subtype_val _
  have hc : IsClosed ((Subtype.val : F → M) '' (f ⁻¹' H)) := hF.isClosedMap_subtype_val _ (hH.preimage hf)
  have heq : (Subtype.val : F → M) '' (f ⁻¹' H) = (Subtype.val : Q → M) '' H := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨f y,hy,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hHF hy⟩,hy,rfl⟩
  rwa [heq] at hc
end Hironaka.HironakaG3ClosedSupportedWindowExtension
