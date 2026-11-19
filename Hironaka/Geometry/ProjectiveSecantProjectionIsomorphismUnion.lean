import Hironaka.Geometry.ProjectiveSecantProjectionImageOpenIso
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Actual original target isomorphism opens glue over their whole original union

The pure native restriction-union argument is reused from
BingWangEntropy/NativeRestrictionUnionIso.lean, SHA256
52015e61c98002b72f4e3814e12f7ea60cc0d74b5489fd748d8fe0d84b62061c.
No analytic or source-project import is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original restricted scheme isomorphisms glue over the SAME entire original target-open union. -/
theorem original_morphismRestrict_iSup_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type*} (U : I → Y.Opens) (h : ∀ i, IsIso (f ∣_ U i)) : IsIso (f ∣_ ⨆ i, U i) := by
  let V : Y.Opens := ⨆ i, U i
  have hc : (⨆ i, V.ι ⁻¹ᵁ U i) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun i => V.ι ⁻¹ᵁ U i) hc).mpr
  intro i
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ U i) = U i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (le_iSup U i)
  apply ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U i))).mpr
  change IsIso (f ∣_ V.ι ''ᵁ (V.ι ⁻¹ᵁ U i))
  rw [he]
  exact h i

end Hironaka.Geometry.ProjectiveSecant
