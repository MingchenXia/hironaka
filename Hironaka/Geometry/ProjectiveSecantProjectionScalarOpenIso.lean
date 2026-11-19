import Hironaka.Geometry.ProjectiveSecantProjectionScalarEtale
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Actual dense original target isomorphism opens in the same native Cartesian scalar square
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The whole actual Cartesian triangle identifies the SAME original source inverse image with the SAME actual new target inverse image. -/
theorem isPullback_preimage_target_open
    {P X Y Y' : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (H : IsPullback a b f g) (U : Y.Opens) : a ⁻¹ᵁ (f ⁻¹ᵁ U) = b ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  simpa only [Scheme.Hom.comp_preimage] using congrArg (fun m : P ⟶ Y => m ⁻¹ᵁ U) H.w

/-- The SAME actual base-changed whole map is an isomorphism over the actual inverse image of the SAME original target isomorphism open. -/
theorem isIso_pullback_morphismRestrict
    {P X Y Y' : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (H : IsPullback a b f g) (U : Y.Opens) [IsIso (f ∣_ U)] : IsIso (b ∣_ (g ⁻¹ᵁ U)) := by
  have h := Scheme.Hom.isPullback_resLE H (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := b ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl le_rfl (by rw [isPullback_preimage_target_open H U, inf_idem])
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at h
  exact h.isIso_snd_of_isIso

/-- The original dense target isomorphism open pulls back to actual dense source and target opens, proving native birationality of the SAME actual map over its SAME actual target. -/
theorem birationalOver_pullback_of_dense_isIso
    {P X Y Y' : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (H : IsPullback a b f g) [UniversallyOpen g] (U : Y.Opens)
    (hU : Dense (U : Set Y)) (hpre : Dense (f ⁻¹ᵁ U : Set X)) [IsIso (f ∣_ U)] :
    Scheme.BirationalOver b (𝟙 Y') := by
  let : UniversallyOpen a := MorphismProperty.of_isPullback H.flip inferInstance
  have hs : Dense (b ⁻¹ᵁ (g ⁻¹ᵁ U) : Set P) := by
    rw [← isPullback_preimage_target_open H U]
    exact hpre.preimage a.isOpenMap
  let : IsIso (b ∣_ (g ⁻¹ᵁ U)) := isIso_pullback_morphismRestrict H U
  let e : P.PartialIso Y' := {
    source := b ⁻¹ᵁ (g ⁻¹ᵁ U)
    dense_source := hs
    target := g ⁻¹ᵁ U
    dense_target := hU.preimage g.isOpenMap
    iso := asIso (b ∣_ (g ⁻¹ᵁ U)) }
  refine ⟨e, ?_⟩
  change (b ∣_ (g ⁻¹ᵁ U)) ≫ (g ⁻¹ᵁ U).ι ≫ 𝟙 Y' = (b ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ b
  rw [Category.comp_id, morphismRestrict_ι]

end Hironaka.Geometry.ProjectiveSecant
