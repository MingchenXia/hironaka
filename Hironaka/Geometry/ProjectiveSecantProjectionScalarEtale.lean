import Hironaka.Geometry.GenericallyEtaleComposition
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Generic etaleness of the actual original native pullback under open scalar projection
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pasting the actual original source-open square and SAME native pullback square makes the SAME original second projection etale on its actual original inverse-image open. -/
theorem etale_pullback_source_open
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (U : X.Opens)
    [Etale (U.ι ≫ f)] :
    Etale (((pullback.fst f g) ⁻¹ᵁ U).ι ≫ pullback.snd f g) := by
  have h := (isPullback_morphismRestrict (pullback.fst f g) U).paste_vert
    (IsPullback.of_hasPullback f g)
  exact MorphismProperty.of_isPullback h inferInstance

/-- The actual original dense etale source open has dense actual inverse image under the SAME native open first projection. -/
theorem genericallyEtale_pullback_of_universallyOpen
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [UniversallyOpen g]
    (hf : IsGenericallyEtale f) : IsGenericallyEtale (pullback.snd f g) := by
  obtain ⟨U, hU, hEt⟩ := hf
  let := hEt
  let : UniversallyOpen (pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
  exact ⟨(pullback.fst f g) ⁻¹ᵁ U, hU.preimage (pullback.fst f g).isOpenMap,
    etale_pullback_source_open f g U⟩

end Hironaka.Geometry.ProjectiveSecant
