import Hironaka.Geometry.NodeFamilyFibres

/-! Genuine open-cover descent of native geometric reducedness, for the actual node tower consumer. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace Hironaka.Geometry.NodeFamilyTowerLocality

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native geometric reducedness descends from the composites of a genuine source open cover. -/
theorem geometricallyReduced_of_openCover {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : X.OpenCover.{v}) (h : ∀ i, GeometricallyReduced (𝒰.f i ≫ f)) :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff]
  intro K _ y Z fst snd hpb
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := 𝒰.pullback₁ fst)
  intro i
  let : GeometricallyReduced (𝒰.f i ≫ f) := h i
  exact GeometricallyReduced.geometrically_isReduced y _ _
    ((IsPullback.of_hasPullback fst (𝒰.f i)).flip.paste_vert hpb)

end Hironaka.Geometry.NodeFamilyTowerLocality
