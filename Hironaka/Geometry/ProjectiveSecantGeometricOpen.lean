import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Geometric reducedness on actual original source opens
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual source open immersions retain native geometric reducedness under every actual field base change. -/
theorem geometricallyReduced_open_source {U X Y : Scheme.{u}}
    (a : U ⟶ X) [IsOpenImmersion a] (f : X ⟶ Y) [GeometricallyReduced f] :
    GeometricallyReduced (a ≫ f) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ y
  let h : pullback (a ≫ f) y ⟶ pullback f y :=
    pullback.map _ _ _ _ a (𝟙 _) (𝟙 _) (by simp) (by simp)
  let : IsReduced (pullback f y) :=
    GeometricallyReduced.geometrically_isReduced y _ _ (.of_hasPullback _ _)
  exact isReduced_of_isOpenImmersion h

/-- The actual original source over a field is reduced directly from its native geometric reducedness. -/
theorem isReduced_over_field_of_geometricallyReduced
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [GeometricallyReduced f] : IsReduced X :=
  self_of_isIntegral_of_geometrically (GeometricallyReduced.geometrically_isReduced (f := f))

end Hironaka.Geometry.ProjectiveSecant
