import DeJongAlterations.Geometry.FiniteProjectiveImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite morphisms preserve actual projectivity over the original coefficient ring

The original source obtains its own native projective immersion from internally
constructed twisted algebra generators. Properness of the original composite
then makes that actual immersion closed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.FiniteProjective

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- A finite morphism over an actually projective target gives an actual closed
projective embedding of the original source, with its literal structure map. -/
theorem isProjectiveOver_comp_of_isFinite (p : X ⟶ Spec (.of R))
    (hp : IsProjectiveOver p) (f : Y ⟶ X) [IsFinite f] : IsProjectiveOver (f ≫ p) := by
  let : IsProper p := hp.isProper
  obtain ⟨n, e, he, hbase⟩ := hp
  let := he
  exact (isQuasiProjectiveOver_of_affine_to_projective (f ≫ p) (f ≫ e)).isProjective_of_isProper

end DeJongAlterations.Geometry.FiniteProjective
